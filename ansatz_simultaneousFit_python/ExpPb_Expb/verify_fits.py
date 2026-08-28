#!/usr/bin/env python
# coding: utf-8
import h5py
import numpy as np
import gvar as gv
import lsqfit
import time
import os

os.environ["OMP_NUM_THREADS"] = "1"
os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["MKL_NUM_THREADS"] = "1"

def load_and_filter_data(filepath, bminForFit, etamin, etamax, remove_bL0=False):
    with h5py.File(filepath, "r") as f:
        raw_data = f["Dataset1"][:]
    kin = raw_data[:, 0:3]
    samples = raw_data[:, 3:]
    eta = kin[:, 0]
    bL = kin[:, 1]
    bT = kin[:, 2]
    b_mag = np.sqrt(bL**2 + bT**2)
    if remove_bL0: mask = (eta >= etamin) & (eta <= etamax) & (b_mag >= bminForFit) & (bL != 0)
    else: mask = (eta >= etamin) & (eta <= etamax) & (b_mag >= bminForFit)
    return kin[mask], samples[mask]

# === OLD SLOW MODEL ===
def old_ReA2B(eta, bL, bT, PL, a, c, k1, k2, d, f):
    return a * gv.exp(-f * eta) * gv.exp(-c * (1 - k1/eta - k2/eta**2) * np.abs(bL * PL)) * gv.exp(-d * np.sqrt(bL**2 + bT**2))

def old_ImA2B(eta, bL, bT, PL, a, c, d, f):
    return a * (bL * PL) * gv.exp(-f * eta) * gv.exp(-c * np.abs(bL * PL)) * gv.exp(-d * np.sqrt(bL**2 + bT**2))

def old_ReA12B(eta, bL, bT, PL, a, c, d, f):
    return -a * gv.exp(-f * eta) * gv.exp(-c * np.abs(bL * PL)) * gv.exp(-d * np.sqrt(bL**2 + bT**2))

def old_fcn(x, p):
    kin_re = x['Re']
    kin_im = x['Im']
    kin_reA12B = x['ReA12B']
    PL = x['PL']

    eta_re, bL_re, bT_re = kin_re[:, 0], kin_re[:, 1], kin_re[:, 2]
    eta_im, bL_im, bT_im = kin_im[:, 0], kin_im[:, 1], kin_im[:, 2]
    eta_reA12B, bL_reA12B, bT_reA12B = kin_reA12B[:, 0], kin_reA12B[:, 1], kin_reA12B[:, 2]

    f = p['f']

    val_re = old_ReA2B(eta_re, bL_re, bT_re, PL, p['a_re'], p['c_re'], p['k1_re'], p['k2_re'], p['d_re'], f)
    val_im = old_ImA2B(eta_im, bL_im, bT_im, PL, p['a_im'], p['c_im'], p['d_im'], f)
    val_reA12B = old_ReA12B(eta_reA12B, bL_reA12B, bT_reA12B, PL, p['a_reA12B'], p['c_reA12B'], p['d_reA12B'], f)

    return {'Re': val_re, 'Im': val_im, 'ReA12B': val_reA12B}

# === NEW FAST MODEL ===
def new_fcn(x, p):
    f_eta_re = p['f'] * x['eta_re']
    c_term_re = p['c_re'] * (1 - p['k1_re']/x['eta_re'] - p['k2_re']/x['eta_re']**2) * x['abs_bL_PL_re']
    d_term_re = p['d_re'] * x['b_mag_re']
    val_re = p['a_re'] * gv.exp(-(f_eta_re + c_term_re + d_term_re))
    
    f_eta_im = p['f'] * x['eta_im']
    c_term_im = p['c_im'] * x['abs_bL_PL_im']
    d_term_im = p['d_im'] * x['b_mag_im']
    val_im = p['a_im'] * x['bL_PL_im'] * gv.exp(-(f_eta_im + c_term_im + d_term_im))
    
    f_eta_reA12B = p['f'] * x['eta_reA12B']
    c_term_reA12B = p['c_reA12B'] * x['abs_bL_PL_reA12B']
    d_term_reA12B = p['d_reA12B'] * x['b_mag_reA12B']
    val_reA12B = -p['a_reA12B'] * gv.exp(-(f_eta_reA12B + c_term_reA12B + d_term_reA12B))
    
    return {'Re': val_re, 'Im': val_im, 'ReA12B': val_reA12B}

def VerifyFits(PL=-1, bminForFit=3, etamin=6, etamax=10, base_path="/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/"):
    file_re = f"{base_path}/ReA2B_PL{PL}_jackknife_data.h5"
    file_im = f"{base_path}/ImA2B_PL{PL}_jackknife_data.h5"
    file_reA12B = f"{base_path}/ReA12B_PL{PL}_jackknife_data.h5"

    kin_re, jk_re = load_and_filter_data(file_re, bminForFit, etamin, etamax)
    kin_im, jk_im = load_and_filter_data(file_im, bminForFit, etamin, etamax, remove_bL0=True)
    kin_reA12B, jk_reA12B = load_and_filter_data(file_reA12B, bminForFit, etamin, etamax)

    N_re = jk_re.shape[0]; N_im = jk_im.shape[0]

    combined_jk = np.vstack([jk_re, jk_im, jk_reA12B])
    diff = combined_jk - np.mean(combined_jk, axis=1)[:, None]
    cov_matrix = ((combined_jk.shape[1] - 1) / combined_jk.shape[1]) * (diff @ diff.T)

    current_prior = {
        'f'    : gv.gvar(0.473, 0.2),
        'k1_re': gv.gvar(11.60, 2.0),
        'k2_re': gv.gvar(-32.4, 4.0),
        'a_re' : gv.gvar(5.28, 1.0),
        'c_re' : gv.gvar(0.51, 0.2),
        'd_re' : gv.gvar(0.580, 0.2),
        'a_im' : gv.gvar(0.26, 0.2),
        'c_im' : gv.gvar(0.3, 0.2),
        'd_im' : gv.gvar(0.2, 0.2),
        'a_reA12B' : gv.gvar(0.6, 0.2),
        'c_reA12B' : gv.gvar(0.02, 0.2),
        'd_reA12B' : gv.gvar(0.02, 0.2),
    }

    # Data for ONE single jackknife sample
    y_sample_0 = combined_jk[:, 0]
    y_gvar_0 = gv.gvar(y_sample_0, cov_matrix)
    y_dict = {'Re': y_gvar_0[:N_re], 'Im': y_gvar_0[N_re:(N_re + N_im)], 'ReA12B': y_gvar_0[(N_re + N_im):]}

    # 1. RUN OLD FIT
    old_x_dict = {'Re': kin_re, 'Im': kin_im, 'ReA12B': kin_reA12B, 'PL': PL}
    t0 = time.time()
    fit_old = lsqfit.nonlinear_fit(data=(old_x_dict, y_dict), prior=current_prior, fcn=old_fcn, debug=False)
    t1 = time.time()
    old_time = t1 - t0

    # 2. RUN NEW FIT
    new_x_dict = {
        'eta_re': kin_re[:, 0], 'bL_PL_re': kin_re[:, 1] * PL, 'abs_bL_PL_re': np.abs(kin_re[:, 1] * PL), 'b_mag_re': np.sqrt(kin_re[:, 1]**2 + kin_re[:, 2]**2),
        'eta_im': kin_im[:, 0], 'bL_PL_im': kin_im[:, 1] * PL, 'abs_bL_PL_im': np.abs(kin_im[:, 1] * PL), 'b_mag_im': np.sqrt(kin_im[:, 1]**2 + kin_im[:, 2]**2),
        'eta_reA12B': kin_reA12B[:, 0], 'bL_PL_reA12B': kin_reA12B[:, 1] * PL, 'abs_bL_PL_reA12B': np.abs(kin_reA12B[:, 1] * PL), 'b_mag_reA12B': np.sqrt(kin_reA12B[:, 1]**2 + kin_reA12B[:, 2]**2)
    }
    t2 = time.time()
    fit_new = lsqfit.nonlinear_fit(data=(new_x_dict, y_dict), prior=current_prior, fcn=new_fcn, tol=(1e-8, 1e-8, 1e-8), debug=False)
    t3 = time.time()
    new_time = t3 - t2

    # PRINT COMPARISON
    print("="*60)
    print(f"{'Metric':<15} | {'Old Fit':<20} | {'New Fit':<20}")
    print("-" * 60)
    print(f"{'Time Taken':<15} | {old_time:<20.4f} | {new_time:<20.4f}")
    print(f"{'Chi2 / dof':<15} | {fit_old.chi2/fit_old.dof:<20.4f} | {fit_new.chi2/fit_new.dof:<20.4f}")
    
    print("\nFitted Parameters:")
    for k in current_prior.keys():
        old_val = fit_old.pmean[k]
        new_val = fit_new.pmean[k]
        diff = abs(old_val - new_val)
        print(f"  {k:<10} => Old: {old_val:10.7f}  |  New: {new_val:10.7f}  |  Diff: {diff:.2e}")
    print("="*60)

if __name__ == "__main__":
    VerifyFits()
