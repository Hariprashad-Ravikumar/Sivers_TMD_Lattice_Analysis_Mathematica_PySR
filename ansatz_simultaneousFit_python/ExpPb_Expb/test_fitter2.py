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

def fcn(x, p):
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

file_re = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/ReA2B_PL-1_jackknife_data.h5"
file_im = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/ImA2B_PL-1_jackknife_data.h5"
file_reA12B = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/ReA12B_PL-1_jackknife_data.h5"
kin_re, jk_re = load_and_filter_data(file_re, 3, 6, 10)
kin_im, jk_im = load_and_filter_data(file_im, 3, 6, 10, True)
kin_reA12B, jk_reA12B = load_and_filter_data(file_reA12B, 3, 6, 10)

N_re = jk_re.shape[0]; N_im = jk_im.shape[0]
combined_jk = np.vstack([jk_re, jk_im, jk_reA12B])
cov_matrix = np.cov(combined_jk) # just for test

current_prior = {
    'f': gv.gvar(0.473, 0.2), 'k1_re': gv.gvar(11.60, 2.0), 'k2_re': gv.gvar(-32.4, 4.0),
    'a_re': gv.gvar(5.28, 1.0), 'c_re': gv.gvar(0.51, 0.2), 'd_re': gv.gvar(0.580, 0.2),
    'a_im': gv.gvar(0.26, 0.2), 'c_im': gv.gvar(0.3, 0.2), 'd_im': gv.gvar(0.2, 0.2),
    'a_reA12B': gv.gvar(0.6, 0.2), 'c_reA12B': gv.gvar(0.02, 0.2), 'd_reA12B': gv.gvar(0.02, 0.2)
}

x_dict = {
    'eta_re': kin_re[:, 0], 'bL_PL_re': -kin_re[:, 1], 'abs_bL_PL_re': np.abs(-kin_re[:, 1]), 'b_mag_re': np.sqrt(kin_re[:, 1]**2 + kin_re[:, 2]**2),
    'eta_im': kin_im[:, 0], 'bL_PL_im': -kin_im[:, 1], 'abs_bL_PL_im': np.abs(-kin_im[:, 1]), 'b_mag_im': np.sqrt(kin_im[:, 1]**2 + kin_im[:, 2]**2),
    'eta_reA12B': kin_reA12B[:, 0], 'bL_PL_reA12B': -kin_reA12B[:, 1], 'abs_bL_PL_reA12B': np.abs(-kin_reA12B[:, 1]), 'b_mag_reA12B': np.sqrt(kin_reA12B[:, 1]**2 + kin_reA12B[:, 2]**2)
}

y_gvar_i = gv.gvar(combined_jk[:, 0], cov_matrix)
y_dict = {'Re': y_gvar_i[:N_re], 'Im': y_gvar_i[N_re:(N_re+N_im)], 'ReA12B': y_gvar_i[(N_re+N_im):]}

fit = lsqfit.nonlinear_fit(data=(x_dict, y_dict), prior=current_prior, fcn=fcn)
print(f"Default fitter: {fit.fitter}")
print(f"Chi2/dof: {fit.chi2/fit.dof:.4f}")
