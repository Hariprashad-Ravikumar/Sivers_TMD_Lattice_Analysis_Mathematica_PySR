#!/usr/bin/env python
# coding: utf-8

import h5py
import numpy as np
import gvar as gv
import lsqfit
import math
from scipy.special import kv, gamma
import inspect
import warnings
from multiprocessing import Pool
import os

os.environ["OMP_NUM_THREADS"] = "1"
os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["MKL_NUM_THREADS"] = "1"

warnings.filterwarnings('ignore', category=RuntimeWarning)

def Jackknife(datalist): 
    N = len(datalist)
    theta_bar = np.mean(datalist)
    theta_nminus_theta_bar = []
    for i in range(N): 
        theta_n = datalist[i]
        theta_nminus_theta_bar.append(np.square(theta_n - theta_bar))
    sigma_sq = ((N-1)/N) * np.sum(theta_nminus_theta_bar)
    return theta_bar, np.sqrt(sigma_sq)

def fmt_err(mean, err):
    if err <= 0: return f"{mean}"
    if mean and (abs(mean) < 1e-3 or abs(mean) >= 1e3):
        exp = int(math.floor(math.log10(abs(mean))))
        mean_scaled = mean / 10**exp
        err_scaled = err / 10**exp
        place = int(math.floor(math.log10(abs(err_scaled))))
        ndec = max(0, -(place - 1))
        m_str = f"{mean_scaled:.{ndec}f}"
        err_int = int(round(err_scaled * 10**ndec))
        return f"{m_str}({err_int})e{exp}"
    else:
        place = int(math.floor(math.log10(abs(err))))
        ndec = max(0, -(place - 1))
        m_str = f"{mean:.{ndec}f}"
        err_int = int(round(err * 10**ndec))
        return f"{m_str}({err_int})"

def load_and_filter_data(filepath, bminForFit, etamin, etamax, remove_bL0=False):
    with h5py.File(filepath, "r") as f:
        raw_data = f["Dataset1"][:]
    kin = raw_data[:, 0:3]
    samples = raw_data[:, 3:]
    eta = kin[:, 0]
    bL = kin[:, 1]
    bT = kin[:, 2]
    b_mag = np.sqrt(bL**2 + bT**2)
    
    if remove_bL0:
        mask = (eta >= etamin) & (eta <= etamax) & (b_mag >= bminForFit) & (bL != 0)
    else:
        mask = (eta >= etamin) & (eta <= etamax) & (b_mag >= bminForFit)
    return kin[mask], samples[mask]

# === MODEL DEFINITIONS ===
def fcn(x, p):
    # ExpPb_Expb model optimized
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

# === GLOBAL WORKER SETUP ===
_global_x_dict = None
_global_y_samples = None
_global_cov_matrix = None
_global_prior = None

def init_worker(x_dict, y_samples, cov_matrix, prior):
    global _global_x_dict, _global_y_samples, _global_cov_matrix, _global_prior
    _global_x_dict = x_dict
    _global_y_samples = y_samples
    _global_cov_matrix = cov_matrix
    _global_prior = prior

def fit_worker(i):
    global _global_x_dict, _global_y_samples, _global_cov_matrix, _global_prior
    N_re = len(_global_x_dict['eta_re'])
    N_im = len(_global_x_dict['eta_im'])
    
    y_sample_i = _global_y_samples[:, i]
    y_gvar_i = gv.gvar(y_sample_i, _global_cov_matrix)
    
    y_dict = {
        'Re': y_gvar_i[:N_re],
        'Im': y_gvar_i[N_re:(N_re + N_im)],
        'ReA12B': y_gvar_i[(N_re + N_im):]
    }
    
    fit = lsqfit.nonlinear_fit(data=(_global_x_dict, y_dict), prior=_global_prior, fcn=fcn, tol=(1e-8, 1e-8, 1e-8), debug=False)
    
    res_pmean = {k: fit.pmean[k] for k in _global_prior.keys()}
    return (res_pmean, fit.chi2 / fit.dof)

def FitSimultaneousA2B(PL, bminForFit, etamin, etamax, base_path="/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/"):
    print(f"\n--- Simultaneous Fit (ExpPb_Expb) : PL={PL}, b_min>={bminForFit}, eta in [{etamin}, {etamax}] ---")
    
    file_re = f"{base_path}/ReA2B_PL{PL}_jackknife_data.h5"
    file_im = f"{base_path}/ImA2B_PL{PL}_jackknife_data.h5"
    file_reA12B = f"{base_path}/ReA12B_PL{PL}_jackknife_data.h5"

    kin_re, jk_re = load_and_filter_data(file_re, bminForFit, etamin, etamax)
    kin_im, jk_im = load_and_filter_data(file_im, bminForFit, etamin, etamax, remove_bL0=True)
    kin_reA12B, jk_reA12B = load_and_filter_data(file_reA12B, bminForFit, etamin, etamax)

    N_re = jk_re.shape[0]
    N_im = jk_im.shape[0]
    N_reA12B = jk_reA12B.shape[0]
    N_samples = jk_re.shape[1]

    print(f"Re A2B points: {N_re}, Im A2B points: {N_im}, Re A12B points: {N_reA12B}")

    combined_jk = np.vstack([jk_re, jk_im, jk_reA12B])
    mean_data = np.mean(combined_jk, axis=1)
    diff = combined_jk - mean_data[:, None]
    cov_matrix = ((N_samples - 1) / N_samples) * (diff @ diff.T)
    print(f"Covariance Matrix size: {cov_matrix.shape}")

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

    # PRECALCULATE KINEMATICS
    x_dict = {
        'eta_re': kin_re[:, 0], 'bL_PL_re': kin_re[:, 1] * PL, 'abs_bL_PL_re': np.abs(kin_re[:, 1] * PL), 'b_mag_re': np.sqrt(kin_re[:, 1]**2 + kin_re[:, 2]**2),
        'eta_im': kin_im[:, 0], 'bL_PL_im': kin_im[:, 1] * PL, 'abs_bL_PL_im': np.abs(kin_im[:, 1] * PL), 'b_mag_im': np.sqrt(kin_im[:, 1]**2 + kin_im[:, 2]**2),
        'eta_reA12B': kin_reA12B[:, 0], 'bL_PL_reA12B': kin_reA12B[:, 1] * PL, 'abs_bL_PL_reA12B': np.abs(kin_reA12B[:, 1] * PL), 'b_mag_reA12B': np.sqrt(kin_reA12B[:, 1]**2 + kin_reA12B[:, 2]**2)
    }

    print("Starting multiprocessing fit...")
    param_names = list(current_prior.keys())
    fitted_params = {key: [] for key in param_names}
    chi2_dof_list = []

    num_cores = 4
    with Pool(num_cores, initializer=init_worker, initargs=(x_dict, combined_jk, cov_matrix, current_prior), maxtasksperchild=50) as pool:
        results = pool.map(fit_worker, range(N_samples))
        
    for res_pmean, chi2_dof in results:
        for key in param_names:
            fitted_params[key].append(res_pmean[key])
        chi2_dof_list.append(chi2_dof)

    print("\n--- Final Extracted Parameters ---")
    for key in param_names:
        mean_val, err_val = Jackknife(fitted_params[key])
        print(f"{key:>10} = {fmt_err(mean_val, err_val)}")

    mean_chi2, err_chi2 = Jackknife(chi2_dof_list)
    print(f"\n chi^2/dof : {fmt_err(mean_chi2, err_chi2)}\n")

    return fitted_params, chi2_dof_list

def save_params_to_h5(fitted_params, chi2_dof_list, filename):
    print(f"\nSaving results to {filename}...")
    os.makedirs(os.path.dirname(filename), exist_ok=True)
    with h5py.File(filename, "w") as f:
        param_group = f.create_group("jackknife_samples")
        for key, value_list in fitted_params.items():
            param_group.create_dataset(key, data=np.array(value_list))
        f.create_dataset("chi2_dof", data=np.array(chi2_dof_list))
    print("Save complete!")

if __name__ == "__main__":
    bmin = 3
    etaminvalue = 6
    etamaxvalue = 10
    
    base_save_dir = "/pscratch/sd/h/hari_8/TMD_fit/h5data/"
    if not os.path.exists("/pscratch"):
        base_save_dir = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/h5data/"

    ansatz_name = "ExpPb_Expb"

    for PL_val in [-1, -2, -3, -4]:
        results, chi2_list = FitSimultaneousA2B(PL=PL_val, bminForFit=bmin, etamin=etaminvalue, etamax=etamaxvalue)
        save_path = f"{base_save_dir}/FitParams_SimulFit_{ansatz_name}_bmin{bmin}_eta{etaminvalue}{etamaxvalue}_PL{PL_val}.h5"
        save_params_to_h5(results, chi2_list, save_path)
