#!/usr/bin/env python
# coding: utf-8

# In[1]:


import h5py
import numpy as np
import gvar as gv
import lsqfit
from tqdm.auto import tqdm
import matplotlib.pyplot as plt
import math
from scipy.special import kv, gamma
import inspect
import warnings
warnings.filterwarnings('ignore', category=RuntimeWarning)

# ---------------------------------------------------------
# 1. Jackknife Statistics Helper
# ---------------------------------------------------------
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
    # Fallback for 0 or negative error
    if err <= 0:
        return f"{mean}"

    # Switch to scientific if very small/big
    if mean and (abs(mean) < 1e-3 or abs(mean) >= 1e3):
        # Calculate exponent of the mean
        exp = int(math.floor(math.log10(abs(mean))))
        mean_scaled = mean / 10**exp
        err_scaled = err / 10**exp

        # Find precision needed for exactly 2 significant digits of the error
        place = int(math.floor(math.log10(abs(err_scaled))))
        ndec = max(0, -(place - 1))

        m_str = f"{mean_scaled:.{ndec}f}"
        err_int = int(round(err_scaled * 10**ndec))
        return f"{m_str}({err_int})e{exp}"

    else:
        # Find precision needed for exactly 2 significant digits of the error
        place = int(math.floor(math.log10(abs(err))))
        ndec = max(0, -(place - 1))  # -1 gives us 2 sig figs instead of 1

        m_str = f"{mean:.{ndec}f}"
        err_int = int(round(err * 10**ndec))
        return f"{m_str}({err_int})"

'''
def fmt_err(mean, err):
    # switch to scientific if very small/big
    if mean and (abs(mean) < 1e-3 or abs(mean) >= 1e3):
        m_str = f"{mean:.2e}"           # e.g. "2.86e-08"
        mant, exp = m_str.split("e")
        ndec = len(mant.split(".")[1])  # digits in mantissa
        err_int = int(round(err / 10**int(exp) * 10**ndec))
        return f"{mant}({err_int})e{int(exp)}"
    else:
        ndec = 4                        # choose 4 decimal places
        m_str = f"{mean:.{ndec}f}"      # e.g. "0.4721"
        err_int = int(round(err * 10**ndec))
        return f"{m_str}({err_int:0{ndec}d})"
'''

# ---------------------------------------------------------
# 2. Data Loading & Filtering Helper
# ---------------------------------------------------------
def load_and_filter_data(filepath, bminForFit, etamin, etamax):
    """Loads HDF5 data and applies kinematic cuts."""
    with h5py.File(filepath, "r") as f:
        raw_data = f["Dataset1"][:]

    kin = raw_data[:, 0:3]
    samples = raw_data[:, 3:]

    eta = kin[:, 0]
    bL  = kin[:, 1]
    bT  = kin[:, 2]

    # Calculate b = sqrt(bL^2 + bT^2)
    b_mag = np.sqrt(bL**2 + bT**2)

    # Create a boolean mask for our cuts
    mask = (eta >= etamin) & (eta <= etamax) & (b_mag >= bminForFit)

    # Return only the rows that passed the cuts
    return kin[mask], samples[mask]


def load_and_filter_data_rm_0_bL(filepath, bminForFit, etamin, etamax):
    """Loads HDF5 data and applies kinematic cuts."""
    with h5py.File(filepath, "r") as f:
        raw_data = f["Dataset1"][:]

    kin = raw_data[:, 0:3]
    samples = raw_data[:, 3:]

    eta = kin[:, 0]
    bL  = kin[:, 1]
    bT  = kin[:, 2]

    # Calculate b = sqrt(bL^2 + bT^2)
    b_mag = np.sqrt(bL**2 + bT**2)

    # Create a boolean mask for our cuts
    mask = (eta >= etamin) & (eta <= etamax) & (b_mag >= bminForFit) & (bL != 0)

    # Return only the rows that passed the cuts
    return kin[mask], samples[mask]


def ReA2B(eta, bL, bT, a, c, d, f, k1, k2, j):
    denom = (1 + (d + c * (1 - k1/eta - k2/eta**2)) * bL**2 + d * bT**2)**j
    return a * gv.exp(-f * eta) / denom

def ImA2B(eta, bL, bT, a, c, d, f, j):
    denom = (1 + (d + c) * bL**2 + d * bT**2)**j
    return a * bL * gv.exp(-f * eta) / denom

def ReA12B(eta, bL, bT, a, c, d, f, j):
    denom = (1 + (d + c) * bL**2 + d * bT**2)**j
    return -a * gv.exp(-f * eta) / denom


def fcn(x, p):
    # 1. Unpack the kinematic arrays from the dictionary x
    kin_re = x['Re']
    kin_im = x['Im']
    kin_reA12B = x['ReA12B']

    eta_re, bL_re, bT_re = kin_re[:, 0], kin_re[:, 1], kin_re[:, 2]
    eta_im, bL_im, bT_im = kin_im[:, 0], kin_im[:, 1], kin_im[:, 2]
    eta_reA12B, bL_reA12B, bT_reA12B = kin_reA12B[:, 0], kin_reA12B[:, 1], kin_reA12B[:, 2]

    # Shared parameter
    f = p['f']

    # Real-specific parameters
    val_re = ReA2B(eta_re, bL_re, bT_re, p['a_re'], p['c_re'], p['d_re'], f, p['k1_re'], p['k2_re'], p['j_re'])

    # Imaginary-specific parameters
    val_im = ImA2B(eta_im, bL_im, bT_im, p['a_im'], p['c_im'], p['d_im'], f, p['j_im'])

    val_reA12B = ReA12B(eta_reA12B, bL_reA12B, bT_reA12B, p['a_reA12B'], p['c_reA12B'], p['d_reA12B'], f, p['j_reA12B'])

    return {'Re': val_re, 'Im': val_im, 'ReA12B': val_reA12B}

# ---------------------------------------------------------
# 3. Main Simultaneous Fitting Function
# ---------------------------------------------------------
def FitSimultaneousA2B(PL, bminForFit, etamin, etamax):
    print(f"Simultaneous Fit (ReA2B & ImA2B) : PL={PL}, b_min>={bminForFit}, eta in [{etamin}, {etamax}] ---")
    print("\n--- Fit Functions ---")
    print(inspect.getsource(ReA2B))
    print(inspect.getsource(ImA2B))
    print(inspect.getsource(ReA12B))
    print("---------------------\n")

    # 1. Construct file paths (Update the base path if needed)
    base_path = "/pscratch/sd/h/hari_8/TMD_fit/h5data/"
    file_re = f"{base_path}/ReA2B_PL{PL}_jackknife_data.h5"
    file_im = f"{base_path}/ImA2B_PL{PL}_jackknife_data.h5"
    file_reA12B = f"{base_path}/ReA12B_PL{PL}_jackknife_data.h5"

    # 2. Load and Filter Data
    kin_re, jk_re = load_and_filter_data(file_re, bminForFit, etamin, etamax)
    kin_im, jk_im = load_and_filter_data_rm_0_bL(file_im, bminForFit, etamin, etamax)
    kin_reA12B, jk_reA12B = load_and_filter_data(file_reA12B, bminForFit, etamin, etamax)

    N_re = jk_re.shape[0]
    N_im = jk_im.shape[0]
    N_reA12B = jk_reA12B.shape[0]
    N_samples = jk_re.shape[1]

    print(f"Re A2B points: {N_re}, Im A2B points: {N_im}, Re A12B points: {N_reA12B}")

    # 3. Calculate the Full Jackknife Covariance Matrix
    combined_jk = np.vstack([jk_re, jk_im, jk_reA12B])
    mean_data = np.mean(combined_jk, axis=1)
    diff = combined_jk - mean_data[:, None]
    cov_matrix = ((N_samples - 1) / N_samples) * (diff @ diff.T)
    print(f"Covariance Matrix size: {cov_matrix.shape}")


    # ---------------------------------------------------------
    # Set up Priors
    current_prior = {
        # Shared Parameters (Anchored by Real Part)
        'f'    : gv.gvar(0.5, 0.05),   # Centered on your last successful fit
        #'d' : gv.gvar(0.10, 0.05),
        #'j'    : gv.gvar(2, 0.5),
        # Real-specific (Stable, moderate priors)   
        'k1_re': gv.gvar(12.27, 0.05),
        'k2_re': gv.gvar(-36.2,0.05),
        'a_re' : gv.gvar(4.01, 0.05),
        'c_re' : gv.gvar(0.146, 0.05),
        'd_re' : gv.gvar(0.094, 0.05),  # Shared: forces consistent broadening
        'j_re' : gv.gvar(2.06,0.05),     # Shared: forces consistent large-b decay
    # Imaginary-specific (Tighter priors to prevent wandering)
        #'k1_im': gv.gvar(-5.5, 2.0),   # MUCH tighter than 50.0
        'a_im' : gv.gvar(0.26,  0.05),  # Magnitude of the T-odd signal
        'c_im' : gv.gvar(0.3,  0.05),
        'd_im' : gv.gvar(0.2, 0.05), 
        'j_im'    : gv.gvar(1, 0.05),   # Shared: forces consistent large-b decay
        'a_reA12B' : gv.gvar(0.6,  0.05), 
        'c_reA12B' : gv.gvar(0.02,  0.05),
        'd_reA12B' : gv.gvar(0.02, 0.05), 
        'j_reA12B'    : gv.gvar(2, 0.05),
    }


    x_dict = {'Re': kin_re, 'Im': kin_im, 'ReA12B': kin_reA12B}
    param_names = ['k1_re','k2_re','f','a_re','c_re','d_re','j_re','a_im','c_im','d_im','j_im', 'a_reA12B', 'c_reA12B', 'd_reA12B', 'j_reA12B']
    fitted_params = {key: [] for key in param_names}

    # We will also track chi-square per degree of freedom
    chi2_dof_list = []

    for i in tqdm(range(N_samples)):
        y_sample_i = combined_jk[:, i]
        y_gvar_i = gv.gvar(y_sample_i, cov_matrix)

        y_dict = {
            'Re': y_gvar_i[:N_re],
            'Im': y_gvar_i[N_re:(N_re + N_im)],
            'ReA12B': y_gvar_i[(N_re + N_im):]
        }

        fit = lsqfit.nonlinear_fit(data=(x_dict, y_dict), prior=current_prior, fcn=fcn, debug=False)

        for key in fitted_params:
            fitted_params[key].append(fit.pmean[key])

        chi2_dof_list.append(fit.chi2 / fit.dof)
        #dof = (N_re + N_im) - len(param_names)
        #chi2_dof_list.append(fit.chi2 / dof)

    # 7. Apply Jackknife and Print Results
    print("\n--- Final Extracted Parameters ---")
    for key in fitted_params:
        mean_val, err_val = Jackknife(fitted_params[key])
        print(f"{key:>5} = {fmt_err(mean_val, err_val)}")

    mean_chi2, err_chi2 = Jackknife(chi2_dof_list)
    print(f"\n chi^2/dof : {fmt_err(mean_chi2, err_chi2)}\n")

    # Return the dictionary of jackknifed parameter arrays in case you want to plot them later
    return fitted_params


# ---------------------------------------------------------
# Plotting Function
# ---------------------------------------------------------
def plot_fourier_transforms_A2B_A12B(fitted_params, b2, PL, num_points=200):
    # 1. Setup x-axis (avoid exactly 0 to prevent division by zero in Bessel/powers)
    x_vals = np.linspace(-1, 1, num_points)
    MassN = 0.6228
    lata = 0.11403
    massterm = MassN*(197*0.001/lata)

    # 2. Extract parameters as NumPy arrays
    a_re = np.array(fitted_params['a_re'])
    c_re = np.array(fitted_params['c_re']) / (PL**2)
    d_re = 1.0 + np.array(fitted_params['d_re']) * b2  
    j_re = np.array(fitted_params['j_re'])

    a_im = np.array(fitted_params['a_im']) / PL
    c_im = np.array(fitted_params['c_im']) / (PL**2)
    d_im = 1.0 + np.array(fitted_params['d_im']) * b2
    j_im = np.array(fitted_params['j_im'])

    a_reA12B = -np.array(fitted_params['a_reA12B'])
    c_reA12B = np.array(fitted_params['c_reA12B']) / (PL**2)
    d_reA12B = 1.0 + np.array(fitted_params['d_reA12B']) * b2  
    j_reA12B = np.array(fitted_params['j_reA12B'])

    # Prepare lists to store the jackknife results for plotting
    re_mean, re_err = [], []
    reA12B_mean, reA12B_err = [], []
    im_mean, im_err = [], []
    full_mean, full_err = [], []
    SiverseShift_mean, SiverseShift_err = [], []
    xSiverseShift_mean, xSiverseShift_err = [], []

    print("Evaluating Fourier transforms and applying Jackknife...")

    # 3. Loop over each x value and apply your Jackknife function
    for x in x_vals:
        abs_x = np.abs(x)

        # --- Evaluate Real Part for all ~2900 samples at this x ---
        cd_R = c_re / d_re
        term1_R = (2**(1 - j_re) * a_re * cd_R**(-0.25 - j_re/2) * d_re**(-j_re)) / gamma(j_re)
        term2_R = abs_x**(-0.5 + j_re)
        bessel_R = kv(0.5 - j_re, abs_x / np.sqrt(cd_R))

        re_evals_at_x = term1_R * term2_R * bessel_R

        # Apply your Jackknife function
        m_re, e_re = Jackknife(re_evals_at_x)
        re_mean.append(m_re)
        re_err.append(e_re)

        # --- Evaluate Imaginary Part for all ~2900 samples at this x ---
        cd_I = c_im / d_im
        term1_I = (2**(1 - j_im) * a_im * cd_I**(0.25 * (-3 - 2*j_im)) * d_im**(-j_im)) / gamma(j_im)
        term2_I = x * abs_x**(-1.5 + j_im)
        bessel_I = kv(1.5 - j_im, np.sqrt(d_im / c_im) * abs_x)

        im_evals_at_x = term1_I * term2_I * bessel_I

        # Apply your Jackknife function
        m_im, e_im = Jackknife(im_evals_at_x)
        im_mean.append(m_im)
        im_err.append(e_im)

        m_full, e_full = Jackknife(2*(re_evals_at_x-im_evals_at_x))
        full_mean.append(m_full)
        full_err.append(e_full)

        ####################
        cd_RA12B = c_reA12B / d_reA12B
        term1_RA12B = (2**(1 - j_reA12B) * a_reA12B * cd_RA12B**(-0.25 - j_reA12B/2) * d_reA12B**(-j_reA12B)) / gamma(j_reA12B)
        term2_RA12B = abs_x**(-0.5 + j_reA12B)
        bessel_RA12B = kv(0.5 - j_reA12B, abs_x / np.sqrt(cd_RA12B))

        reA12B_evals_at_x = term1_RA12B * term2_RA12B * bessel_RA12B

        # Apply your Jackknife function
        m_reA12B, e_reA12B = Jackknife(-2*reA12B_evals_at_x)
        reA12B_mean.append(m_reA12B)
        reA12B_err.append(e_reA12B)

        m_SiverseShift, e_SiverseShift = Jackknife((-massterm*reA12B_evals_at_x)/(re_evals_at_x-im_evals_at_x))
        SiverseShift_mean.append(m_SiverseShift)
        SiverseShift_err.append(e_SiverseShift)


        m_xSiverseShift, e_xSiverseShift = Jackknife(x*(-massterm*reA12B_evals_at_x)/(re_evals_at_x-im_evals_at_x))
        xSiverseShift_mean.append(m_xSiverseShift)
        xSiverseShift_err.append(e_xSiverseShift)

    # Convert results to arrays for easier plotting
    re_mean, re_err = np.array(re_mean), np.array(re_err)
    im_mean, im_err = np.array(im_mean), np.array(im_err)
    full_mean, full_err = np.array(full_mean), np.array(full_err)
    reA12B_mean, reA12B_err = np.array(reA12B_mean), np.array(reA12B_err)
    SiverseShift_mean, SiverseShift_err = np.array(SiverseShift_mean), np.array(SiverseShift_err)
    xSiverseShift_mean, xSiverseShift_err = np.array(xSiverseShift_mean), np.array(xSiverseShift_err)

    # 4. Plotting
    #fig, (ax1, ax2, ax3) = plt.subplots(1, 3, figsize=(14, 5))
    fig, ((ax1, ax2, ax3), (ax4, ax5, ax6)) = plt.subplots(2, 3, figsize=(14, 8))

    # Real Plot
    ax1.plot(x_vals, re_mean, color='blue', label='ReA2B Mean')
    ax1.fill_between(x_vals, re_mean - re_err, re_mean + re_err, color='blue', alpha=0.3, label='Jackknife Error Band')
    ax1.set_title(f'$\\tilde{{A}}_{{2B}}^{{Re}}$ ($P_L$={PL}, $b^2$={b2})')
    ax1.set_xlabel('$x$')
    ax1.set_ylabel('$\\tilde{{A}}_{{2B}}^{{Re}}$')
    #ax1.legend()
    ax1.grid(True, linestyle='--', alpha=0.6)

    # Imaginary Plot
    ax2.plot(x_vals, im_mean, color='red', label='ImA2B Mean')
    ax2.fill_between(x_vals, im_mean - im_err, im_mean + im_err, color='red', alpha=0.3, label='Jackknife Error Band')
    ax2.set_title(f'$i\\tilde{{A}}_{{2B}}^{{Im}}$ ($P_L$={PL}, $b^2$={b2})')
    ax2.set_xlabel('$x$')
    ax2.set_ylabel('$i\\tilde{{A}}_{{2B}}^{{Im}}$')
    #ax2.legend()
    ax2.grid(True, linestyle='--', alpha=0.6)


    ax3.plot(x_vals, full_mean, color='green', label='A2B Mean')
    ax3.fill_between(x_vals, full_mean - full_err, full_mean + full_err, color='green', alpha=0.3, label='Jackknife Error Band')
    ax3.set_title(f'$\\tilde{{f}}_{{1}}^{{(0)}}=2\\tilde{{A}}_{{2B}}$ ($P_L$={PL}, $b^2$={b2}) = $\\tilde{{A}}_{{2B}}^{{Re}}+i(i\\tilde{{A}}_{{2B}}^{{Im}})$')
    ax3.set_xlabel('$x$')
    ax3.set_ylabel('$\\tilde{{f}}_{{1}}^{{(0)}}$')
    #ax3.legend()
    ax3.grid(True, linestyle='--', alpha=0.6)

    ax4.plot(x_vals, reA12B_mean, color='blue')
    ax4.fill_between(x_vals, reA12B_mean - reA12B_err, reA12B_mean + reA12B_err, color='blue', alpha=0.3)
    ax4.set_title(f'$\\tilde{{f}}_{{1}}^{{\\perp(1)}}=-2\\tilde{{A}}_{{12B}}$ ($P_L$={PL}, $b^2$={b2})')
    ax4.set_xlabel('$x$')
    ax4.set_ylabel('$\\tilde{{f}}_{{1}}^{{\\perp(1)}}$')
    ax4.grid(True, linestyle='--', alpha=0.6)
    # Create mask for x values from 0 to 1
    mask = x_vals >= 0

    # Sivers Shift Plot (0 to 1)
    ax5.plot(x_vals[mask], SiverseShift_mean[mask], color='blue')
    ax5.fill_between(x_vals[mask], SiverseShift_mean[mask] - SiverseShift_err[mask], 
                     SiverseShift_mean[mask] + SiverseShift_err[mask], color='blue', alpha=0.3)
    ax5.set_title(f'$\\langle k_{{y}} \\rangle_{{TU}}$(GeV) ($P_L$={PL}, $b^2$={b2})')
    ax5.set_xlabel('$x$')
    ax5.set_ylabel('$\\langle k_{{y}} \\rangle_{{TU}}$(GeV)')
    ax5.grid(True, linestyle='--', alpha=0.6)

    # x*Sivers Shift Plot (0 to 1)
    ax6.plot(x_vals[mask], xSiverseShift_mean[mask], color='blue')
    ax6.fill_between(x_vals[mask], xSiverseShift_mean[mask] - xSiverseShift_err[mask], 
                     xSiverseShift_mean[mask] + xSiverseShift_err[mask], color='blue', alpha=0.3)
    ax6.set_title(f'$x\\langle k_{{y}} \\rangle_{{TU}}$(GeV) ($P_L$={PL}, $b^2$={b2})')
    ax6.set_xlabel('$x$')
    ax6.set_ylabel('$x\\langle k_{{y}} \\rangle_{{TU}}$(GeV)')
    ax6.grid(True, linestyle='--', alpha=0.6)

    plt.tight_layout()
    param_keys_str = "-".join(fitted_params.keys())
    file_name = f"SimulFitCovMatrix-A2B-FT-{param_keys_str}.pdf"
    plt.savefig(file_name, format='pdf', bbox_inches='tight')
    plt.show()

    return fig, (ax1, ax2, ax3, ax4, ax5, ax6)


# In[2]:


results_1 = FitSimultaneousA2B(PL=-1, bminForFit=3, etamin=6, etamax=10)


# In[10]:


fig1, axes1 = plot_fourier_transforms_A2B_A12B(results_1, b2=9, PL=-1)


# In[2]:


results_1 = FitSimultaneousA2B(PL=-2, bminForFit=3, etamin=6, etamax=10)
fig1, axes1 = plot_fourier_transforms_A2B_A12B(results_1, b2=9, PL=-2)


# In[3]:


import h5py
import numpy as np
import gvar as gv
import math
import lsqfit
from tqdm.auto import tqdm
import matplotlib.pyplot as plt
from scipy.special import kv, gamma
import inspect
import warnings
warnings.filterwarnings('ignore', category=RuntimeWarning)

# ---------------------------------------------------------
# 1. Jackknife Statistics Helper
# ---------------------------------------------------------
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
    # Fallback for 0 or negative error
    if err <= 0:
        return f"{mean}"

    # Switch to scientific if very small/big
    if mean and (abs(mean) < 1e-3 or abs(mean) >= 1e3):
        # Calculate exponent of the mean
        exp = int(math.floor(math.log10(abs(mean))))
        mean_scaled = mean / 10**exp
        err_scaled = err / 10**exp

        # Find precision needed for exactly 2 significant digits of the error
        place = int(math.floor(math.log10(abs(err_scaled))))
        ndec = max(0, -(place - 1))

        m_str = f"{mean_scaled:.{ndec}f}"
        err_int = int(round(err_scaled * 10**ndec))
        return f"{m_str}({err_int})e{exp}"

    else:
        # Find precision needed for exactly 2 significant digits of the error
        place = int(math.floor(math.log10(abs(err))))
        ndec = max(0, -(place - 1))  # -1 gives us 2 sig figs instead of 1

        m_str = f"{mean:.{ndec}f}"
        err_int = int(round(err * 10**ndec))
        return f"{m_str}({err_int})"

# ---------------------------------------------------------
# 2. Data Loading & Filtering Helper
# ---------------------------------------------------------
def load_and_filter_data(filepath, bminForFit, etamin, etamax):
    """Loads HDF5 data and applies kinematic cuts."""
    with h5py.File(filepath, "r") as f:
        raw_data = f["Dataset1"][:]

    kin = raw_data[:, 0:3]
    samples = raw_data[:, 3:]

    eta = kin[:, 0]
    bL  = kin[:, 1]
    bT  = kin[:, 2]

    # Calculate b = sqrt(bL^2 + bT^2)
    b_mag = np.sqrt(bL**2 + bT**2)

    # Create a boolean mask for our cuts
    mask = (eta >= etamin) & (eta <= etamax) & (b_mag >= bminForFit)

    # Return only the rows that passed the cuts
    return kin[mask], samples[mask]


def load_and_filter_data_rm_0_bL(filepath, bminForFit, etamin, etamax):
    """Loads HDF5 data and applies kinematic cuts."""
    with h5py.File(filepath, "r") as f:
        raw_data = f["Dataset1"][:]

    kin = raw_data[:, 0:3]
    samples = raw_data[:, 3:]

    eta = kin[:, 0]
    bL  = kin[:, 1]
    bT  = kin[:, 2]

    # Calculate b = sqrt(bL^2 + bT^2)
    b_mag = np.sqrt(bL**2 + bT**2)

    # Create a boolean mask for our cuts
    mask = (eta >= etamin) & (eta <= etamax) & (b_mag >= bminForFit) & (bL != 0)

    # Return only the rows that passed the cuts
    return kin[mask], samples[mask]


def ReA2B(eta, bL, bT, a, c, d, f, k1, k2, j):
    denom = (1 + (d + c * (1 - k1/eta - k2/eta**2)) * bL**2 + d * bT**2)**j
    return a * gv.exp(-f * eta) / denom

def ImA2B(eta, bL, bT, a, c, d, f, j):
    denom = (1 + (d + c) * bL**2 + d * bT**2)**j
    return a * bL * gv.exp(-f * eta) / denom

def ReA12B(eta, bL, bT, a, c, d, f, j):
    denom = (1 + (d + c) * bL**2 + d * bT**2)**j
    return -a * gv.exp(-f * eta) / denom


def fcn(x, p):
    # 1. Unpack the kinematic arrays from the dictionary x
    kin_re = x['Re']
    kin_im = x['Im']
    kin_reA12B = x['ReA12B']

    eta_re, bL_re, bT_re = kin_re[:, 0], kin_re[:, 1], kin_re[:, 2]
    eta_im, bL_im, bT_im = kin_im[:, 0], kin_im[:, 1], kin_im[:, 2]
    eta_reA12B, bL_reA12B, bT_reA12B = kin_reA12B[:, 0], kin_reA12B[:, 1], kin_reA12B[:, 2]

    # Shared parameter
    f = p['f']

    # --- ENFORCE c > d FOR ALL THREE TARGETS ---
    # np.exp() is strictly > 0, so c will always be strictly > d
    c_re_eff = p['d_re'] + np.exp(p['log_delta_c_re'])
    c_im_eff = p['d_im'] + np.exp(p['log_delta_c_im'])
    c_reA12B_eff = p['d_reA12B'] + np.exp(p['log_delta_c_reA12B'])

    # Real-specific parameters
    val_re = ReA2B(eta_re, bL_re, bT_re, p['a_re'], c_re_eff, p['d_re'], f, p['k1_re'], p['k2_re'], p['j_re'])

    # Imaginary-specific parameters
    val_im = ImA2B(eta_im, bL_im, bT_im, p['a_im'], c_im_eff, p['d_im'], f, p['j_im'])

    # ReA12B-specific parameters
    val_reA12B = ReA12B(eta_reA12B, bL_reA12B, bT_reA12B, p['a_reA12B'], c_reA12B_eff, p['d_reA12B'], f, p['j_reA12B'])

    return {'Re': val_re, 'Im': val_im, 'ReA12B': val_reA12B}

# ---------------------------------------------------------
# 3. Main Simultaneous Fitting Function
# ---------------------------------------------------------
def FitSimultaneousA2B(PL, bminForFit, etamin, etamax):
    print(f"Simultaneous Fit (ReA2B, ImA2B, & ReA12B) : PL={PL}, b_min>={bminForFit}, eta in [{etamin}, {etamax}] ---")
    print("\n--- Fit Functions ---")
    print(inspect.getsource(ReA2B))
    print(inspect.getsource(ImA2B))
    print(inspect.getsource(ReA12B))
    print("---------------------\n")

    # 1. Construct file paths (Update the base path if needed)
    base_path = "/pscratch/sd/h/hari_8/TMD_fit/h5data/"
    file_re = f"{base_path}/ReA2B_PL{PL}_jackknife_data.h5"
    file_im = f"{base_path}/ImA2B_PL{PL}_jackknife_data.h5"
    file_reA12B = f"{base_path}/ReA12B_PL{PL}_jackknife_data.h5"

    # 2. Load and Filter Data
    kin_re, jk_re = load_and_filter_data(file_re, bminForFit, etamin, etamax)
    kin_im, jk_im = load_and_filter_data_rm_0_bL(file_im, bminForFit, etamin, etamax)
    kin_reA12B, jk_reA12B = load_and_filter_data(file_reA12B, bminForFit, etamin, etamax)

    N_re = jk_re.shape[0]
    N_im = jk_im.shape[0]
    N_reA12B = jk_reA12B.shape[0]
    N_samples = jk_re.shape[1]

    print(f"Re A2B points: {N_re}, Im A2B points: {N_im}, Re A12B points: {N_reA12B}")

    # 3. Calculate the Full Jackknife Covariance Matrix
    combined_jk = np.vstack([jk_re, jk_im, jk_reA12B])
    mean_data = np.mean(combined_jk, axis=1)
    diff = combined_jk - mean_data[:, None]
    cov_matrix = ((N_samples - 1) / N_samples) * (diff @ diff.T)
    print(f"Covariance Matrix size: {cov_matrix.shape}")

    # ---------------------------------------------------------
    # Set up Priors
    # The initial guesses for log_delta are calculated as ln(c_prior - d_prior)
    # Re: ln(0.146 - 0.094) = ln(0.052) ~ -2.95
    # Im: ln(0.3 - 0.2) = ln(0.1) ~ -2.30
    # ReA12B: The previous prior had c=0.02 and d=0.02. ln(0) is undefined.
    # We will use -4.0, which assumes an initial difference of e^(-4) ≈ 0.018
    current_prior = {
        # Shared Parameters
        'f'    : gv.gvar(0.5, 0.05),   

        # Real-specific 
        'k1_re': gv.gvar(12.27, 0.05),
        'k2_re': gv.gvar(-36.2, 0.05),
        'a_re' : gv.gvar(4.01, 0.05),
        'd_re' : gv.gvar(0.094, 0.05), 
        'log_delta_c_re': gv.gvar(-2.95, 2.0),
        'j_re' : gv.gvar(2.06, 0.05),  

        # Imaginary-specific 
        'a_im' : gv.gvar(0.26, 0.05),  
        'd_im' : gv.gvar(0.2, 0.05), 
        'log_delta_c_im': gv.gvar(-2.30, 2.0),
        'j_im' : gv.gvar(1, 0.05),   

        # ReA12B-specific 
        'a_reA12B' : gv.gvar(0.6, 0.05), 
        'd_reA12B' : gv.gvar(0.02, 0.05), 
        'log_delta_c_reA12B': gv.gvar(-4.0, 2.0),
        'j_reA12B' : gv.gvar(2, 0.05),
    }

    x_dict = {'Re': kin_re, 'Im': kin_im, 'ReA12B': kin_reA12B}

    # The parameters lsqfit actually sees and optimizes
    fit_param_names = [
        'k1_re', 'k2_re', 'f', 'a_re', 'log_delta_c_re', 'd_re', 'j_re',
        'a_im', 'log_delta_c_im', 'd_im', 'j_im', 
        'a_reA12B', 'log_delta_c_reA12B', 'd_reA12B', 'j_reA12B'
    ]

    # The physical parameters we want to print out at the end
    track_param_names = [
        'k1_re', 'k2_re', 'f', 'a_re', 'c_re', 'd_re', 'j_re',
        'a_im', 'c_im', 'd_im', 'j_im', 
        'a_reA12B', 'c_reA12B', 'd_reA12B', 'j_reA12B'
    ]
    fitted_params = {key: [] for key in track_param_names}

    chi2_dof_list = []

    for i in tqdm(range(N_samples)):
        y_sample_i = combined_jk[:, i]
        y_gvar_i = gv.gvar(y_sample_i, cov_matrix)

        y_dict = {
            'Re': y_gvar_i[:N_re],
            'Im': y_gvar_i[N_re:(N_re + N_im)],
            'ReA12B': y_gvar_i[(N_re + N_im):]
        }

        fit = lsqfit.nonlinear_fit(data=(x_dict, y_dict), prior=current_prior, fcn=fcn, debug=False)

        # 1. Extract the standard unchanged parameters directly from the fit
        for key in ['k1_re','k2_re','f','a_re','d_re','j_re','a_im','d_im','j_im','a_reA12B','d_reA12B','j_reA12B']:
            fitted_params[key].append(fit.pmean[key])

        # 2. Reconstruct the physical 'c' values for all three data types
        actual_c_re = fit.pmean['d_re'] + np.exp(fit.pmean['log_delta_c_re'])
        actual_c_im = fit.pmean['d_im'] + np.exp(fit.pmean['log_delta_c_im'])
        actual_c_reA12B = fit.pmean['d_reA12B'] + np.exp(fit.pmean['log_delta_c_reA12B'])

        fitted_params['c_re'].append(actual_c_re)
        fitted_params['c_im'].append(actual_c_im)
        fitted_params['c_reA12B'].append(actual_c_reA12B)

        chi2_dof_list.append(fit.chi2 / fit.dof)

    # 7. Apply Jackknife and Print Results
    print("\n--- Final Extracted Parameters ---")
    for key in track_param_names:
        mean_val, err_val = Jackknife(fitted_params[key])
        print(f"{key:>10} = {fmt_err(mean_val, err_val)}")

    mean_chi2, err_chi2 = Jackknife(chi2_dof_list)
    print(f"\n chi^2/dof : {fmt_err(mean_chi2, err_chi2)}\n")

    return fitted_params, chi2_dof_list


def save_params_to_h5(fitted_params, chi2_dof_list, filename):
    """
    Saves the dictionary of jackknifed parameter arrays AND the chi2 array to an HDF5 file.
    """
    print(f"\nSaving results to {filename}...")
    with h5py.File(filename, "w") as f:
        # 1. Save the physical parameters inside a group
        param_group = f.create_group("jackknife_samples")
        for key, value_list in fitted_params.items():
            param_group.create_dataset(key, data=np.array(value_list))

        # 2. Save the chi-square array at the root level of the file
        f.create_dataset("chi2_dof", data=np.array(chi2_dof_list))

    print("Save complete!")


# ---------------------------------------------------------
# Plotting Function
# ---------------------------------------------------------
def plot_fourier_transforms_A2B_A12B(fitted_params, b2, PL, num_points=200):
    # 1. Setup x-axis (avoid exactly 0 to prevent division by zero in Bessel/powers)
    x_vals = np.linspace(-1, 1, num_points)
    MassN = 0.6228
    lata = 0.11403
    massterm = MassN*(197*0.001/lata)

    # 2. Extract parameters as NumPy arrays
    a_re = np.array(fitted_params['a_re'])
    c_re = np.array(fitted_params['c_re']) / (PL**2)
    d_re = 1.0 + np.array(fitted_params['d_re']) * b2  
    j_re = np.array(fitted_params['j_re'])

    a_im = np.array(fitted_params['a_im']) / PL
    c_im = np.array(fitted_params['c_im']) / (PL**2)
    d_im = 1.0 + np.array(fitted_params['d_im']) * b2
    j_im = np.array(fitted_params['j_im'])

    a_reA12B = -np.array(fitted_params['a_reA12B'])
    c_reA12B = np.array(fitted_params['c_reA12B']) / (PL**2)
    d_reA12B = 1.0 + np.array(fitted_params['d_reA12B']) * b2  
    j_reA12B = np.array(fitted_params['j_reA12B'])

    # Prepare lists to store the jackknife results for plotting
    re_mean, re_err = [], []
    reA12B_mean, reA12B_err = [], []
    im_mean, im_err = [], []
    full_mean, full_err = [], []
    SiverseShift_mean, SiverseShift_err = [], []
    xSiverseShift_mean, xSiverseShift_err = [], []

    print("Evaluating Fourier transforms and applying Jackknife...")

    # 3. Loop over each x value and apply your Jackknife function
    for x in x_vals:
        abs_x = np.abs(x)

        # --- Evaluate Real Part for all ~2900 samples at this x ---
        cd_R = c_re / d_re
        term1_R = (2**(1 - j_re) * a_re * cd_R**(-0.25 - j_re/2) * d_re**(-j_re)) / gamma(j_re)
        term2_R = abs_x**(-0.5 + j_re)
        bessel_R = kv(0.5 - j_re, abs_x / np.sqrt(cd_R))

        re_evals_at_x = term1_R * term2_R * bessel_R

        # Apply your Jackknife function
        m_re, e_re = Jackknife(re_evals_at_x)
        re_mean.append(m_re)
        re_err.append(e_re)

        # --- Evaluate Imaginary Part for all ~2900 samples at this x ---
        cd_I = c_im / d_im
        term1_I = (2**(1 - j_im) * a_im * cd_I**(0.25 * (-3 - 2*j_im)) * d_im**(-j_im)) / gamma(j_im)
        term2_I = x * abs_x**(-1.5 + j_im)
        bessel_I = kv(1.5 - j_im, np.sqrt(d_im / c_im) * abs_x)

        im_evals_at_x = term1_I * term2_I * bessel_I

        # Apply your Jackknife function
        m_im, e_im = Jackknife(im_evals_at_x)
        im_mean.append(m_im)
        im_err.append(e_im)

        m_full, e_full = Jackknife(2*(re_evals_at_x-im_evals_at_x))
        full_mean.append(m_full)
        full_err.append(e_full)

        ####################
        cd_RA12B = c_reA12B / d_reA12B
        term1_RA12B = (2**(1 - j_reA12B) * a_reA12B * cd_RA12B**(-0.25 - j_reA12B/2) * d_reA12B**(-j_reA12B)) / gamma(j_reA12B)
        term2_RA12B = abs_x**(-0.5 + j_reA12B)
        bessel_RA12B = kv(0.5 - j_reA12B, abs_x / np.sqrt(cd_RA12B))

        reA12B_evals_at_x = term1_RA12B * term2_RA12B * bessel_RA12B

        # Apply your Jackknife function
        m_reA12B, e_reA12B = Jackknife(-2*reA12B_evals_at_x)
        reA12B_mean.append(m_reA12B)
        reA12B_err.append(e_reA12B)

        m_SiverseShift, e_SiverseShift = Jackknife((-massterm*reA12B_evals_at_x)/(re_evals_at_x-im_evals_at_x))
        SiverseShift_mean.append(m_SiverseShift)
        SiverseShift_err.append(e_SiverseShift)


        m_xSiverseShift, e_xSiverseShift = Jackknife(x*(-massterm*reA12B_evals_at_x)/(re_evals_at_x-im_evals_at_x))
        xSiverseShift_mean.append(m_xSiverseShift)
        xSiverseShift_err.append(e_xSiverseShift)

    # Convert results to arrays for easier plotting
    re_mean, re_err = np.array(re_mean), np.array(re_err)
    im_mean, im_err = np.array(im_mean), np.array(im_err)
    full_mean, full_err = np.array(full_mean), np.array(full_err)
    reA12B_mean, reA12B_err = np.array(reA12B_mean), np.array(reA12B_err)
    SiverseShift_mean, SiverseShift_err = np.array(SiverseShift_mean), np.array(SiverseShift_err)
    xSiverseShift_mean, xSiverseShift_err = np.array(xSiverseShift_mean), np.array(xSiverseShift_err)

    # 4. Plotting
    #fig, (ax1, ax2, ax3) = plt.subplots(1, 3, figsize=(14, 5))
    fig, ((ax1, ax2, ax3), (ax4, ax5, ax6)) = plt.subplots(2, 3, figsize=(14, 8))

    # Real Plot
    ax1.plot(x_vals, re_mean, color='blue', label='ReA2B Mean')
    ax1.fill_between(x_vals, re_mean - re_err, re_mean + re_err, color='blue', alpha=0.3, label='Jackknife Error Band')
    ax1.set_title(f'$\\tilde{{A}}_{{2B}}^{{Re}}$ ($P_L$={PL}, $b^2$={b2})')
    ax1.set_xlabel('$x$')
    ax1.set_ylabel('$\\tilde{{A}}_{{2B}}^{{Re}}$')
    #ax1.legend()
    ax1.grid(True, linestyle='--', alpha=0.6)

    # Imaginary Plot
    ax2.plot(x_vals, im_mean, color='red', label='ImA2B Mean')
    ax2.fill_between(x_vals, im_mean - im_err, im_mean + im_err, color='red', alpha=0.3, label='Jackknife Error Band')
    ax2.set_title(f'$i\\tilde{{A}}_{{2B}}^{{Im}}$ ($P_L$={PL}, $b^2$={b2})')
    ax2.set_xlabel('$x$')
    ax2.set_ylabel('$i\\tilde{{A}}_{{2B}}^{{Im}}$')
    #ax2.legend()
    ax2.grid(True, linestyle='--', alpha=0.6)


    ax3.plot(x_vals, full_mean, color='green', label='A2B Mean')
    ax3.fill_between(x_vals, full_mean - full_err, full_mean + full_err, color='green', alpha=0.3, label='Jackknife Error Band')
    ax3.set_title(f'$\\tilde{{f}}_{{1}}^{{(0)}}=2\\tilde{{A}}_{{2B}}$ ($P_L$={PL}, $b^2$={b2}) = $\\tilde{{A}}_{{2B}}^{{Re}}+i(i\\tilde{{A}}_{{2B}}^{{Im}})$')
    ax3.set_xlabel('$x$')
    ax3.set_ylabel('$\\tilde{{f}}_{{1}}^{{(0)}}$')
    #ax3.legend()
    ax3.grid(True, linestyle='--', alpha=0.6)

    ax4.plot(x_vals, reA12B_mean, color='blue')
    ax4.fill_between(x_vals, reA12B_mean - reA12B_err, reA12B_mean + reA12B_err, color='blue', alpha=0.3)
    ax4.set_title(f'$\\tilde{{f}}_{{1}}^{{\\perp(1)}}=-2\\tilde{{A}}_{{12B}}$ ($P_L$={PL}, $b^2$={b2})')
    ax4.set_xlabel('$x$')
    ax4.set_ylabel('$\\tilde{{f}}_{{1}}^{{\\perp(1)}}$')
    ax4.grid(True, linestyle='--', alpha=0.6)
    # Create mask for x values from 0 to 1
    mask = x_vals >= 0

    # Sivers Shift Plot (0 to 1)
    ax5.plot(x_vals[mask], SiverseShift_mean[mask], color='blue')
    ax5.fill_between(x_vals[mask], SiverseShift_mean[mask] - SiverseShift_err[mask], 
                     SiverseShift_mean[mask] + SiverseShift_err[mask], color='blue', alpha=0.3)
    ax5.set_title(f'$\\langle k_{{y}} \\rangle_{{TU}}$(GeV) ($P_L$={PL}, $b^2$={b2})')
    ax5.set_xlabel('$x$')
    ax5.set_ylabel('$\\langle k_{{y}} \\rangle_{{TU}}$(GeV)')
    ax5.grid(True, linestyle='--', alpha=0.6)

    # x*Sivers Shift Plot (0 to 1)
    ax6.plot(x_vals[mask], xSiverseShift_mean[mask], color='blue')
    ax6.fill_between(x_vals[mask], xSiverseShift_mean[mask] - xSiverseShift_err[mask], 
                     xSiverseShift_mean[mask] + xSiverseShift_err[mask], color='blue', alpha=0.3)
    ax6.set_title(f'$x\\langle k_{{y}} \\rangle_{{TU}}$(GeV) ($P_L$={PL}, $b^2$={b2})')
    ax6.set_xlabel('$x$')
    ax6.set_ylabel('$x\\langle k_{{y}} \\rangle_{{TU}}$(GeV)')
    ax6.grid(True, linestyle='--', alpha=0.6)

    plt.tight_layout()
    param_keys_str = "-".join(fitted_params.keys())
    file_name = f"SimulFitCovMatrix-A2B-FT-{param_keys_str}.pdf"
    plt.savefig(file_name, format='pdf', bbox_inches='tight')
    plt.show()

    return fig, (ax1, ax2, ax3, ax4, ax5, ax6)


# In[4]:


PL_val = -1
bmin = 3
etaminvalue = 6
etamaxvalue = 10
results, chi2_list = FitSimultaneousA2B(PL=PL_val, bminForFit=bmin, etamin=etaminvalue, etamax=etamaxvalue)
save_path = f"/pscratch/sd/h/hari_8/TMD_fit/h5data/FitParams_SimulFit_f_A2BRe_cetasq_A2BIm_A12BRe_bmin{bmin}_eta{etaminvalue}{etamaxvalue}_PL{PL_val}.h5"
save_params_to_h5(results, chi2_list, save_path)


# In[5]:


PL_val = -2
bmin = 3
etaminvalue = 6
etamaxvalue = 10
results, chi2_list = FitSimultaneousA2B(PL=PL_val, bminForFit=bmin, etamin=etaminvalue, etamax=etamaxvalue)
save_path = f"/pscratch/sd/h/hari_8/TMD_fit/h5data/FitParams_SimulFit_f_A2BRe_cetasq_A2BIm_A12BRe_bmin{bmin}_eta{etaminvalue}{etamaxvalue}_PL{PL_val}.h5"
save_params_to_h5(results, chi2_list, save_path)


# In[6]:


PL_val = -3
bmin = 3
etaminvalue = 6
etamaxvalue = 10
results, chi2_list = FitSimultaneousA2B(PL=PL_val, bminForFit=bmin, etamin=etaminvalue, etamax=etamaxvalue)
save_path = f"/pscratch/sd/h/hari_8/TMD_fit/h5data/FitParams_SimulFit_f_A2BRe_cetasq_A2BIm_A12BRe_bmin{bmin}_eta{etaminvalue}{etamaxvalue}_PL{PL_val}.h5"
save_params_to_h5(results, chi2_list, save_path)


# In[7]:


PL_val = -4
bmin = 3
etaminvalue = 6
etamaxvalue = 10
results, chi2_list = FitSimultaneousA2B(PL=PL_val, bminForFit=bmin, etamin=etaminvalue, etamax=etamaxvalue)
save_path = f"/pscratch/sd/h/hari_8/TMD_fit/h5data/FitParams_SimulFit_f_A2BRe_cetasq_A2BIm_A12BRe_bmin{bmin}_eta{etaminvalue}{etamaxvalue}_PL{PL_val}.h5"
save_params_to_h5(results, chi2_list, save_path)


# In[5]:


PL_val = -4
bmin = 3
etaminvalue = 5
etamaxvalue = 9
results, chi2_list = FitSimultaneousA2B(PL=PL_val, bminForFit=bmin, etamin=etaminvalue, etamax=etamaxvalue)
save_path = f"/pscratch/sd/h/hari_8/TMD_fit/h5data/FitParams_SimulFit_f_A2BRe_cetasq_A2BIm_A12BRe_bmin{bmin}_eta{etaminvalue}{etamaxvalue}_PL{PL_val}.h5"
save_params_to_h5(results, chi2_list, save_path)


# In[5]:


results_1 = FitSimultaneousA2B(PL=-1, bminForFit=3, etamin=6, etamax=10)
fig1, axes1 = plot_fourier_transforms_A2B_A12B(results_1, b2=9, PL=-1)


# In[2]:


results_1 = FitSimultaneousA2B(PL=-2, bminForFit=3, etamin=6, etamax=10)
fig1, axes1 = plot_fourier_transforms_A2B_A12B(results_1, b2=9, PL=-2)


# In[2]:


results_1 = FitSimultaneousA2B(PL=-3, bminForFit=3, etamin=6, etamax=10)
fig1, axes1 = plot_fourier_transforms_A2B_A12B(results_1, b2=9, PL=-3)


# In[3]:


results_1 = FitSimultaneousA2B(PL=-4, bminForFit=3, etamin=6, etamax=10)
fig1, axes1 = plot_fourier_transforms_A2B_A12B(results_1, b2=9, PL=-4)


# In[ ]:




