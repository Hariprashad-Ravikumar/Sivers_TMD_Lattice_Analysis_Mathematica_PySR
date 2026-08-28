import h5py
import numpy as np
import gvar as gv
import math
import matplotlib.pyplot as plt

def Jackknife(datalist): 
    N = len(datalist)
    theta_bar = np.mean(datalist, axis=0)
    theta_nminus_theta_bar = []
    for i in range(N): 
        theta_n = datalist[i]
        theta_nminus_theta_bar.append(np.square(theta_n - theta_bar))
    sigma_sq = ((N-1)/N) * np.sum(theta_nminus_theta_bar, axis=0)
    return theta_bar, np.sqrt(sigma_sq)

def load_params_from_h5(filename):
    fitted_params = {}
    with h5py.File(filename, "r") as f:
        param_group = f["jackknife_samples"]
        for key in param_group.keys():
            fitted_params[key] = param_group[key][:]
        chi2_dof_list = f["chi2_dof"][:]
    return fitted_params, chi2_dof_list

fitted_params, chi2 = load_params_from_h5("/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/h5data/FitParams_SimulFit_ExpPb_Expb_bmin3_eta610_PL-1.h5")

MassN = 0.6228
lata = 0.11403
massterm = MassN * (197 * 0.001 / lata)

# Plot for PL = -1, bT^2 = 9
PL = -1
bT2 = 9

# Parameters shape is (N_samples,)
a_re = fitted_params['a_re']
c_re = fitted_params['c_re'] / (PL**2)
d_re = fitted_params['d_re']

a_im = fitted_params['a_im'] / PL
c_im = fitted_params['c_im'] / (PL**2)
d_im = fitted_params['d_im']

a_reA12B = fitted_params['a_reA12B']
c_reA12B = fitted_params['c_reA12B'] / (PL**2)
d_reA12B = fitted_params['d_reA12B']

x_vals = np.linspace(-1, 1, 200)
lam_grid = np.linspace(-40, 40, 4000)
dlam = lam_grid[1] - lam_grid[0]

# Precompute lambdas and b_mags
lam = lam_grid[:, None] # shape (4000, 1)
abs_lam = np.abs(lam)
b_mag = np.sqrt(bT2 + (lam / PL)**2) # shape (4000, 1)

# ExpPb_Expb Physical Amplitudes (shape: 4000, N_samples)
re_evals = a_re * np.exp(-c_re * abs_lam - d_re * b_mag)
im_evals = a_im * (-lam) * np.exp(-c_im * abs_lam - d_im * b_mag)
reA12B_evals = -a_reA12B * np.exp(-c_reA12B * abs_lam - d_reA12B * b_mag)

print("Shape of re_evals:", re_evals.shape)

re_x = []
im_x = []
full_x = []
reA12B_x = []

for x in x_vals:
    cos_xl = np.cos(x * lam)
    sin_xl = np.sin(x * lam)
    
    int_re = np.trapz(cos_xl * re_evals, x=lam_grid, axis=0) / (2 * np.pi)
    int_im = np.trapz(sin_xl * im_evals, x=lam_grid, axis=0) / (2 * np.pi)
    int_reA12B = np.trapz(cos_xl * reA12B_evals, x=lam_grid, axis=0) / (2 * np.pi)
    
    re_x.append(int_re)
    im_x.append(int_im)
    full_x.append(2 * (int_re + int_im))
    reA12B_x.append(int_reA12B)

re_x = np.array(re_x) # shape (200, N_samples)
im_x = np.array(im_x)
full_x = np.array(full_x)
reA12B_x = np.array(reA12B_x)

re_mean, re_err = Jackknife(re_x)
im_mean, im_err = Jackknife(im_x)
full_mean, full_err = Jackknife(full_x)
reA12B_mean, reA12B_err = Jackknife(-2 * reA12B_x)

sivers_shift = (-massterm * reA12B_x) / (re_x + im_x)
sivers_mean, sivers_err = Jackknife(sivers_shift)

xsivers_shift = x_vals[:, None] * sivers_shift
xsivers_mean, xsivers_err = Jackknife(xsivers_shift)

mask = x_vals >= 0
plt.plot(x_vals[mask], sivers_mean[mask], color='blue')
plt.fill_between(x_vals[mask], sivers_mean[mask] - sivers_err[mask], sivers_mean[mask] + sivers_err[mask], color='blue', alpha=0.3)
plt.title("Sivers Shift (Numerical FT)")
plt.savefig("test_numerical_FT.pdf")
print("Saved test plot successfully!")
