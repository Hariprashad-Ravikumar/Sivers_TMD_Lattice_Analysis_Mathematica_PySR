import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as _plt
_plt.show = lambda *a, **k: None

# ===== notebook cell 7 =====
import h5py
import numpy as np
import math
from tqdm.auto import tqdm
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from scipy.special import kv, gamma

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

def load_params_from_h5(filename):
    fitted_params = {}
    with h5py.File(filename, "r") as f:
        # Load the jackknifed parameter samples
        param_group = f["jackknife_samples"]
        for key in param_group.keys():
            fitted_params[key] = param_group[key][:]
            
        # Load the chi-square per dof array
        chi2_dof_list = f["chi2_dof"][:]
        
    return fitted_params, chi2_dof_list

# ---------------------------------------------------------
# 2. 3D Plotting Function (Distinct Slices for 1/PL)
# ---------------------------------------------------------
def plot_fourier_transforms_3D_PL_discrete(PL_list, bminfit, etamin, etamax, b2=9.0, num_points_x=500):
    pl_to_zeta = {-4: 0.785756, -3: 0.539684, -2: 0.294367, -1: 0.090772}
    
    # 1. Setup X (x-values)
    x_vals = np.linspace(-1, 1, num_points_x)
    
    

    #P_L_GeV = np.round(PL * (197.32698 * 0.001 * 2 * np.pi / (lata * 32)), 2)
    
    # Calculate 1/PL and sort them
    inv_zeta_vals = np.array([1.0 / pl_to_zeta.get(pl) for pl in PL_list])
    sort_idx = np.argsort(inv_zeta_vals)
    inv_zeta_vals = inv_zeta_vals[sort_idx]
    sorted_PL_list = [PL_list[i] for i in sort_idx]

    # Initialize figure
    fig = plt.figure(figsize=(13, 10))      # amplitudes, 2x2
    ax1 = fig.add_subplot(221, projection='3d')
    ax2 = fig.add_subplot(222, projection='3d')
    ax3 = fig.add_subplot(223, projection='3d')
    ax4 = fig.add_subplot(224, projection='3d')
    fig_k = plt.figure(figsize=(13, 5))     # Sivers shift, 1x2
    ax5 = fig_k.add_subplot(121, projection='3d')
    ax6 = fig_k.add_subplot(122, projection='3d')
    
    axes = [ax1, ax2, ax3, ax4, ax5, ax6]

    # Helper function to plot a discrete 3D slice (line + vertical error band)
    def add_discrete_3d_band(ax, x, y_val, mean, err, color):
        # Plot the central mean line
        ax.plot(x, [y_val]*len(x), mean, color=color, linewidth=2)
        
        # Create a vertical polygon for the error band
        x_poly = np.concatenate([x, x[::-1]])
        y_poly = np.full_like(x_poly, y_val)
        z_poly = np.concatenate([mean - err, (mean + err)[::-1]])
        
        # Add polygon to axes
        verts = [list(zip(x_poly, y_poly, z_poly))]
        poly = Poly3DCollection(verts, color=color, alpha=0.3)
        ax.add_collection3d(poly)
        
        # Update limits manually since add_collection3d doesn't auto-scale Z
        ax.auto_scale_xyz(x, [y_val]*len(x), z_poly, had_data=True)

    print(f"\nEvaluating discrete Fourier transforms over PL list for fixed b^2 = {b2}...")
    lata = 0.11403
    # Loop over PL
    for i, pl in enumerate(tqdm(sorted_PL_list, desc="Evaluating PL slices")):
        #lata = 0.11403
        mass_filepath = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/TMD_fit/h5data/MassN_Jackknife.h5"
        with h5py.File(mass_filepath, "r") as f:
            MassN_jk = f["PL_-1"][:]   # P_L=-1 jackknife nucleon mass for every slice
        massterm = MassN_jk * (197 * 0.001 / lata)
        
        y_val = 1.0 / pl_to_zeta[pl]
        
        # Dynamically load the data for the current PL
        filename = f"/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/TMD_fit/h5data/FitParams_SimulFit_f_A2BRe_cetasq_A2BIm_A12BRe_bmin{bminfit}_eta{etamin}{etamax}_PL{pl}.h5"
        fitted_params, _ = load_params_from_h5(filename)
        
        # Extract parameters specifically scaled for this PL
        a_re = np.array(fitted_params['a_re']) / (np.sqrt(2*np.pi))
        c_re = np.array(fitted_params['c_re']) / (pl**2)
        j_re = np.array(fitted_params['j_re'])
        d_re = 1.0 + np.array(fitted_params['d_re']) * b2  

        a_im = np.array(fitted_params['a_im']) / (pl*np.sqrt(2*np.pi))
        c_im = np.array(fitted_params['c_im']) / (pl**2)
        j_im = np.array(fitted_params['j_im'])
        d_im = 1.0 + np.array(fitted_params['d_im']) * b2

        a_reA12B = -np.array(fitted_params['a_reA12B']) / (np.sqrt(2*np.pi))
        c_reA12B = np.array(fitted_params['c_reA12B']) / (pl**2)
        j_reA12B = np.array(fitted_params['j_reA12B'])
        d_reA12B = 1.0 + np.array(fitted_params['d_reA12B']) * b2
        
        # Initialize arrays for this specific slice
        re_m, re_e = np.zeros_like(x_vals), np.zeros_like(x_vals)
        im_m, im_e = np.zeros_like(x_vals), np.zeros_like(x_vals)
        full_m, full_e = np.zeros_like(x_vals), np.zeros_like(x_vals)
        reA12B_m, reA12B_e = np.zeros_like(x_vals), np.zeros_like(x_vals)
        siv_m, siv_e = np.zeros_like(x_vals), np.zeros_like(x_vals)
        xsiv_m, xsiv_e = np.zeros_like(x_vals), np.zeros_like(x_vals)
        
        # Evaluate for each x
        for j, x in enumerate(x_vals):
            abs_x = max(np.abs(x), 1e-12)
            safe_x = x if x != 0 else 1e-12

            # --- Evaluate Real Part ---
            cd_R = c_re / d_re
            term1_R = (2**(1 - j_re) * a_re * cd_R**(-0.25 - j_re/2) * d_re**(-j_re)) / gamma(j_re)
            term2_R = abs_x**(-0.5 + j_re)
            bessel_R = kv(0.5 - j_re, abs_x / np.sqrt(cd_R))
            re_evals = term1_R * term2_R * bessel_R
            re_m[j], re_e[j] = Jackknife(re_evals)

            # --- Evaluate Imaginary Part ---
            cd_I = c_im / d_im
            term1_I = (2**(1 - j_im) * a_im * cd_I**(0.25 * (-3 - 2*j_im)) * d_im**(-j_im)) / gamma(j_im)
            term2_I = safe_x * abs_x**(-1.5 + j_im)
            bessel_I = kv(1.5 - j_im, np.sqrt(d_im / c_im) * abs_x)
            im_evals = term1_I * term2_I * bessel_I
            im_m[j], im_e[j] = Jackknife(im_evals)

            # --- Full A2B ---
            full_m[j], full_e[j] = Jackknife(2*(re_evals - im_evals))

            # --- Evaluate ReA12B Part ---
            cd_RA12B = c_reA12B / d_reA12B
            term1_RA12B = (2**(1 - j_reA12B) * a_reA12B * cd_RA12B**(-0.25 - j_reA12B/2) * d_reA12B**(-j_reA12B)) / gamma(j_reA12B)
            term2_RA12B = abs_x**(-0.5 + j_reA12B)
            bessel_RA12B = kv(0.5 - j_reA12B, abs_x / np.sqrt(cd_RA12B))
            reA12B_evals = term1_RA12B * term2_RA12B * bessel_RA12B
            reA12B_m[j], reA12B_e[j] = Jackknife(-2*reA12B_evals)

            # --- Sivers Shift ---
            siv_evals = (-massterm * reA12B_evals) / (re_evals - im_evals)
            siv_m[j], siv_e[j] = Jackknife(siv_evals)
            xsiv_m[j], xsiv_e[j] = Jackknife(safe_x * siv_evals)

        # Draw the slices onto the subplots
        add_discrete_3d_band(ax1, x_vals, y_val, re_m, re_e, 'blue')
        add_discrete_3d_band(ax2, x_vals, y_val, im_m, im_e, 'red')
        add_discrete_3d_band(ax3, x_vals, y_val, full_m, full_e, 'purple')
        add_discrete_3d_band(ax4, x_vals, y_val, reA12B_m, reA12B_e, 'green')

        # Sivers shift plots (Masked for x >= 0)
        mask = x_vals >= 0
        x_pos = x_vals[mask]
        add_discrete_3d_band(ax5, x_pos, y_val, siv_m[mask], siv_e[mask], 'olive')
        add_discrete_3d_band(ax6, x_pos, y_val, xsiv_m[mask], xsiv_e[mask], 'olive')

    # ---------------------------------------------------------
    # 3. Apply Formatting & Labels to all subplots
    # ---------------------------------------------------------
    titles = [
        f'$\\widetilde{{A}}^{{[x]\\mathrm{{Re}}}}_{{2B}}$ ($b^2$={b2})',
        f'$\\widetilde{{A}}^{{[x]\\mathrm{{Im}}}}_{{2B}}$ ($b^2$={b2})',
        f'$\\tilde{{f}}_{{1}}^{{(0)}}=2\\widetilde{{A}}^{{[x]}}_{{2B}}$ ($b^2$={b2})',
        f'$\\tilde{{f}}_{{1T}}^{{\\perp(1)}}=-2\\widetilde{{A}}^{{[x]\\mathrm{{Re}}}}_{{12B}}$ ($b^2$={b2})',
        f'$\\langle k_{{y}} \\rangle_{{TU}}$(GeV) ($b^2$={b2})',
        f'$x\\langle k_{{y}} \\rangle_{{TU}}$(GeV) ($b^2$={b2})'
    ]
    
    zlabels = [
        '$\\widetilde{A}^{[x]\\mathrm{Re}}_{2B}$', '$\\widetilde{A}^{[x]\\mathrm{Im}}_{2B}$', '$\\tilde{f}_{1}^{(0)}$',
        '$\\tilde{f}_{1T}^{\\perp(1)}$', '$\\langle k_{y} \\rangle_{TU}$(GeV)', '$x\\langle k_{y} \\rangle_{TU}$(GeV)'
    ]

    for idx, ax in enumerate(axes):
        ax.set_title(titles[idx])
        ax.set_xlabel('$x$')
        ax.set_ylabel('$1/\\hat\\zeta$', labelpad=10)
        ax.set_zlabel(zlabels[idx])
        
        # Enforce strict discrete ticks on the Y-axis so only exact 1/PL values appear
        ax.set_yticks(inv_zeta_vals)
        # vertical labels on a lengthened (still linear) 1/zeta-hat axis so 1.27, 1.85, 3.40, 11.02 do not overlap
        ax.set_yticklabels([f"{v:.2f}" for v in inv_zeta_vals], rotation=90, va="top", ha="center", fontsize=8)
        ax.set_box_aspect((1, 2.2, 1))
        ax.xaxis.set_major_locator(plt.MaxNLocator(3))   # fewer x ticks on the shortened x-axis
        ax.view_init(elev=20, azim=-50)

    #plt.tight_layout()
    file_stem = f"SimulFit_Distinct_1_over_PL_bmin{bminfit}_eta{etamin}{etamax}_b2{b2}"
    fig.savefig(f"{file_stem}_Amps.pdf", format='pdf', bbox_inches='tight', pad_inches=0.35)
    fig_k.savefig(f"{file_stem}_Sivers.pdf", format='pdf', bbox_inches='tight', pad_inches=0.35)
    plt.show()

# ---------------------------------------------------------

# ---------------------------------------------------------
bminfit = 3
etamin = 6
etamax = 10
PL_list = [-1, -2, -3, -4]

#num_points_x=500
# Execute the plot
plot_fourier_transforms_3D_PL_discrete(PL_list, bminfit, etamin, etamax, b2=9.0)
