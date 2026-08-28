import nbformat as nbf
import textwrap

def create_notebook(ansatz_name, re_eq, im_eq, a12b_eq, latex_re, latex_im, latex_a12b, params_re, params_im, params_a12b):
    nb = nbf.v4.new_notebook()
    
    # Imports cell
    imports_code = """import h5py
import numpy as np
import gvar as gv
import math
import matplotlib.pyplot as plt
from IPython.display import display, Markdown

def Jackknife(datalist): 
    N = len(datalist)
    theta_bar = np.mean(datalist, axis=0)
    theta_nminus_theta_bar = []
    for i in range(N): 
        theta_n = datalist[i]
        theta_nminus_theta_bar.append(np.square(theta_n - theta_bar))
    sigma_sq = ((N-1)/N) * np.sum(theta_nminus_theta_bar, axis=0)
    return theta_bar, np.sqrt(sigma_sq)

def fmt_err(mean, err):
    if err <= 0:
        return f"{mean}"
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

def load_params_from_h5(filename):
    fitted_params = {}
    with h5py.File(filename, "r") as f:
        param_group = f["jackknife_samples"]
        for key in param_group.keys():
            fitted_params[key] = param_group[key][:]
        chi2_dof_list = f["chi2_dof"][:]
    return fitted_params, chi2_dof_list
"""
    
    # Settings cell
    settings_code = f"""PL_val = -1
bmin = 3
etaminvalue = 6
etamaxvalue = 10
bT2 = 9 # Fixed bT^2 for plotting
ansatz = "{ansatz_name}"

filename = f"/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/h5data/FitParams_SimulFit_{ansatz_name}_bmin{{bmin}}_eta{{etaminvalue}}{{etamaxvalue}}_PL{{PL_val}}.h5"
fitted_params, chi2 = load_params_from_h5(filename)
"""

    # LaTeX Table Cell
    latex_table_code = f"""def print_latex_table(fitted_params, chi2_dof_list, PL, bmin, etamin, etamax):
    res = {{}}
    for key in fitted_params:
        mean, err = Jackknife(fitted_params[key])
        res[key] = fmt_err(mean, err)
        
    mean_chi2, err_chi2 = Jackknife(chi2_dof_list)
    chi2_str = fmt_err(mean_chi2, err_chi2)

    re_params = {params_re}
    im_params = {params_im}
    a12b_params = {params_a12b}

    vals_re = ", ".join([res[p] for p in re_params])
    vals_im = ", ".join([res[p] for p in im_params])
    vals_a12b = ", ".join([res[p] for p in a12b_params])

    eq_re = r"{latex_re}"
    eq_im = r"{latex_im}"
    eq_a12b = r"{latex_a12b}"

    names_re = r"$\\{{" + ", ".join([p.replace('_reA12B', '').replace('_re', '').replace('_im', '') for p in re_params]) + r"\\}}$"
    names_im = r"$\\{{" + ", ".join([p.replace('_reA12B', '').replace('_re', '').replace('_im', '') for p in im_params]) + r"\\}}$"
    names_a12b = r"$\\{{" + ", ".join([p.replace('_reA12B', '').replace('_re', '').replace('_im', '') for p in a12b_params]) + r"\\}}$"

    md = f"\\n### Simultaneous Fit with common f: \\n for PL={{PL}}, $b_{{{{min}}}} \\\\ge {{bmin}}$, $\\\\eta \\\\in [{{etamin}}, {{etamax}}]$\\n\\n $\\\\chi^2/\\\\text{{{{DoF}}}}$ = {{chi2_str}} (Global)\\n\\n"
    md += "| Amplitude | Model Expression | Params List | Fitted Values |\\n"
    md += "| :--- | :--- | :--- | :--- |\\n"
    md += f"| $\\\\text{{{{Re}}}}A_{{{{2B}}}}$ | {{eq_re}} | {{names_re}} | $[{{vals_re}}]$ |\\n"
    md += f"| $\\\\text{{{{Im}}}}A_{{{{2B}}}}$ | {{eq_im}} | {{names_im}} | $[{{vals_im}}]$ |\\n"
    md += f"| $\\\\text{{{{Re}}}}A_{{{{12B}}}}$ | {{eq_a12b}} | {{names_a12b}} | $[{{vals_a12b}}]$ |\\n"

    display(Markdown(md))

print_latex_table(fitted_params, chi2, PL_val, bmin, etaminvalue, etamaxvalue)
"""

    # Model equations cell
    model_code = f"""# Compute Physical Amplitudes for the {ansatz_name} model
# For physical x-dependence, we extract the structural amplitude stripped of the exp(-f*eta) lattice artifact.
# In the infinite momentum limit (eta -> infinity), the terms (1 - k1/eta - k2/eta^2) -> 1.

# Parameters shape is (N_samples,)
a_re = fitted_params['a_re']
c_re = fitted_params['c_re'] / (PL_val**2)
d_re = fitted_params['d_re']

a_im = fitted_params['a_im'] / PL_val
c_im = fitted_params['c_im'] / (PL_val**2)
d_im = fitted_params['d_im']

a_reA12B = fitted_params['a_reA12B']
c_reA12B = fitted_params['c_reA12B'] / (PL_val**2)
d_reA12B = fitted_params['d_reA12B']

{re_eq}

{im_eq}

{a12b_eq}
"""

    # Fourier Transform Cell
    ft_code = """MassN = 0.6228
lata = 0.11403
massterm = MassN * (197 * 0.001 / lata)

# We evaluate the FT over a dense x-grid to allow precise integration over x later
x_vals = np.linspace(-1, 1, 1000)
lam_grid = np.linspace(-40, 40, 4000)

# Precompute lambdas and b_mags
lam = lam_grid[:, None] # shape (4000, 1)
abs_lam = np.abs(lam)
b_mag = np.sqrt(bT2 + (lam / PL_val)**2) # shape (4000, 1)

# Evaluate physical amplitudes over the lambda grid
re_evals = ReA2B_phys(abs_lam, b_mag, a_re, c_re, d_re)
im_evals = ImA2B_phys(lam, abs_lam, b_mag, a_im, c_im, d_im)
reA12B_evals = ReA12B_phys(abs_lam, b_mag, a_reA12B, c_reA12B, d_reA12B)

re_x = []
im_x = []
full_x = []
reA12B_x = []

print("Performing Numerical Fourier Transform...")
for x in x_vals:
    cos_xl = np.cos(x * lam)
    sin_xl = np.sin(x * lam)
    
    # Integration over lambda using Trapezoidal rule
    int_re = np.trapz(cos_xl * re_evals, x=lam_grid, axis=0) / (2 * np.pi)
    int_im = np.trapz(sin_xl * im_evals, x=lam_grid, axis=0) / (2 * np.pi)
    int_reA12B = np.trapz(cos_xl * reA12B_evals, x=lam_grid, axis=0) / (2 * np.pi)
    
    re_x.append(int_re)
    im_x.append(int_im)
    
    # As requested: A2B = ReA2B - ImA2B
    full_x.append(2 * (int_re - int_im))
    reA12B_x.append(int_reA12B)

# Convert to (N_samples, N_x) arrays for Jackknife
re_x = np.array(re_x).T 
im_x = np.array(im_x).T
full_x = np.array(full_x).T
reA12B_x = np.array(reA12B_x).T

# Calculate Jackknife statistics for plotting
re_mean, re_err = Jackknife(re_x)
im_mean, im_err = Jackknife(im_x)
full_mean, full_err = Jackknife(full_x)
reA12B_mean, reA12B_err = Jackknife(-2 * reA12B_x)

sivers_shift = (-massterm * reA12B_x) / (re_x - im_x)
sivers_mean, sivers_err = Jackknife(sivers_shift)

xsivers_shift = x_vals[None, :] * sivers_shift
xsivers_mean, xsivers_err = Jackknife(xsivers_shift)
print("Finished FT!")
"""

    # Integration Cell
    integration_code = r"""def format_jk(data):
    mean, err = Jackknife(data)
    return fmt_err(mean, err)

print("Computing Integrals over x...")

# We use the computed x-dependence to integrate over specific x regions
# The analytical integral from -infty to infty is exactly the amplitude evaluated at lambda = 0
int_inf_re = re_evals[2000, :] # lambda=0 is at index 2000 in np.linspace(-40, 40, 4000)
int_inf_im = im_evals[2000, :] 
int_inf_reA12B = reA12B_evals[2000, :]

mask_11 = (x_vals >= -1) & (x_vals <= 1)
mask_m10 = (x_vals >= -1) & (x_vals <= 0)
mask_01 = (x_vals >= 0) & (x_vals <= 1)

# Integrate over the x_vals grid
int_11_re = np.trapz(re_x[:, mask_11], x=x_vals[mask_11], axis=1)
int_11_im = np.trapz(im_x[:, mask_11], x=x_vals[mask_11], axis=1)
int_11_reA12B = np.trapz(reA12B_x[:, mask_11], x=x_vals[mask_11], axis=1)

int_m10_re = np.trapz(re_x[:, mask_m10], x=x_vals[mask_m10], axis=1)
int_m10_im = np.trapz(im_x[:, mask_m10], x=x_vals[mask_m10], axis=1)
int_m10_reA12B = np.trapz(reA12B_x[:, mask_m10], x=x_vals[mask_m10], axis=1)

int_01_re = np.trapz(re_x[:, mask_01], x=x_vals[mask_01], axis=1)
int_01_im = np.trapz(im_x[:, mask_01], x=x_vals[mask_01], axis=1)
int_01_reA12B = np.trapz(reA12B_x[:, mask_01], x=x_vals[mask_01], axis=1)

# Compile results: [inf, [-1,1], [-1,0], [0,1]]
res_re = [int_inf_re, int_11_re, int_m10_re, int_01_re]
res_im = [int_inf_im, int_11_im, int_m10_im, int_01_im]
res_f1 = [2*(res_re[i] - res_im[i]) for i in range(4)]
res_f1T = [-2*int_inf_reA12B, -2*int_11_reA12B, -2*int_m10_reA12B, -2*int_01_reA12B]
res_sivers = [massterm * res_f1T[i] / res_f1[i] for i in range(4)]

row1 = [format_jk(d) for d in res_re]
row2 = [format_jk(d) for d in res_im]
row3 = [format_jk(d) for d in res_f1]
row4 = [format_jk(d) for d in res_f1T]
row5 = [format_jk(d) for d in res_sivers]

md_int = "\n### Numerical Integration of Fourier Transforms\n\n"
md_int += "| Integral | $\\{-\\infty, \\infty\\}$ | $\\{-1, 1\\}$ | $\\{-1, 0\\}$ | $\\{0, 1\\}$ |\n"
md_int += "| :--- | :--- | :--- | :--- | :--- |\n"
md_int += f"| $\\int dx \\tilde{{A}}_{{2B}}^{{\\text{{Re}}}}$ | {row1[0]} | {row1[1]} | {row1[2]} | {row1[3]} |\n"
md_int += f"| $\\int dx (i\\tilde{{A}}_{{2B}}^{{\\text{{Im}}}})$ | {row2[0]} | {row2[1]} | {row2[2]} | {row2[3]} |\n"
md_int += f"| $\\tilde{{f}}_1^{{(0)}} = 2\\int dx (\\tilde{{A}}_{{2B}}^{{\\text{{Re}}}} - i\\tilde{{A}}_{{2B}}^{{\\text{{Im}}}})$ | {row3[0]} | {row3[1]} | {row3[2]} | {row3[3]} |\n"
md_int += f"| $\\tilde{{f}}_{{1T}}^{{\\perp(1)}} = -2\\int dx \\tilde{{A}}_{{12B}}$ | {row4[0]} | {row4[1]} | {row4[2]} | {row4[3]} |\n"
md_int += f"| $m_N \\frac{{\\tilde{{f}}_{{1T}}^{{\\perp(1)}}}}{{\\tilde{{f}}_1^{{(0)}}}}$ | {row5[0]} | {row5[1]} | {row5[2]} | {row5[3]} |\n"

display(Markdown(md_int))
"""

    # Plotting cell
    plot_code = r"""fig, ((ax1, ax2, ax3), (ax4, ax5, ax6)) = plt.subplots(2, 3, figsize=(14, 8))

# Real Plot
ax1.plot(x_vals, re_mean, color='blue', label='ReA2B Mean')
ax1.fill_between(x_vals, re_mean - re_err, re_mean + re_err, color='blue', alpha=0.3)
ax1.set_title(fr'$\tilde{{A}}_{{2B}}^{{Re}}$ ($P_L$={PL_val}, $b^2$={bT2})')
ax1.set_xlabel(r'$x$')
ax1.set_ylabel(r'$\tilde{{A}}_{{2B}}^{{Re}}$')
ax1.grid(True, linestyle='--', alpha=0.6)

# Imaginary Plot
ax2.plot(x_vals, im_mean, color='red', label='ImA2B Mean')
ax2.fill_between(x_vals, im_mean - im_err, im_mean + im_err, color='red', alpha=0.3)
ax2.set_title(fr'$i\tilde{{A}}_{{2B}}^{{Im}}$ ($P_L$={PL_val}, $b^2$={bT2})')
ax2.set_xlabel(r'$x$')
ax2.set_ylabel(r'$i\tilde{{A}}_{{2B}}^{{Im}}$')
ax2.grid(True, linestyle='--', alpha=0.6)

# Full f1 Plot
ax3.plot(x_vals, full_mean, color='green', label='A2B Mean')
ax3.fill_between(x_vals, full_mean - full_err, full_mean + full_err, color='green', alpha=0.3)
ax3.set_title(fr'$\tilde{{f}}_{{1}}^{{(0)}}=2\tilde{{A}}_{{2B}}$ ($P_L$={PL_val}, $b^2$={bT2})')
ax3.set_xlabel(r'$x$')
ax3.set_ylabel(r'$\tilde{{f}}_{{1}}^{{(0)}}$')
ax3.grid(True, linestyle='--', alpha=0.6)

# A12B Plot
ax4.plot(x_vals, reA12B_mean, color='blue')
ax4.fill_between(x_vals, reA12B_mean - reA12B_err, reA12B_mean + reA12B_err, color='blue', alpha=0.3)
ax4.set_title(fr'$\tilde{{f}}_{{1T}}^{{\perp(1)}}=-2\tilde{{A}}_{{12B}}$ ($P_L$={PL_val}, $b^2$={bT2})')
ax4.set_xlabel(r'$x$')
ax4.set_ylabel(r'$\tilde{{f}}_{{1T}}^{{\perp(1)}}$')
ax4.grid(True, linestyle='--', alpha=0.6)

mask = x_vals >= 0

# Sivers Shift Plot (0 to 1)
ax5.plot(x_vals[mask], sivers_mean[mask], color='blue')
ax5.fill_between(x_vals[mask], sivers_mean[mask] - sivers_err[mask], 
                 sivers_mean[mask] + sivers_err[mask], color='blue', alpha=0.3)
ax5.set_title(fr'$\langle k_{{y}} \rangle_{{TU}}$(GeV) ($P_L$={PL_val}, $b^2$={bT2})')
ax5.set_xlabel(r'$x$')
ax5.set_ylabel(r'$\langle k_{{y}} \rangle_{{TU}}$(GeV)')
ax5.grid(True, linestyle='--', alpha=0.6)

# x*Sivers Shift Plot (0 to 1)
ax6.plot(x_vals[mask], xsivers_mean[mask], color='blue')
ax6.fill_between(x_vals[mask], xsivers_mean[mask] - xsivers_err[mask], 
                 xsivers_mean[mask] + xsivers_err[mask], color='blue', alpha=0.3)
ax6.set_title(fr'$x\langle k_{{y}} \rangle_{{TU}}$(GeV) ($P_L$={PL_val}, $b^2$={bT2})')
ax6.set_xlabel(r'$x$')
ax6.set_ylabel(r'$x\langle k_{{y}} \rangle_{{TU}}$(GeV)')
ax6.grid(True, linestyle='--', alpha=0.6)

plt.tight_layout()
file_name = f"SimulFitCovMatrix-A12B-A2B-FT-{ansatz}_bmin{bmin}_eta{etaminvalue}{etamaxvalue}_PL{PL_val}.pdf"
plt.savefig(file_name, format='pdf', bbox_inches='tight')
plt.show()
"""
    
    nb['cells'] = [
        nbf.v4.new_markdown_cell(f"# Sivers TMD Analysis: {ansatz_name} Ansatz\nThis notebook computes numerical Fourier transforms to extract the physical Sivers shift."),
        nbf.v4.new_code_cell(imports_code),
        nbf.v4.new_code_cell(settings_code),
        nbf.v4.new_code_cell(latex_table_code),
        nbf.v4.new_code_cell(model_code),
        nbf.v4.new_code_cell(ft_code),
        nbf.v4.new_code_cell(integration_code),
        nbf.v4.new_code_cell(plot_code)
    ]
    
    save_path = f"/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/SimultaniousFit/SimultaneousFit_{ansatz_name}_fromh5.ipynb"
    with open(save_path, 'w') as f:
        nbf.write(nb, f)
    print(f"Generated {save_path}")


# 1. ExpPb_Expb
re_eq_1 = "def ReA2B_phys(abs_lam, b_mag, a_re, c_re, d_re):\n    return a_re * np.exp(-c_re * abs_lam - d_re * b_mag)"
im_eq_1 = "def ImA2B_phys(lam, abs_lam, b_mag, a_im, c_im, d_im):\n    return a_im * (-lam) * np.exp(-c_im * abs_lam - d_im * b_mag)"
a12b_eq_1 = "def ReA12B_phys(abs_lam, b_mag, a_reA12B, c_reA12B, d_reA12B):\n    return -a_reA12B * np.exp(-c_reA12B * abs_lam - d_reA12B * b_mag)"
latex_re_1 = r"\frac{a e^{-f \eta}}{e^{c(1 - k_1/\eta - k_2/\eta^2)|b_L P_L| + d b}}"
latex_im_1 = r"\frac{a (b_L P_L) e^{-f \eta}}{e^{c |b_L P_L| + d b}}"
latex_a12b_1 = r"\frac{-a e^{-f \eta}}{e^{c |b_L P_L| + d b}}"
p_re_1 = "['a_re', 'c_re', 'd_re', 'k1_re', 'k2_re', 'f']"
p_im_1 = "['a_im', 'c_im', 'd_im', 'f']"
p_a12b_1 = "['a_reA12B', 'c_reA12B', 'd_reA12B', 'f']"
create_notebook("ExpPb_Expb", re_eq_1, im_eq_1, a12b_eq_1, latex_re_1, latex_im_1, latex_a12b_1, p_re_1, p_im_1, p_a12b_1)

# 2. ExpPb_PowerLawb
re_eq_2 = "def ReA2B_phys(abs_lam, b_mag, a_re, c_re, d_re):\n    j_re = fitted_params['j_re']\n    return a_re * np.exp(-c_re * abs_lam) / (1 + d_re * b_mag**2)**j_re"
im_eq_2 = "def ImA2B_phys(lam, abs_lam, b_mag, a_im, c_im, d_im):\n    j_im = fitted_params['j_im']\n    return a_im * (-lam) * np.exp(-c_im * abs_lam) / (1 + d_im * b_mag**2)**j_im"
a12b_eq_2 = "def ReA12B_phys(abs_lam, b_mag, a_reA12B, c_reA12B, d_reA12B):\n    j_reA12B = fitted_params['j_reA12B']\n    return -a_reA12B * np.exp(-c_reA12B * abs_lam) / (1 + d_reA12B * b_mag**2)**j_reA12B"
latex_re_2 = r"\frac{a e^{-f \eta}}{e^{c(1 - k_1/\eta - k_2/\eta^2)|b_L P_L|} [1 + d b^2]^j}"
latex_im_2 = r"\frac{a (b_L P_L) e^{-f \eta}}{e^{c |b_L P_L|} [1 + d b^2]^j}"
latex_a12b_2 = r"\frac{-a e^{-f \eta}}{e^{c |b_L P_L|} [1 + d b^2]^j}"
p_re_2 = "['a_re', 'c_re', 'd_re', 'j_re', 'k1_re', 'k2_re', 'f']"
p_im_2 = "['a_im', 'c_im', 'd_im', 'j_im', 'f']"
p_a12b_2 = "['a_reA12B', 'c_reA12B', 'd_reA12B', 'j_reA12B', 'f']"
create_notebook("ExpPb_PowerLawb", re_eq_2, im_eq_2, a12b_eq_2, latex_re_2, latex_im_2, latex_a12b_2, p_re_2, p_im_2, p_a12b_2)

# 3. GaussianPb_Expb
re_eq_3 = "def ReA2B_phys(abs_lam, b_mag, a_re, c_re, d_re):\n    return a_re * np.exp(-c_re * abs_lam**2 - d_re * b_mag)"
im_eq_3 = "def ImA2B_phys(lam, abs_lam, b_mag, a_im, c_im, d_im):\n    return a_im * (-lam) * np.exp(-c_im * abs_lam**2 - d_im * b_mag)"
a12b_eq_3 = "def ReA12B_phys(abs_lam, b_mag, a_reA12B, c_reA12B, d_reA12B):\n    return -a_reA12B * np.exp(-c_reA12B * abs_lam**2 - d_reA12B * b_mag)"
latex_re_3 = r"\frac{a e^{-f \eta}}{e^{c(1 - k_1/\eta - k_2/\eta^2)|b_L P_L|^2 + d b}}"
latex_im_3 = r"\frac{a (b_L P_L) e^{-f \eta}}{e^{c |b_L P_L|^2 + d b}}"
latex_a12b_3 = r"\frac{-a e^{-f \eta}}{e^{c |b_L P_L|^2 + d b}}"
create_notebook("GaussianPb_Expb", re_eq_3, im_eq_3, a12b_eq_3, latex_re_3, latex_im_3, latex_a12b_3, p_re_1, p_im_1, p_a12b_1)

# 4. GaussianPb_PowerLawb
re_eq_4 = "def ReA2B_phys(abs_lam, b_mag, a_re, c_re, d_re):\n    j_re = fitted_params['j_re']\n    return a_re * np.exp(-c_re * abs_lam**2) / (1 + d_re * b_mag**2)**j_re"
im_eq_4 = "def ImA2B_phys(lam, abs_lam, b_mag, a_im, c_im, d_im):\n    j_im = fitted_params['j_im']\n    return a_im * (-lam) * np.exp(-c_im * abs_lam**2) / (1 + d_im * b_mag**2)**j_im"
a12b_eq_4 = "def ReA12B_phys(abs_lam, b_mag, a_reA12B, c_reA12B, d_reA12B):\n    j_reA12B = fitted_params['j_reA12B']\n    return -a_reA12B * np.exp(-c_reA12B * abs_lam**2) / (1 + d_reA12B * b_mag**2)**j_reA12B"
latex_re_4 = r"\frac{a e^{-f \eta}}{e^{c(1 - k_1/\eta - k_2/\eta^2)|b_L P_L|^2} [1 + d b^2]^j}"
latex_im_4 = r"\frac{a (b_L P_L) e^{-f \eta}}{e^{c |b_L P_L|^2} [1 + d b^2]^j}"
latex_a12b_4 = r"\frac{-a e^{-f \eta}}{e^{c |b_L P_L|^2} [1 + d b^2]^j}"
create_notebook("GaussianPb_PowerLawb", re_eq_4, im_eq_4, a12b_eq_4, latex_re_4, latex_im_4, latex_a12b_4, p_re_2, p_im_2, p_a12b_2)
