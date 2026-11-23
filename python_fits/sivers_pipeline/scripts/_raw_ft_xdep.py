import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as _plt
_plt.show = lambda *a, **k: None

# ===== notebook cell 0 =====
import h5py
import numpy as np
import gvar as gv
import math
import lsqfit
import matplotlib.pyplot as plt
from scipy.special import kv, gamma
#import warnings
#warnings.filterwarnings('ignore', category=RuntimeWarning)

# np.trapezoid (numpy >= 2.0) is np.trapz in older numpy; same trapezoidal rule.
_trapezoid = getattr(np, "trapezoid", None) or np.trapz

# ---------------------------------------------------------
# Notation (thesis): \tAmp^{[x]} denotes the Fourier transform over b.P,
#   \tilde f_1^{(0)} = 2 \tAmp^{[x]}_{2B},  \tilde f_{1T}^{\perp(1)} = -2 \tAmp^{[x]}_{12B}
# ---------------------------------------------------------

# Nucleon mass (lattice units) and hbar*c used for every thesis table/figure
MassN = 0.6228
HBARC_MEV_FM = 197
lata = 0.11403

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

def ReA2B(eta, bL, bT, a, c, d, f, k1, k2, j):
    denom = (1 + (d + c * (1 - k1/eta - k2/eta**2)) * bL**2 + d * bT**2)**j
    return a * gv.exp(-f * eta) / denom

def ImA2B(eta, bL, bT, a, c, d, f, j):
    denom = (1 + (d + c) * bL**2 + d * bT**2)**j
    return a * bL * gv.exp(-f * eta) / denom

def ReA12B(eta, bL, bT, a, c, d, f, j):
    denom = (1 + (d + c) * bL**2 + d * bT**2)**j
    return -a * gv.exp(-f * eta) / denom

def load_params_from_h5(filename):
    fitted_params = {}
    with h5py.File(filename, "r") as f:
        # 1. Load the jackknifed parameter samples
        param_group = f["jackknife_samples"]
        for key in param_group.keys():
            # Read the dataset back into a numpy array
            fitted_params[key] = param_group[key][:]

        # 2. Load the chi-square per dof array
        chi2_dof_list = f["chi2_dof"][:]

    return fitted_params, chi2_dof_list


def format_jk(data):
    mean, err = Jackknife(data)
    return fmt_err(mean, err)


def print_latex_table(fitted_params, chi2_dof_list, PL, bmin, etamin, etamax):
    # Calculate jackknifed means and errors for all parameters
    res = {}
    for key in fitted_params:
        res[key] = format_jk(fitted_params[key])

    chi2_str = format_jk(chi2_dof_list)

    # Group parameters by Amplitude ('f' is shared by all three)
    re_params = ['a_re', 'c_re', 'd_re', 'k1_re', 'k2_re', 'j_re', 'f']
    im_params = ['a_im', 'c_im', 'd_im', 'j_im', 'f']
    a12b_params = ['a_reA12B', 'c_reA12B', 'd_reA12B', 'j_reA12B', 'f']

    vals_re = ", ".join([res[p] for p in re_params])
    vals_im = ", ".join([res[p] for p in im_params])
    vals_a12b = ", ".join([res[p] for p in a12b_params])

    eq_re = r"$\frac{a e^{-f \eta}}{\left[1 + \left(d + c\left(1 - \frac{k_1}{\eta} - \frac{k_2}{\eta^2}\right)\right) b_L^2 + d b_T^2\right]^j}$"
    eq_im = r"$\frac{a b_L e^{-f \eta}}{\left[1 + (c + d) b_L^2 + d b_T^2\right]^j}$"
    eq_a12b = r"$\frac{-a e^{-f \eta}}{\left[1 + (c + d) b_L^2 + d b_T^2\right]^j}$"

    names_re = r"$\{a, c, d, k_1, k_2, j, f\}$"
    names_im = r"$\{a, c, d, j, f\}$"
    names_a12b = r"$\{a, c, d, j, f\}$"

    # Amplitude labels: b-space amplitudes (no Fourier transform here)
    lab_re = r"$\tAmp_{2B}^{\text{Re}}$"
    lab_im = r"$\tAmp_{2B}^{\text{Im}}$"
    lab_a12b = r"$\tAmp_{12B}^{\text{Re}}$"
    # Markdown preview cannot see the thesis macro \tAmp
    md_lab = lambda s: s.replace(r"\tAmp", r"\widetilde{A}")

    md = f"\n### Simultaneous Fit with common f: \n for PL={PL}, $b_{{min}} \\ge {bmin}$, $\\eta \\in [{etamin}, {etamax}]$\n\n $\\chi^2/\\text{{DoF}}$ = {chi2_str} (Global)\n\n"
    md += "| Amplitude | Model Expression | Params List | Fitted Values |\n"
    md += "| :--- | :--- | :--- | :--- |\n"
    md += f"| {md_lab(lab_re)} | {eq_re} | {names_re} | $[{vals_re}]$ |\n"
    md += f"| {md_lab(lab_im)} | {eq_im} | {names_im} | $[{vals_im}]$ |\n"
    md += f"| {md_lab(lab_a12b)} | {eq_a12b} | {names_a12b} | $[{vals_a12b}]$ |\n"

    try:
        from IPython.display import display, Markdown
        display(Markdown(md))
    except ImportError:
        print(md)
    with open(f"Fit_Table_PL{PL}_bmin{bmin}.md", "w") as text_file:
        text_file.write(md)

    tex = "\\begin{table}[htpb]\n\\centering\n"
    tex += "\\renewcommand{\\arraystretch}{1.5}\n"
    tex += f"\\caption{{Simultaneous Fit with common $f$: for $P_L={PL}$, $b_{{min}} \\ge {bmin}$, $\\eta \\in [{etamin}, {etamax}]$. Global $\\chi^2/\\text{{DoF}} = {chi2_str}$}}\n"
    tex += "\\scalebox{0.5}{\\begin{tabular}{|l|l|l|l|}\n\\hline\n"
    tex += "Amplitude & Model Expression & Params List & Fitted Values \\\\\n\\hline\n"
    tex += f"{lab_re} & {eq_re} & {names_re} & $[{vals_re}]$ \\\\\n"
    tex += f"{lab_im} & {eq_im} & {names_im} & $[{vals_im}]$ \\\\\n"
    tex += f"{lab_a12b} & {eq_a12b} & {names_a12b} & $[{vals_a12b}]$ \\\\\n"
    tex += "\\hline\n\\end{tabular}}\n\\end{table}\n"

    with open(f"Fit_Table_PL{PL}_bmin{bmin}.tex", "w") as f:
        f.write(tex)


# Row labels of the integration table (thesis macro \tAmp)
INTEGRATION_LABELS = [
    r"$\int dx\, \tAmp^{[x]\text{Re}}_{2B}$",
    r"$\int dx\, (\tAmp^{[x]\text{Im}}_{2B})$",
    r"$\int dx\, \tilde{f}_1^{(0)} = 2\int dx\, (\tAmp^{[x]\text{Re}}_{2B} - \tAmp^{[x]\text{Im}}_{2B})$",
    r"$\int dx\, \tilde{f}_{1T}^{\perp(1)} = -2\int dx\, \tAmp^{[x]\text{Re}}_{12B}$",
    r"$m_N \frac{\int dx\, \tilde{f}_{1T}^{\perp(1)}}{\int dx\, \tilde{f}_1^{(0)}}$ (GeV)",
]


def print_integration_latex_table(res_inf, res_11, res_m10, res_01, PL, bmin, b2):
    # res indices: 0: Re A2B, 1: i Im A2B, 2: f1_0, 3: f1T_perp, 4: sivers_ratio
    rows = [[format_jk(res_inf[i]), format_jk(res_11[i]), format_jk(res_m10[i]), format_jk(res_01[i])]
            for i in range(5)]

    tex = "\\begin{table}[htpb]\n\\centering\n"
    tex += "\\renewcommand{\\arraystretch}{1.8}\n"
    tex += f"\\caption{{Numerical Integration of Fourier Transforms: $P_L={PL}, b_{{min}} \\ge {bmin}$}}\n"
    tex += "\\scalebox{0.5}{\\begin{tabular}{|l|c|c|c|c|}\n\\hline\n"
    tex += "Integral & $[-\\infty, \\infty]$ & $[-1, 1]$ & $[-1, 0]$ & $[0, 1]$ \\\\\n\\hline\n"
    for label, row_data in zip(INTEGRATION_LABELS, rows):
        tex += f"{label} & {' & '.join(row_data)} \\\\\n"
    tex += "\\hline\n\\end{tabular}}\n\\end{table}\n"
    with open(f"Integration_Table_PL{PL}_bmin{bmin}_b2-{b2}.tex", "w") as f:
        f.write(tex)

    md = "\n### Numerical Integration of Fourier Transforms\n\n"
    md += "| Integral | $\\{-\\infty, \\infty\\}$ | $\\{-1, 1\\}$ | $\\{-1, 0\\}$ | $\\{0, 1\\}$ |\n"
    md += "| :--- | :--- | :--- | :--- | :--- |\n"
    for label, row_data in zip(INTEGRATION_LABELS, rows):
        md += f"| {label.replace(chr(92) + 'tAmp', chr(92) + 'widetilde{A}')} | {' | '.join(row_data)} |\n"
    try:
        from IPython.display import display, Markdown
        display(Markdown(md))
    except ImportError:
        print(md)
    with open(f"Integration_Table_PL{PL}_bmin{bmin}_b2-{b2}.md", "w") as text_file:
        text_file.write(md)


def ft_evaluators(fitted_params, b2, PL):
    """Return a function x_grid -> (Re A2B, i Im A2B, Re A12B) Fourier transforms,
    each of shape (len(x_grid), N_jk)."""
    a_re = np.array(fitted_params['a_re']) / (np.sqrt(2*np.pi))
    c_re = np.array(fitted_params['c_re']) / (PL**2)
    d_re = 1.0 + np.array(fitted_params['d_re']) * b2
    j_re = np.array(fitted_params['j_re'])

    a_im = np.array(fitted_params['a_im']) / (PL*np.sqrt(2*np.pi))
    c_im = np.array(fitted_params['c_im']) / (PL**2)
    d_im = 1.0 + np.array(fitted_params['d_im']) * b2
    j_im = np.array(fitted_params['j_im'])

    a_reA12B = -np.array(fitted_params['a_reA12B']) / (np.sqrt(2*np.pi))
    c_reA12B = np.array(fitted_params['c_reA12B']) / (PL**2)
    d_reA12B = 1.0 + np.array(fitted_params['d_reA12B']) * b2
    j_reA12B = np.array(fitted_params['j_reA12B'])

    def evals(x_grid):
        abs_x = np.abs(x_grid)

        # Re A2B
        cd_R = c_re / d_re
        term1_R = (2**(1 - j_re) * a_re * cd_R**(-0.25 - j_re/2) * d_re**(-j_re)) / gamma(j_re)
        re_evals = term1_R * abs_x**(-0.5 + j_re) * kv(0.5 - j_re, abs_x / np.sqrt(cd_R))

        # i Im A2B
        cd_I = c_im / d_im
        term1_I = (2**(1 - j_im) * a_im * cd_I**(0.25 * (-3 - 2*j_im)) * d_im**(-j_im)) / gamma(j_im)
        im_evals = term1_I * x_grid * abs_x**(-1.5 + j_im) * kv(1.5 - j_im, np.sqrt(d_im / c_im) * abs_x)

        # Re A12B
        cd_RA12B = c_reA12B / d_reA12B
        term1_RA12B = (2**(1 - j_reA12B) * a_reA12B * cd_RA12B**(-0.25 - j_reA12B/2) * d_reA12B**(-j_reA12B)) / gamma(j_reA12B)
        reA12B_evals = term1_RA12B * abs_x**(-0.5 + j_reA12B) * kv(0.5 - j_reA12B, abs_x / np.sqrt(cd_RA12B))

        return re_evals, im_evals, reA12B_evals

    return evals


def plot_fourier_transforms_A2B_A12B(fitted_params, chi2_dof_list, b2, PL, bminfit, etamin, etamax, num_points=200):
    print_latex_table(fitted_params, chi2_dof_list, PL, bminfit, etamin, etamax)

    x_vals = np.linspace(-1, 1, num_points)
    massterm = MassN * (HBARC_MEV_FM * 0.001 / lata)
    evals = ft_evaluators(fitted_params, b2, PL)

    # =========================================================================
    # 1. Numerical integration over x
    # =========================================================================
    print("\nComputing Numerical Integrals across Jackknife samples...")

    # -infinity..infinity approximated by -40..40 (the transforms decay exponentially)
    x_inf = np.linspace(-40, 40, 4000)[:, None]
    x_11  = np.linspace(-1, 1, 1000)[:, None]
    x_m10 = np.linspace(-1, 0, 1000)[:, None]
    x_01  = np.linspace(0, 1, 1000)[:, None]

    # Safeguard against exactly zero
    for g in (x_inf, x_11, x_m10, x_01):
        g[g == 0] = 1e-12

    def calc_integrals_for_grid(x_grid):
        re_evals, im_evals, reA12B_evals = evals(x_grid)
        int_re = _trapezoid(re_evals, x=x_grid.flatten(), axis=0)
        int_im = _trapezoid(im_evals, x=x_grid.flatten(), axis=0)
        int_reA12B = _trapezoid(reA12B_evals, x=x_grid.flatten(), axis=0)

        f1_0 = 2 * (int_re - int_im)
        f1T_perp = -2 * int_reA12B
        sivers_ratio = massterm * f1T_perp / f1_0
        return int_re, int_im, f1_0, f1T_perp, sivers_ratio

    res_inf = calc_integrals_for_grid(x_inf)
    res_11  = calc_integrals_for_grid(x_11)
    res_01  = calc_integrals_for_grid(x_01)
    res_m10 = calc_integrals_for_grid(x_m10)

    print_integration_latex_table(res_inf, res_11, res_m10, res_01, PL, bminfit, b2)

    # =========================================================================
    # 2. x-dependence plots
    # =========================================================================
    print("\nEvaluating Fourier transforms and applying Jackknife for Plotting...")

    x_safe = x_vals.copy()
    x_safe[x_safe == 0] = 1e-12
    re_ev, im_ev, a12_ev = evals(x_safe[:, None])   # (num_points, N_jk)

    def jk_rows(arr):
        out = np.array([Jackknife(row) for row in arr])
        return out[:, 0], out[:, 1]

    re_mean, re_err = jk_rows(re_ev)
    im_mean, im_err = jk_rows(im_ev)
    full_mean, full_err = jk_rows(2 * (re_ev - im_ev))
    reA12B_mean, reA12B_err = jk_rows(-2 * a12_ev)
    siv = (-massterm * a12_ev) / (re_ev - im_ev)
    SiverseShift_mean, SiverseShift_err = jk_rows(siv)
    xSiverseShift_mean, xSiverseShift_err = jk_rows(x_safe[:, None] * siv)

    tag = f'($P_L$={PL}, $b^2$={b2})'
    lab_re   = r'$\widetilde{A}^{[x]\mathrm{Re}}_{2B}$'
    lab_im   = r'$\widetilde{A}^{[x]\mathrm{Im}}_{2B}$'
    lab_f1   = r'$\tilde{f}_{1}^{(0)}=2\widetilde{A}^{[x]}_{2B}$'
    lab_f1T  = r'$\tilde{f}_{1T}^{\perp(1)}=-2\widetilde{A}^{[x]\mathrm{Re}}_{12B}$'

    fig, ((ax1, ax2, ax3), (ax4, ax5, ax6)) = plt.subplots(2, 3, figsize=(14, 8))

    def panel(ax, x, mean, err, color, title, ylabel):
        ax.plot(x, mean, color=color)
        ax.fill_between(x, mean - err, mean + err, color=color, alpha=0.3)
        ax.set_title(f'{title} {tag}')
        ax.set_xlabel('$x$')
        ax.set_ylabel(ylabel)
        ax.grid(True, linestyle='--', alpha=0.6)

    mask = x_vals >= 0
    panel(ax1, x_vals, re_mean, re_err, 'blue', lab_re, lab_re)
    panel(ax2, x_vals, im_mean, im_err, 'red', lab_im, lab_im)
    panel(ax3, x_vals, full_mean, full_err, 'purple', lab_f1, r'$\tilde{f}_{1}^{(0)}$')
    panel(ax4, x_vals, reA12B_mean, reA12B_err, 'green', lab_f1T, r'$\tilde{f}_{1T}^{\perp(1)}$')
    panel(ax5, x_vals[mask], SiverseShift_mean[mask], SiverseShift_err[mask], 'olive',
          r'$\langle k_{y} \rangle_{TU}$(GeV)', r'$\langle k_{y} \rangle_{TU}$(GeV)')
    panel(ax6, x_vals[mask], xSiverseShift_mean[mask], xSiverseShift_err[mask], 'olive',
          r'$x\langle k_{y} \rangle_{TU}$(GeV)', r'$x\langle k_{y} \rangle_{TU}$(GeV)')

    plt.tight_layout()
    file_name = f"FT_xdep_A2B_A12B_bmin{bminfit}_eta{etamin}{etamax}_b2-{b2}_PL{PL}.pdf"
    plt.savefig(file_name, format='pdf', bbox_inches='tight')
    plt.show()

    return

# ===== notebook cell 1 =====
b2 = 9
PL = -1
bminfit = 3
etamin = 6
etamax = 10
#sivers_TMD_PhD_project/save_h5_A12B_A2B/SimultaniousFit/FitParams_SimulFit_f_A2BRe_cetasq_A2BIm_A12BRe_bmin3_eta610_PL-4.h5
fitted_params, chi2_dof_list = load_params_from_h5(f"/Users/hariprashadravikumar/sivers_TMD_PhD_project/save_h5_A12B_A2B/SimultaniousFit/FitParams_SimulFit_f_A2BRe_cetasq_A2BIm_A12BRe_bmin{bminfit}_eta{etamin}{etamax}_PL{PL}.h5")
plot_fourier_transforms_A2B_A12B(fitted_params, chi2_dof_list, b2, PL, bminfit, etamin, etamax)

# ===== notebook cell 2 =====
b2 = 9
PL = -2
bminfit = 3
etamin = 6
etamax = 10
fitted_params, chi2_dof_list = load_params_from_h5(f"/Users/hariprashadravikumar/sivers_TMD_PhD_project/save_h5_A12B_A2B/SimultaniousFit/FitParams_SimulFit_f_A2BRe_cetasq_A2BIm_A12BRe_bmin{bminfit}_eta{etamin}{etamax}_PL{PL}.h5")
plot_fourier_transforms_A2B_A12B(fitted_params, chi2_dof_list, b2, PL, bminfit, etamin, etamax)

# ===== notebook cell 3 =====
b2 = 9
PL = -3
bminfit = 3
etamin = 6
etamax = 10
fitted_params, chi2_dof_list = load_params_from_h5(f"/Users/hariprashadravikumar/sivers_TMD_PhD_project/save_h5_A12B_A2B/SimultaniousFit/FitParams_SimulFit_f_A2BRe_cetasq_A2BIm_A12BRe_bmin{bminfit}_eta{etamin}{etamax}_PL{PL}.h5")
plot_fourier_transforms_A2B_A12B(fitted_params, chi2_dof_list, b2, PL, bminfit, etamin, etamax)

# ===== notebook cell 4 =====
b2 = 9
PL = -4
bminfit = 3
etamin = 6
etamax = 10
fitted_params, chi2_dof_list = load_params_from_h5(f"/Users/hariprashadravikumar/sivers_TMD_PhD_project/save_h5_A12B_A2B/SimultaniousFit/FitParams_SimulFit_f_A2BRe_cetasq_A2BIm_A12BRe_bmin{bminfit}_eta{etamin}{etamax}_PL{PL}.h5")
plot_fourier_transforms_A2B_A12B(fitted_params, chi2_dof_list, b2, PL, bminfit, etamin, etamax)
