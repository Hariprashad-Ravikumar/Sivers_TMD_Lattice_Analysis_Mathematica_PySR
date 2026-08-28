#!/usr/bin/env python3
"""Generates the four factorized-ansatz notebooks
   (ExpPb_Expb, ExpPb_PowerLawb, GaussianPb_Expb, GaussianPb_PowerLawb)
   using the CLOSED-FORM ANALYTICAL Fourier transform of the separable
   (Pb-part) x (b-part) amplitude models, instead of numerical lambda-grid
   integration.

FT convention: Mathematica FourierTransform default, FourierParameters -> {0,1}
    Atilde(x) = (1/sqrt(2*pi)) * Integral A(lambda) * exp(i*x*lambda) d(lambda)
This matches the convention documented in
SimultaneousFit_A12bA2B_fromh5_notebook_documentation.md (Sec. 5.1), so the
Sivers-shift ratio is convention-independent, and is exactly what Mathematica's
FourierTransform[...] returns for the Pb-part.

Closed forms used (all verified numerically against direct quadrature):

  Pb-part = Exp[-c|Pb|]            (ExpPb)
      FT[Exp[-c|lam|]](x)          =  sqrt(2/pi) * c / (c^2+x^2)
      FT[lam*Exp[-c|lam|]](x)      =  i * 2*sqrt(2/pi) * c*x / (c^2+x^2)^2

  Pb-part = Exp[-c*Pb^2]           (GaussianPb)
      FT[Exp[-c*lam^2]](x)         =  (1/sqrt(2c)) * Exp[-x^2/(4c)]
      FT[lam*Exp[-c*lam^2]](x)     =  i * x*Exp[-x^2/(4c)] / (2c)^(3/2)

The b-part (b = sqrt(b2), held fixed) is NOT Fourier transformed -- it is a
pure multiplicative envelope evaluated at the chosen b2:
      Expb:      exp(-d*b)
      PowerLawb: (1 + d*b2)^(-j)

For an odd amplitude A_Im(lam) = a*lam*PbPart(c,lam)*bPart(d,b), its FT is
purely imaginary: FT[A_Im](x) = i*M(x). We track "im_evals(x) = i*A_Im~(x)"
(a REAL quantity, matching the reference notebook's row-2 convention
"integral dx (i*ImA2B)"), so im_evals(x) = -M(x) exactly (verified numerically).

Parseval identity in the {0,1} convention:
    A(lambda=0) = (1/sqrt(2*pi)) * Integral Atilde(x) dx
 => Integral_{-inf}^{inf} Atilde(x) dx = sqrt(2*pi) * A(0)
"""
import json
import os

H5_BASE = ("/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD"
           "/sivers_TMD_PhD_project/save_h5_A12B_A2B/h5data")

PREAMBLE = r"""import h5py
import numpy as np
import math
import matplotlib
import matplotlib.pyplot as plt
from IPython.display import display, Markdown

SQRT_2PI = np.sqrt(2 * np.pi)

# -- Jackknife: generalized to arrays of shape (N_jk, ...), axis=0 -----------
def Jackknife(datalist):
    arr = np.asarray(datalist, dtype=float)
    N = arr.shape[0]
    theta_bar = arr.mean(axis=0)
    sigma_sq = ((N - 1) / N) * np.sum((arr - theta_bar) ** 2, axis=0)
    return theta_bar, np.sqrt(sigma_sq)

# -- Compact error formatter ---------------------------------------------
def fmt_err(mean, err):
    if err <= 0:
        return f"{mean}"
    if mean and (abs(mean) < 1e-3 or abs(mean) >= 1e3):
        exp = int(math.floor(math.log10(abs(mean))))
        ms = mean / 10**exp; es = err / 10**exp
        pl = int(math.floor(math.log10(abs(es))))
        nd = max(0, -(pl - 1))
        return f"{ms:.{nd}f}({int(round(es*10**nd))})e{exp}"
    else:
        pl = int(math.floor(math.log10(abs(err))))
        nd = max(0, -(pl - 1))
        return f"{mean:.{nd}f}({int(round(err*10**nd))})"

# -- H5 loader -------------------------------------------------------------
def load_params_from_h5(filename):
    fitted_params = {}
    with h5py.File(filename, "r") as f:
        for key in f["jackknife_samples"].keys():
            fitted_params[key] = f["jackknife_samples"][key][:]
        chi2_dof_list = f["chi2_dof"][:]
    return fitted_params, chi2_dof_list
"""


LATEX_TABLE_TEMPLATE = r'''
# -- LaTeX / Markdown parameter table ---------------------------------------
def print_latex_table(fitted_params, chi2_dof_list, PL, bmin, etamin, etamax):
    res = {k: fmt_err(*Jackknife(v)) for k, v in fitted_params.items()}
    chi2_str = fmt_err(*Jackknife(chi2_dof_list))

    re_params   = ['a_re', 'c_re', 'd_re', @J_RE@'k1_re', 'k2_re', 'f']
    im_params   = ['a_im', 'c_im', 'd_im', @J_IM@'f']
    a12b_params = ['a_reA12B', 'c_reA12B', 'd_reA12B', @J_A12B@'f']

    vals_re   = ", ".join(res[p] for p in re_params   if p in res)
    vals_im   = ", ".join(res[p] for p in im_params   if p in res)
    vals_a12b = ", ".join(res[p] for p in a12b_params if p in res)

    eq_re   = r"@EQ_RE@"
    eq_im   = r"@EQ_IM@"
    eq_a12b = r"@EQ_A12B@"

    names_re   = "$\\{" + ", ".join(re_params)   + "\\}$"
    names_im   = "$\\{" + ", ".join(im_params)   + "\\}$"
    names_a12b = "$\\{" + ", ".join(a12b_params) + "\\}$"

    md  = "\n### @ANSATZ@ Simultaneous Fit (common $f$)\n"
    md += f"$P_L={PL}$,&nbsp; $b_{{\\min}}\\ge{bmin}a$,&nbsp; $\\eta\\in[{etamin},{etamax}]$\n\n"
    md += f"$\\chi^2/\\text{{DoF}} = {chi2_str}$ (Global)\n\n"
    md += "| Amplitude | Model Expression | Params | Fitted Values |\n"
    md += "| :--- | :--- | :--- | :--- |\n"
    md += f"| $\\tilde{{A}}_{{2B}}^{{\\text{{Re}}}}$ | {eq_re} | {names_re} | $[{vals_re}]$ |\n"
    md += f"| $\\tilde{{A}}_{{2B}}^{{\\text{{Im}}}}$ | {eq_im} | {names_im} | $[{vals_im}]$ |\n"
    md += f"| $\\tilde{{A}}_{{12B}}^{{\\text{{Re}}}}$ | {eq_a12b} | {names_a12b} | $[{vals_a12b}]$ |\n"

    try:
        display(Markdown(md))
    except Exception:
        print(md)
'''


def latex_table_block(ansatz, eq_re, eq_im, eq_a12b, has_j):
    j_re = "'j_re', " if has_j else ""
    j_im = "'j_im', " if has_j else ""
    j_a12b = "'j_reA12B', " if has_j else ""
    return (LATEX_TABLE_TEMPLATE
            .replace("@ANSATZ@", ansatz.replace("_", "\\_"))
            .replace("@EQ_RE@", eq_re)
            .replace("@EQ_IM@", eq_im)
            .replace("@EQ_A12B@", eq_a12b)
            .replace("@J_RE@", j_re)
            .replace("@J_IM@", j_im)
            .replace("@J_A12B@", j_a12b))


MAIN_FT_TEMPLATE = r'''
# -- Main FT + integration table + 6-panel plot -----------------------------
def re_tilde(a, c, bpart, x):
    return @RE_FORMULA@

def im_evals_fn(a, c, bpart, x):
    # im_evals(x) := i * ImA2B~(x)  (real-valued; matches reference row-2 convention)
    return @IM_FORMULA@

def A_at_zero(a, c, bpart):
    return @A0_FORMULA@

def plot_fourier_transforms_A2B_A12B(fitted_params, chi2_dof_list, b2, PL,
                                      bminfit, etamin, etamax, num_points=200):
    print_latex_table(fitted_params, chi2_dof_list, PL, bminfit, etamin, etamax)

    x_vals = np.linspace(-1, 1, num_points)

    MassN    = 0.6228
    lata     = 0.11403
    massterm = MassN * (197.0 * 0.001 / lata)

    b = np.sqrt(b2)   # fixed Lorentz-invariant |b| (b^2 = bL^2 + bT^2 held fixed)

    # -- Jackknife parameter arrays, shape (N_jk,) ---------------------------
    a_re  = np.array(fitted_params['a_re'])
    c_re  = np.array(fitted_params['c_re'])
    d_re  = np.array(fitted_params['d_re'])

    a_im  = np.array(fitted_params['a_im'])
    c_im  = np.array(fitted_params['c_im'])
    d_im  = np.array(fitted_params['d_im'])

    a_reA12B = -np.array(fitted_params['a_reA12B'])   # sign flip already in the model
    c_reA12B =  np.array(fitted_params['c_reA12B'])
    d_reA12B =  np.array(fitted_params['d_reA12B'])
@PARAM_EXTRA@

@BPART_LINES@

    # =========================================================================
    # Integration table (all rows fully analytic; only the finite x-ranges
    # need a trivial 1D numerical integration of the closed-form curve)
    # =========================================================================
    print("\nEvaluating analytical Fourier transforms across Jackknife samples...")

    # {-inf, +inf}: exact via Parseval, Integral Atilde(x) dx = sqrt(2*pi)*A(lambda=0)
    int_inf_re   = SQRT_2PI * A_at_zero(a_re,      c_re,      bpart_re)
    int_inf_im   = np.zeros_like(a_im)                        # odd -> A_im(0) = 0
    int_inf_a12b = SQRT_2PI * A_at_zero(a_reA12B,  c_reA12B,  bpart_a12b)

    x_fine = np.linspace(-1, 1, 1000)
    re_xf   = re_tilde(a_re,      c_re,      bpart_re,   x_fine)   # (N_jk, 1000)
    im_xf   = im_evals_fn(a_im,   c_im,      bpart_im,   x_fine)
    a12b_xf = re_tilde(a_reA12B,  c_reA12B,  bpart_a12b, x_fine)

    m11  = (x_fine >= -1) & (x_fine <= 1)
    mm10 = (x_fine >= -1) & (x_fine <= 0)
    m01  = (x_fine >= 0)  & (x_fine <= 1)

    int_11_re    = np.trapz(re_xf[:,  m11],  x=x_fine[m11],  axis=1)
    int_m10_re   = np.trapz(re_xf[:,  mm10], x=x_fine[mm10], axis=1)
    int_01_re    = np.trapz(re_xf[:,  m01],  x=x_fine[m01],  axis=1)

    int_11_im    = np.trapz(im_xf[:,  m11],  x=x_fine[m11],  axis=1)
    int_m10_im   = np.trapz(im_xf[:,  mm10], x=x_fine[mm10], axis=1)
    int_01_im    = np.trapz(im_xf[:,  m01],  x=x_fine[m01],  axis=1)

    int_11_a12b  = np.trapz(a12b_xf[:, m11],  x=x_fine[m11],  axis=1)
    int_m10_a12b = np.trapz(a12b_xf[:, mm10], x=x_fine[mm10], axis=1)
    int_01_a12b  = np.trapz(a12b_xf[:, m01],  x=x_fine[m01],  axis=1)

    res_re  = [int_inf_re,   int_11_re,   int_m10_re,   int_01_re]
    res_im  = [int_inf_im,   int_11_im,   int_m10_im,   int_01_im]
    res_f1  = [2*(res_re[i] - res_im[i]) for i in range(4)]
    res_f1T = [-2*int_inf_a12b, -2*int_11_a12b, -2*int_m10_a12b, -2*int_01_a12b]
    res_siv = [massterm * res_f1T[i] / res_f1[i] for i in range(4)]

    def format_jk(data):
        m, e = Jackknife(data)
        return fmt_err(m, e)

    row1 = [format_jk(d) for d in res_re]
    row2 = [format_jk(d) for d in res_im]
    row3 = [format_jk(d) for d in res_f1]
    row4 = [format_jk(d) for d in res_f1T]
    row5 = [format_jk(d) for d in res_siv]

    md_int  = "\n### Analytical Fourier Transform Integration Table\n\n"
    md_int += "| Integral | $\\{-\\infty,\\infty\\}$ | $\\{-1,1\\}$ | $\\{-1,0\\}$ | $\\{0,1\\}$ |\n"
    md_int += "| :--- | :--- | :--- | :--- | :--- |\n"
    md_int += (f"| $\\int dx\\,\\tilde{{A}}_{{2B}}^{{\\text{{Re}}}}$ "
               f"| {row1[0]} | {row1[1]} | {row1[2]} | {row1[3]} |\n")
    md_int += (f"| $\\int dx\\,(i\\tilde{{A}}_{{2B}}^{{\\text{{Im}}}})$ "
               f"| {row2[0]} | {row2[1]} | {row2[2]} | {row2[3]} |\n")
    md_int += (f"| $\\tilde{{f}}_1^{{(0)}}=2\\int dx\\,"
               f"(\\tilde{{A}}_{{2B}}^{{\\text{{Re}}}}"
               f"-i\\tilde{{A}}_{{2B}}^{{\\text{{Im}}}})$ "
               f"| {row3[0]} | {row3[1]} | {row3[2]} | {row3[3]} |\n")
    md_int += (f"| $\\tilde{{f}}_{{1T}}^{{\\perp(1)}}=-2\\int dx\\,"
               f"\\tilde{{A}}_{{12B}}$ "
               f"| {row4[0]} | {row4[1]} | {row4[2]} | {row4[3]} |\n")
    md_int += (f"| $m_N\\dfrac{{\\tilde{{f}}_{{1T}}^{{\\perp(1)}}}}"
               f"{{\\tilde{{f}}_1^{{(0)}}}}$ "
               f"| {row5[0]} | {row5[1]} | {row5[2]} | {row5[3]} |\n")

    try:
        display(Markdown(md_int))
    except Exception:
        print(md_int)

    # =========================================================================
    # Plotting -- fully vectorized analytic evaluation over x_vals
    # =========================================================================
    re_v   = re_tilde(a_re,      c_re,      bpart_re,   x_vals)   # (N_jk, num_points)
    im_v   = im_evals_fn(a_im,   c_im,      bpart_im,   x_vals)
    a12b_v = re_tilde(a_reA12B,  c_reA12B,  bpart_a12b, x_vals)

    full_v = 2 * (re_v - im_v)
    f1T_v  = -2 * a12b_v
    siv_v  = massterm * f1T_v / full_v
    xsiv_v = x_vals[None, :] * siv_v

    re_mean,     re_err     = Jackknife(re_v)
    im_mean,     im_err     = Jackknife(im_v)
    full_mean,   full_err   = Jackknife(full_v)
    reA12B_mean, reA12B_err = Jackknife(f1T_v)
    SivShift_mean,  SivShift_err  = Jackknife(siv_v)
    xSivShift_mean, xSivShift_err = Jackknife(xsiv_v)

    fig, ((ax1, ax2, ax3), (ax4, ax5, ax6)) = plt.subplots(2, 3, figsize=(14, 8))

    ax1.plot(x_vals, re_mean, color='blue', label='ReA2B Mean')
    ax1.fill_between(x_vals, re_mean-re_err, re_mean+re_err, color='blue', alpha=0.3)
    ax1.set_title(f'$\\tilde{{A}}_{{2B}}^{{Re}}$ ($P_L$={PL}, $b^2$={b2})')
    ax1.set_xlabel('$x$'); ax1.set_ylabel('$\\tilde{A}_{2B}^{Re}$')
    ax1.grid(True, linestyle='--', alpha=0.6)

    ax2.plot(x_vals, im_mean, color='red', label='ImA2B Mean')
    ax2.fill_between(x_vals, im_mean-im_err, im_mean+im_err, color='red', alpha=0.3)
    ax2.set_title(f'$i\\tilde{{A}}_{{2B}}^{{Im}}$ ($P_L$={PL}, $b^2$={b2})')
    ax2.set_xlabel('$x$'); ax2.set_ylabel('$i\\tilde{A}_{2B}^{Im}$')
    ax2.grid(True, linestyle='--', alpha=0.6)

    ax3.plot(x_vals, full_mean, color='green', label='A2B Mean')
    ax3.fill_between(x_vals, full_mean-full_err, full_mean+full_err, color='green', alpha=0.3)
    ax3.set_title(f'$\\tilde{{f}}_{{1}}^{{(0)}}=2\\tilde{{A}}_{{2B}}$ ($P_L$={PL}, $b^2$={b2})')
    ax3.set_xlabel('$x$'); ax3.set_ylabel('$\\tilde{f}_{1}^{(0)}$')
    ax3.grid(True, linestyle='--', alpha=0.6)

    ax4.plot(x_vals, reA12B_mean, color='blue')
    ax4.fill_between(x_vals, reA12B_mean-reA12B_err, reA12B_mean+reA12B_err,
                     color='blue', alpha=0.3)
    ax4.set_title(f'$\\tilde{{f}}_{{1}}^{{\\perp(1)}}=-2\\tilde{{A}}_{{12B}}$ ($P_L$={PL}, $b^2$={b2})')
    ax4.set_xlabel('$x$'); ax4.set_ylabel('$\\tilde{f}_{1}^{\\perp(1)}$')
    ax4.grid(True, linestyle='--', alpha=0.6)

    mask = x_vals >= 0

    ax5.plot(x_vals[mask], SivShift_mean[mask], color='blue')
    ax5.fill_between(x_vals[mask],
                     SivShift_mean[mask]-SivShift_err[mask],
                     SivShift_mean[mask]+SivShift_err[mask],
                     color='blue', alpha=0.3)
    ax5.set_title(f'$\\langle k_{{y}}\\rangle_{{TU}}$ (GeV) ($P_L$={PL}, $b^2$={b2})')
    ax5.set_xlabel('$x$'); ax5.set_ylabel('$\\langle k_{y}\\rangle_{TU}$ (GeV)')
    ax5.grid(True, linestyle='--', alpha=0.6)

    ax6.plot(x_vals[mask], xSivShift_mean[mask], color='blue')
    ax6.fill_between(x_vals[mask],
                     xSivShift_mean[mask]-xSivShift_err[mask],
                     xSivShift_mean[mask]+xSivShift_err[mask],
                     color='blue', alpha=0.3)
    ax6.set_title(f'$x\\langle k_{{y}}\\rangle_{{TU}}$ (GeV) ($P_L$={PL}, $b^2$={b2})')
    ax6.set_xlabel('$x$'); ax6.set_ylabel('$x\\langle k_{y}\\rangle_{TU}$ (GeV)')
    ax6.grid(True, linestyle='--', alpha=0.6)

    plt.tight_layout()
    param_keys_str = "-".join(fitted_params.keys())
    file_name = (f"SimulFitCovMatrix-A12B-A2B-FT-{param_keys_str}"
                 f"__bmin{bminfit}_eta{etamin}{etamax}_PL{PL}.pdf")
    plt.savefig(file_name, format='pdf', bbox_inches='tight')
    plt.show()
    return
'''


def main_ft_block(pb_type, b_type):
    """pb_type: 'Exp' or 'Gaussian'; b_type: 'Exp' or 'PowerLaw'"""
    if b_type == "Exp":
        bpart_lines = ("    bpart_re    = np.exp(-d_re * b)\n"
                       "    bpart_im    = np.exp(-d_im * b)\n"
                       "    bpart_a12b  = np.exp(-d_reA12B * b)")
        param_extra = ""
    else:
        bpart_lines = ("    bpart_re    = (1.0 + d_re * b2) ** (-j_re)\n"
                       "    bpart_im    = (1.0 + d_im * b2) ** (-j_im)\n"
                       "    bpart_a12b  = (1.0 + d_reA12B * b2) ** (-j_reA12B)")
        param_extra = ("    j_re     = np.array(fitted_params['j_re'])\n"
                       "    j_im     = np.array(fitted_params['j_im'])\n"
                       "    j_reA12B = np.array(fitted_params['j_reA12B'])")

    if pb_type == "Exp":
        re_formula = "a[:, None] * bpart[:, None] * np.sqrt(2/np.pi) * c[:, None] / (c[:, None]**2 + x[None, :]**2)"
        im_formula = "-a[:, None] * bpart[:, None] * 2*np.sqrt(2/np.pi) * c[:, None] * x[None, :] / (c[:, None]**2 + x[None, :]**2)**2"
        a0_formula = "a * bpart"  # PbPart(c, 0) = exp(0) = 1
    else:
        re_formula = "a[:, None] * bpart[:, None] * (1.0/np.sqrt(2*c[:, None])) * np.exp(-x[None, :]**2 / (4*c[:, None]))"
        im_formula = "-a[:, None] * bpart[:, None] * x[None, :] * np.exp(-x[None, :]**2 / (4*c[:, None])) / (2*c[:, None])**1.5"
        a0_formula = "a * bpart"

    return (MAIN_FT_TEMPLATE
            .replace("@RE_FORMULA@", re_formula)
            .replace("@IM_FORMULA@", im_formula)
            .replace("@A0_FORMULA@", a0_formula)
            .replace("@PARAM_EXTRA@", param_extra)
            .replace("@BPART_LINES@", bpart_lines))


ANSATZE = {
    "ExpPb_Expb": dict(
        pb_type="Exp", b_type="Exp", has_j=False,
        eq_re=r"$a\,\exp(-c\lvert\mathrm{Pb}\rvert-d\lvert b\rvert)$",
        eq_im=r"$a\,\mathrm{Pb}\,\exp(-c\lvert\mathrm{Pb}\rvert-d\lvert b\rvert)$",
        eq_a12b=r"$-a\,\exp(-c\lvert\mathrm{Pb}\rvert-d\lvert b\rvert)$",
    ),
    "ExpPb_PowerLawb": dict(
        pb_type="Exp", b_type="PowerLaw", has_j=True,
        eq_re=r"$\dfrac{a\,\exp(-c\lvert\mathrm{Pb}\rvert)}{(1+d\,b^2)^{j}}$",
        eq_im=r"$\dfrac{a\,\mathrm{Pb}\,\exp(-c\lvert\mathrm{Pb}\rvert)}{(1+d\,b^2)^{j}}$",
        eq_a12b=r"$\dfrac{-a\,\exp(-c\lvert\mathrm{Pb}\rvert)}{(1+d\,b^2)^{j}}$",
    ),
    "GaussianPb_Expb": dict(
        pb_type="Gaussian", b_type="Exp", has_j=False,
        eq_re=r"$a\,\exp(-c\,\mathrm{Pb}^2-d\lvert b\rvert)$",
        eq_im=r"$a\,\mathrm{Pb}\,\exp(-c\,\mathrm{Pb}^2-d\lvert b\rvert)$",
        eq_a12b=r"$-a\,\exp(-c\,\mathrm{Pb}^2-d\lvert b\rvert)$",
    ),
    "GaussianPb_PowerLawb": dict(
        pb_type="Gaussian", b_type="PowerLaw", has_j=True,
        eq_re=r"$\dfrac{a\,\exp(-c\,\mathrm{Pb}^2)}{(1+d\,b^2)^{j}}$",
        eq_im=r"$\dfrac{a\,\mathrm{Pb}\,\exp(-c\,\mathrm{Pb}^2)}{(1+d\,b^2)^{j}}$",
        eq_a12b=r"$\dfrac{-a\,\exp(-c\,\mathrm{Pb}^2)}{(1+d\,b^2)^{j}}$",
    ),
}


def make_code_cell(source):
    return {"cell_type": "code", "execution_count": None, "metadata": {}, "outputs": [], "source": source}


def param_cell(ansatz, b2, PL, bminfit=3, etamin=6, etamax=10):
    return (
        f"b2      = {b2}\n"
        f"PL      = {PL}\n"
        f"bminfit = {bminfit}\n"
        f"etamin  = {etamin}\n"
        f"etamax  = {etamax}\n"
        f"\n"
        f"fitted_params, chi2_dof_list = load_params_from_h5(\n"
        f'    f"{H5_BASE}/FitParams_SimulFit_{ansatz}'
        f'_bmin{{bminfit}}_eta{{etamin}}{{etamax}}_PL{{PL}}.h5")\n'
        f"\n"
        f"plot_fourier_transforms_A2B_A12B(\n"
        f"    fitted_params, chi2_dof_list, b2, PL, bminfit, etamin, etamax)\n"
    )


def build_notebook(ansatz):
    cfg = ANSATZE[ansatz]
    cell0 = (
        PREAMBLE
        + latex_table_block(ansatz, cfg["eq_re"], cfg["eq_im"], cfg["eq_a12b"], cfg["has_j"])
        + main_ft_block(cfg["pb_type"], cfg["b_type"])
    )

    nb = {
        "cells": [
            make_code_cell(cell0),
            make_code_cell(param_cell(ansatz, b2=9,  PL=-1)),
            make_code_cell(param_cell(ansatz, b2=50, PL=-1)),
            make_code_cell(param_cell(ansatz, b2=9,  PL=-2)),
            make_code_cell(param_cell(ansatz, b2=9,  PL=-3)),
            make_code_cell(param_cell(ansatz, b2=9,  PL=-4)),
            make_code_cell(param_cell(ansatz, b2=36, PL=-4)),
        ],
        "metadata": {
            "kernelspec": {"display_name": "Python 3 (ipykernel)", "language": "python", "name": "python3"},
            "language_info": {"name": "python", "version": "3.9.0"},
        },
        "nbformat": 4,
        "nbformat_minor": 5,
    }

    out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        f"SimultaneousFit_{ansatz}_fromh5.ipynb")
    with open(out, "w") as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
    print(f"Written: {out}  ({len(nb['cells'])} cells)")


if __name__ == "__main__":
    for name in ANSATZE:
        build_notebook(name)
