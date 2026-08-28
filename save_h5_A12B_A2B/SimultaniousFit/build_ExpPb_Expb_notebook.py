#!/usr/bin/env python3
"""Generates SimultaneousFit_ExpPb_Expb_fromh5.ipynb, mirroring the reference
   SimultaneousFit_A12bA2B_fromh5.ipynb one-to-one in structure.
   The FT uses the same 1/(2pi) normalization as Mathematica FourierParameters->{0,1}.
"""
import json, os

# ─── Cell 0 source ────────────────────────────────────────────────────────────
CELL0 = r"""import h5py
import numpy as np
import math
import matplotlib
import matplotlib.pyplot as plt
from IPython.display import display, Markdown

# ── Jackknife (scalar version, one sample at a time — same as reference) ──────
def Jackknife(datalist):
    N = len(datalist)
    theta_bar = np.mean(datalist)
    sq = [(datalist[i] - theta_bar)**2 for i in range(N)]
    sigma_sq = ((N - 1) / N) * np.sum(sq)
    return theta_bar, np.sqrt(sigma_sq)

# ── Compact error formatter ───────────────────────────────────────────────────
def fmt_err(mean, err):
    if err <= 0:
        return f"{mean}"
    if mean and (abs(mean) < 1e-3 or abs(mean) >= 1e3):
        exp = int(math.floor(math.log10(abs(mean))))
        ms  = mean / 10**exp;  es = err / 10**exp
        pl  = int(math.floor(math.log10(abs(es))))
        nd  = max(0, -(pl - 1))
        return f"{ms:.{nd}f}({int(round(es*10**nd))})e{exp}"
    else:
        pl = int(math.floor(math.log10(abs(err))))
        nd = max(0, -(pl - 1))
        return f"{mean:.{nd}f}({int(round(err*10**nd))})"

# ── H5 loader ─────────────────────────────────────────────────────────────────
def load_params_from_h5(filename):
    fitted_params = {}
    with h5py.File(filename, "r") as f:
        for key in f["jackknife_samples"].keys():
            fitted_params[key] = f["jackknife_samples"][key][:]
        chi2_dof_list = f["chi2_dof"][:]
    return fitted_params, chi2_dof_list

# ── LaTeX / Markdown parameter table ─────────────────────────────────────────
def print_latex_table(fitted_params, chi2_dof_list, PL, bmin, etamin, etamax):
    res = {k: fmt_err(*Jackknife(v)) for k, v in fitted_params.items()}
    chi2_str = fmt_err(*Jackknife(chi2_dof_list))

    re_params   = ['a_re',     'c_re',     'd_re',     'k1_re', 'k2_re', 'f']
    im_params   = ['a_im',     'c_im',     'd_im',     'f']
    a12b_params = ['a_reA12B', 'c_reA12B', 'd_reA12B', 'f']

    vals_re   = ", ".join(res[p] for p in re_params   if p in res)
    vals_im   = ", ".join(res[p] for p in im_params   if p in res)
    vals_a12b = ", ".join(res[p] for p in a12b_params if p in res)

    eq_re   = (r"$a\,e^{-f\eta}"
               r"\exp\bigl(-c(1-k_1/\eta-k_2/\eta^2)\lvert b_LP_L\rvert-d\lvert b\rvert\bigr)$")
    eq_im   = r"$a\,(b_LP_L)\,e^{-f\eta}\exp\bigl(-c\lvert b_LP_L\rvert-d\lvert b\rvert\bigr)$"
    eq_a12b = r"$-a\,e^{-f\eta}\exp\bigl(-c\lvert b_LP_L\rvert-d\lvert b\rvert\bigr)$"

    names_re   = r"$\{a,c,d,k_1,k_2,f\}$"
    names_im   = r"$\{a,c,d,f\}$"
    names_a12b = r"$\{a,c,d,f\}$"

    md  = f"\n### ExpPb\\_Expb Simultaneous Fit (common $f$)\n"
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

# ── Main FT + integration table + 6-panel plot ───────────────────────────────
def plot_fourier_transforms_A2B_A12B(fitted_params, chi2_dof_list, b2, PL,
                                      bminfit, etamin, etamax, num_points=200):
    # One-to-one mirror of SimultaneousFit_A12bA2B_fromh5 reference notebook.
    # FT normalization (Mathematica FourierParameters -> {0,1}):
    #   f~(x) = 1/(2pi) * Integral A(lambda)*exp(i*x*lambda) d(lambda)
    # Physical amplitudes (stripping shared exp(-f*eta)):
    #   ReA2B_phys  = a_re *  exp(-c_re*|lam| - d_re*b_mag(lam))
    #   ImA2B_phys  = a_im * (-lam) * exp(-c_im*|lam| - d_im*b_mag)
    #   ReA12B_phys = -a_12B * exp(-c_12B*|lam| - d_12B*b_mag(lam))
    # where lam = b*P and b_mag = sqrt(bT^2 + (lam/PL)^2) at fixed bT^2=b2.
    # Parseval: int_{-inf}^{inf} f~(x) dx = A(lambda=0)  (exact).
    print_latex_table(fitted_params, chi2_dof_list, PL, bminfit, etamin, etamax)

    x_vals = np.linspace(-1, 1, num_points)

    MassN    = 0.6228
    lata     = 0.11403
    massterm = MassN * (197.0 * 0.001 / lata)

    bT = np.sqrt(b2)   # fixed transverse |b|

    # ── Parameter extraction with physical rescaling ──────────────────────────
    # Fit exponent: c_fit * |bL*PL| = c_fit * |lambda|
    # Cell 4 convention:  c_phys = c_fit / PL^2  so that
    #   c_phys * |lambda| maps correctly to the fit convention via bL = lambda/PL.
    a_re  = np.array(fitted_params['a_re'])
    c_re  = np.array(fitted_params['c_re'])  / (PL**2)
    d_re  = np.array(fitted_params['d_re'])

    a_im  = np.array(fitted_params['a_im'])  / PL
    c_im  = np.array(fitted_params['c_im'])  / (PL**2)
    d_im  = np.array(fitted_params['d_im'])

    a_reA12B = np.array(fitted_params['a_reA12B'])
    c_reA12B = np.array(fitted_params['c_reA12B']) / (PL**2)
    d_reA12B = np.array(fitted_params['d_reA12B'])

    # ── Lambda grid (lambda = bL * PL = b*P) ─────────────────────────────────
    lam_grid = np.linspace(-40, 40, 4000)
    lam      = lam_grid[:, None]            # (4000, 1) — broadcasts over N_jk
    abs_lam  = np.abs(lam)
    b_mag    = np.sqrt(bT**2 + (lam / PL)**2)  # (4000, 1)

    # Physical amplitude tensors — shape (4000, N_jk) via broadcasting
    re_lam   = a_re   * np.exp(-c_re   * abs_lam - d_re   * b_mag)
    im_lam   = a_im   * (-lam) * np.exp(-c_im   * abs_lam - d_im   * b_mag)
    a12b_lam = -a_reA12B * np.exp(-c_reA12B * abs_lam - d_reA12B * b_mag)

    # =========================================================================
    # Integration table
    # =========================================================================
    print("\nComputing Numerical Integrals across Jackknife samples...")

    # {-inf, +inf}:
    #   By Parseval, int_{-inf}^{inf} f~(x) dx = A(lambda=0)  (exact, no 2pi factor)
    idx0         = len(lam_grid) // 2       # index of lambda = 0
    int_inf_re   = re_lam[idx0, :]          # (N_jk,)
    int_inf_im   = im_lam[idx0, :]          # ~0 (odd amplitude at lambda=0)
    int_inf_a12b = a12b_lam[idx0, :]        # (N_jk,)

    # Compute f~(x) on a 1000-point x-grid for finite-range integration
    x_fine = np.linspace(-1, 1, 1000)
    re_xf, im_xf, a12b_xf = [], [], []
    for xf in x_fine:
        cxl = np.cos(xf * lam)
        sxl = np.sin(xf * lam)
        re_xf.append(   np.trapz(cxl * re_lam,    x=lam_grid, axis=0) / (2*np.pi))
        im_xf.append(   np.trapz(sxl * im_lam,    x=lam_grid, axis=0) / (2*np.pi))
        a12b_xf.append( np.trapz(cxl * a12b_lam,  x=lam_grid, axis=0) / (2*np.pi))

    re_xf   = np.array(re_xf).T    # (N_jk, 1000)
    im_xf   = np.array(im_xf).T
    a12b_xf = np.array(a12b_xf).T

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

    md_int  = "\n### Numerical Integration of Fourier Transforms\n\n"
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
    # Plotting: Jackknife per x point (same structure as reference notebook)
    # =========================================================================
    re_mean,     re_err     = [], []
    im_mean,     im_err     = [], []
    full_mean,   full_err   = [], []
    reA12B_mean, reA12B_err = [], []
    SivShift_mean,  SivShift_err  = [], []
    xSivShift_mean, xSivShift_err = [], []

    print("\nEvaluating Fourier transforms and applying Jackknife for plotting...")

    for x in x_vals:
        xs  = x if x != 0 else 1e-12
        cxl = np.cos(xs * lam)
        sxl = np.sin(xs * lam)

        re_at   = np.trapz(cxl * re_lam,    x=lam_grid, axis=0) / (2*np.pi)
        im_at   = np.trapz(sxl * im_lam,    x=lam_grid, axis=0) / (2*np.pi)
        a12b_at = np.trapz(cxl * a12b_lam,  x=lam_grid, axis=0) / (2*np.pi)

        m_re,   e_re   = Jackknife(re_at)
        m_im,   e_im   = Jackknife(im_at)
        m_full, e_full = Jackknife(2*(re_at - im_at))
        m_a12b, e_a12b = Jackknife(-2*a12b_at)
        m_ss,   e_ss   = Jackknife((-massterm * a12b_at) / (re_at - im_at))
        m_xss,  e_xss  = Jackknife(xs * (-massterm * a12b_at) / (re_at - im_at))

        re_mean.append(m_re);      re_err.append(e_re)
        im_mean.append(m_im);      im_err.append(e_im)
        full_mean.append(m_full);  full_err.append(e_full)
        reA12B_mean.append(m_a12b); reA12B_err.append(e_a12b)
        SivShift_mean.append(m_ss);   SivShift_err.append(e_ss)
        xSivShift_mean.append(m_xss); xSivShift_err.append(e_xss)

    re_mean,     re_err     = np.array(re_mean),     np.array(re_err)
    im_mean,     im_err     = np.array(im_mean),     np.array(im_err)
    full_mean,   full_err   = np.array(full_mean),   np.array(full_err)
    reA12B_mean, reA12B_err = np.array(reA12B_mean), np.array(reA12B_err)
    SivShift_mean,  SivShift_err  = np.array(SivShift_mean),  np.array(SivShift_err)
    xSivShift_mean, xSivShift_err = np.array(xSivShift_mean), np.array(xSivShift_err)

    # 4. Plotting — 6-panel layout identical to reference
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
"""

# ─── Helper to make h5 path ────────────────────────────────────────────────────
H5_BASE = ("/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD"
           "/sivers_TMD_PhD_project/save_h5_A12B_A2B/h5data")

def param_cell(b2, PL, bminfit=3, etamin=6, etamax=10):
    return (
        f"b2      = {b2}\n"
        f"PL      = {PL}\n"
        f"bminfit = {bminfit}\n"
        f"etamin  = {etamin}\n"
        f"etamax  = {etamax}\n"
        f"\n"
        f"fitted_params, chi2_dof_list = load_params_from_h5(\n"
        f'    f"{H5_BASE}/FitParams_SimulFit_ExpPb_Expb'
        f'_bmin{{bminfit}}_eta{{etamin}}{{etamax}}_PL{{PL}}.h5")\n'
        f"\n"
        f"plot_fourier_transforms_A2B_A12B(\n"
        f"    fitted_params, chi2_dof_list, b2, PL, bminfit, etamin, etamax)\n"
    )

# ─── Build notebook dict ───────────────────────────────────────────────────────
def make_code_cell(source):
    return {
        "cell_type": "code",
        "execution_count": None,
        "metadata": {},
        "outputs": [],
        "source": source
    }

nb = {
    "cells": [
        make_code_cell(CELL0),
        make_code_cell(param_cell(b2=9,  PL=-1)),
        make_code_cell(param_cell(b2=50, PL=-1)),
        make_code_cell(param_cell(b2=9,  PL=-2)),
        make_code_cell(param_cell(b2=9,  PL=-3)),
        make_code_cell(param_cell(b2=9,  PL=-4)),
        make_code_cell(param_cell(b2=36, PL=-4)),
    ],
    "metadata": {
        "kernelspec": {
            "display_name": "Python 3 (ipykernel)",
            "language": "python",
            "name": "python3"
        },
        "language_info": {
            "name": "python",
            "version": "3.9.0"
        }
    },
    "nbformat": 4,
    "nbformat_minor": 5
}

out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                   "SimultaneousFit_ExpPb_Expb_fromh5.ipynb")

with open(out, "w") as f:
    json.dump(nb, f, indent=1, ensure_ascii=False)

print(f"Written: {out}")
print(f"Cells: {len(nb['cells'])}")
