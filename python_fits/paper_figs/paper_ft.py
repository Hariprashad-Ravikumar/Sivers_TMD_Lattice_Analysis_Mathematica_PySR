#!/opt/homebrew/anaconda3/bin/python
"""x-dependence panels (one PDF per quantity) of the Fourier transform of the simultaneous-fit amplitudes, b^2=9 a^2, P_L=-1..-4.
Numerics copied unchanged from the producer notebook (SimultaneousFit_A12bA2B_fromh5.ipynb, ft_evaluators): same formulas, jackknife over all
2903 samples, m_N = MassN_Jackknife['PL_-1'] sample by sample times hbar c / a (hbar c = 197.32698 MeV fm, a = 0.11403 fm).
Usage: paper_ft.py xdep [--pl 2]   |   paper_ft.py preview"""
import os, sys, argparse
import numpy as np, h5py
from scipy.special import kv, gamma
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paper_style as ps

ROOT = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project"
H5 = f"{ROOT}/save_h5_A12B_A2B"
OUT = f"{ROOT}/python_fits/paper_figs/out"
LATA, HBARC = 0.11403, 197.32698


def jackknife(a, axis=-1):
    a = np.asarray(a, float); a = np.moveaxis(a, axis, -1)
    n = a.shape[-1]; m = a.mean(-1)
    return m, np.sqrt((n - 1) / n * ((a - m[..., None]) ** 2).sum(-1))


def params(pl):
    with h5py.File(f"{H5}/SimultaniousFit/FitParams_SimulFit_f_A2BRe_cetasq_A2BIm_A12BRe_bmin3_eta610_PL-{pl}.h5", "r") as f:
        return {k: f["jackknife_samples"][k][:] for k in f["jackknife_samples"]}


def massterm():
    with h5py.File(f"{H5}/TMD_fit/h5data/MassN_Jackknife.h5", "r") as f:
        return f["PL_-1"][:] * (HBARC * 0.001 / LATA)


def evaluators(P, b2, PL):
    a_re = P["a_re"] / np.sqrt(2 * np.pi); c_re = P["c_re"] / PL ** 2; d_re = 1.0 + P["d_re"] * b2; j_re = P["j_re"]
    a_im = P["a_im"] / (PL * np.sqrt(2 * np.pi)); c_im = P["c_im"] / PL ** 2; d_im = 1.0 + P["d_im"] * b2; j_im = P["j_im"]
    a_A = -P["a_reA12B"] / np.sqrt(2 * np.pi); c_A = P["c_reA12B"] / PL ** 2; d_A = 1.0 + P["d_reA12B"] * b2; j_A = P["j_reA12B"]

    def ev(x):          # x: (Nx,1) -> three arrays (Nx, Njk)
        ax_ = np.abs(x)
        cd = c_re / d_re
        re = (2 ** (1 - j_re) * a_re * cd ** (-0.25 - j_re / 2) * d_re ** (-j_re)) / gamma(j_re) * ax_ ** (-0.5 + j_re) * kv(0.5 - j_re, ax_ / np.sqrt(cd))
        cdi = c_im / d_im
        im = (2 ** (1 - j_im) * a_im * cdi ** (0.25 * (-3 - 2 * j_im)) * d_im ** (-j_im)) / gamma(j_im) * x * ax_ ** (-1.5 + j_im) * kv(1.5 - j_im, np.sqrt(d_im / c_im) * ax_)
        cdA = c_A / d_A
        a12 = (2 ** (1 - j_A) * a_A * cdA ** (-0.25 - j_A / 2) * d_A ** (-j_A)) / gamma(j_A) * ax_ ** (-0.5 + j_A) * kv(0.5 - j_A, ax_ / np.sqrt(cdA))
        return re, im, a12
    return ev


def curves(pl, b2=9.0, nx=200):
    P = params(pl); mt = massterm(); ev = evaluators(P, b2, -pl)
    x = np.linspace(-1, 1, nx); x[x == 0] = 1e-12
    re, im, a12 = ev(x[:, None])
    siv = (-mt * a12) / (re - im)
    return x, dict(ReA2B=re, ImA2B=im, f1=2 * (re - im), f1T=-2 * a12, ky=siv, xky=x[:, None] * siv)


LAB = dict(ReA2B=r"$\tilde A^{[x]\mathrm{Re}}_{2B}$", ImA2B=r"$\tilde A^{[x]\mathrm{Im}}_{2B}$", f1=r"$\tilde f_1^{(0)}=2\tilde A^{[x]}_{2B}$",
           f1T=r"$\tilde f_{1T}^{\perp(1)}=-2\tilde A^{[x]\mathrm{Re}}_{12B}$", ky=r"$\langle k_y\rangle_{TU}$ (GeV)", xky=r"$x\langle k_y\rangle_{TU}$ (GeV)")


def xdep(pl):
    x, c = curves(pl)
    os.makedirs(f"{OUT}/ft_xdep", exist_ok=True)
    for i, (q, y) in enumerate(c.items()):
        m, e = jackknife(y, axis=1)
        sel = x >= 0 if q in ("ky", "xky") else np.ones_like(x, bool)
        fig, ax = ps.new_panel(f"({'ababab'[i]})")
        col = ps.QCOL[q]
        ax.plot(x[sel], m[sel], color=col)
        ax.fill_between(x[sel], (m - e)[sel], (m + e)[sel], color=col, alpha=0.25, lw=0)
        ax.set_xlabel(r"$x$"); ax.set_ylabel(LAB[q], fontsize=10); ax.set_xlim(x[sel].min(), 1.0)
        ps.save(fig, f"{OUT}/ft_xdep/xdep_PL{pl}_{q}.pdf")
        if q in ("f1", "f1T", "ky", "xky"):   # appendix 2x2 grids: tags (a)-(d) by position
            fig, ax = ps.new_panel("(" + "abcdef"[2 * {1: 0, 3: 1, 4: 2}[pl] + ("f1", "f1T", "ky", "xky").index(q) % 2] + ")")
            ax.plot(x[sel], m[sel], color=col); ax.fill_between(x[sel], (m - e)[sel], (m + e)[sel], color=col, alpha=0.25, lw=0)
            ax.set_xlabel(r"$x$"); ax.set_ylabel(LAB[q], fontsize=10); ax.set_xlim(x[sel].min(), 1.0)
            ps.save(fig, f"{OUT}/ft_xdep/xdep4_PL{pl}_{q}.pdf")
    print("written", pl)


def preview():
    """2D replacements for the 3D figures, shown to the author before they go into the paper"""
    import matplotlib.pyplot as plt
    from matplotlib import cm
    os.makedirs(f"{OUT}/preview", exist_ok=True)
    # (A) FT_xdep_3D -> heat map of <k_y>_TU(x, b^2), P_L=-2
    pl = 2; P = params(pl); mt = massterm()
    x = np.linspace(0.0, 1.0, 120); x[0] = 1e-12
    b2s = np.arange(9, 69, 1.0)
    Z = np.zeros((len(b2s), len(x)))
    for i, b2 in enumerate(b2s):
        re, im, a12 = evaluators(P, b2, -pl)(x[:, None])
        Z[i] = jackknife((-mt * a12) / (re - im), axis=1)[0]
    fig, ax = ps.new_panel("(a)")
    ax.set_position([0.185, 0.175, 0.66, 0.70])
    im_ = ax.pcolormesh(x, b2s, Z, shading="auto", cmap="viridis", rasterized=True)
    cax = fig.add_axes([0.87, 0.175, 0.03, 0.70]); cb = fig.colorbar(im_, cax=cax); cb.set_label(r"$\langle k_y\rangle_{TU}$ (GeV)", fontsize=9); cb.ax.tick_params(labelsize=8)
    ax.set_xlabel(r"$x$"); ax.set_ylabel(r"$b^2/a^2$")
    ps.save(fig, f"{OUT}/preview/prev_heatmap_ky_PL2.pdf")
    # (B) zeta-hat slices -> curves for the four momenta
    fig, ax = ps.new_panel("(b)")
    for pl in (1, 2, 3, 4):
        x_, c = curves(pl); m, e = jackknife(c["ky"], axis=1); sel = x_ >= 0
        ax.plot(x_[sel], m[sel], color=ps.PLCOL[pl], label=rf"$P_L={-pl}$")
        ax.fill_between(x_[sel], (m - e)[sel], (m + e)[sel], color=ps.PLCOL[pl], alpha=0.2, lw=0)
    ax.set_xlabel(r"$x$"); ax.set_ylabel(r"$\langle k_y\rangle_{TU}$ (GeV)"); ax.set_xlim(0, 1); ax.legend(loc="upper right")
    ps.save(fig, f"{OUT}/preview/prev_zeta_slices_ky.pdf")
    # (C),(D) amplitude data: Re A2B at P_L=-2 against b_L, coloured by b_T, at eta=8 and 10
    with h5py.File(f"{H5}/eta_bL_bT_Amp_Re_Im_err.h5", "r") as f:
        for tag, eta in (("c", 8), ("d", 10)):
            d = np.array(f[f"Pl-2/eta_{eta}_bL_bT_ReA2B_err"]); fig, ax = ps.new_panel(f"({tag})")
            ax.set_position([0.185, 0.175, 0.66, 0.70])
            bts = sorted(set(d[:, 2])); cmap = plt.cm.viridis
            for bt in bts:
                m = d[:, 2] == bt
                ax.errorbar(d[m, 1], d[m, 3], d[m, 4], fmt="o-", ms=3, lw=0.8, color=cmap(bt / max(bts)), elinewidth=0.8)
            sm = plt.cm.ScalarMappable(cmap=cmap, norm=plt.Normalize(0, max(bts))); cax = fig.add_axes([0.87, 0.175, 0.03, 0.70])
            cb = fig.colorbar(sm, cax=cax); cb.set_label(r"$b_T/a$", fontsize=9); cb.ax.tick_params(labelsize=8)
            ax.set_yscale("symlog", linthresh=1e-3); ax.set_xlabel(r"$b_L/a$"); ax.set_ylabel(r"$\tilde A^{\mathrm{Re}}_{2B}$", fontsize=10)
            ps.save(fig, f"{OUT}/preview/prev_amp_ReA2B_PL2_eta{eta}.pdf")
    print("previews written")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(); ap.add_argument("cmd"); ap.add_argument("--pl", type=int, nargs="*", default=[1, 2, 3, 4]); a = ap.parse_args()
    if a.cmd == "preview": preview()
    if a.cmd == "xdep":
        for pl in a.pl: xdep(pl)
