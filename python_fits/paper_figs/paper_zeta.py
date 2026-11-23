#!/opt/homebrew/anaconda3/bin/python
"""zeta-hat slice figures (single 3.4 x 2.55 in panels, thesis-style 3D ribbons): the formulas are those of SilumFitAmp_bsq_PL.ipynb cell 7
(sivers_pipeline/scripts/zeta_slices_final.py): P_L=-1 jackknife mass sample by sample, hbar c = 197.32698 MeV fm, b^2 = 9, bmin=3, eta 6..10."""
import os, sys
import numpy as np, h5py
from scipy.special import kv, gamma
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paper_style as ps

ROOT = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project"
H5 = f"{ROOT}/save_h5_A12B_A2B/TMD_fit/h5data"
OUT = f"{ROOT}/python_fits/paper_figs/out/zeta"; os.makedirs(OUT, exist_ok=True)
CACHE = f"{OUT}/zeta_curves.npz"
ZETA = {-4: 0.785756, -3: 0.539684, -2: 0.294367, -1: 0.090772}
LATA = 0.11403; B2 = 9.0
KEYS = ["ReA2B", "ImA2B", "f1", "f1T", "ky", "xky"]


def jk(a):
    n = len(a); m = a.mean(); return m, np.sqrt((n - 1) / n * np.sum((a - m) ** 2))


def compute():
    x_vals = np.linspace(-1, 1, 500)
    with h5py.File(f"{H5}/MassN_Jackknife.h5", "r") as f: M = f["PL_-1"][:]
    massterm = M * (197.32698 * 0.001 / LATA)
    out = {}
    for pl in (-1, -2, -3, -4):
        with h5py.File(f"{H5}/FitParams_SimulFit_f_A2BRe_cetasq_A2BIm_A12BRe_bmin3_eta610_PL{pl}.h5", "r") as f:
            P = {k: f["jackknife_samples"][k][:] for k in f["jackknife_samples"].keys()}
        a_re = P["a_re"] / np.sqrt(2 * np.pi); c_re = P["c_re"] / pl ** 2; j_re = P["j_re"]; d_re = 1 + P["d_re"] * B2
        a_im = P["a_im"] / (pl * np.sqrt(2 * np.pi)); c_im = P["c_im"] / pl ** 2; j_im = P["j_im"]; d_im = 1 + P["d_im"] * B2
        a_12 = -P["a_reA12B"] / np.sqrt(2 * np.pi); c_12 = P["c_reA12B"] / pl ** 2; j_12 = P["j_reA12B"]; d_12 = 1 + P["d_reA12B"] * B2
        R = {k: np.zeros((2, len(x_vals))) for k in KEYS}
        for j, x in enumerate(x_vals):
            ax_ = max(abs(x), 1e-12); sx = x if x != 0 else 1e-12
            cd = c_re / d_re
            re = 2 ** (1 - j_re) * a_re * cd ** (-0.25 - j_re / 2) * d_re ** (-j_re) / gamma(j_re) * ax_ ** (-0.5 + j_re) * kv(0.5 - j_re, ax_ / np.sqrt(cd))
            cdi = c_im / d_im
            im = 2 ** (1 - j_im) * a_im * cdi ** (0.25 * (-3 - 2 * j_im)) * d_im ** (-j_im) / gamma(j_im) * sx * ax_ ** (-1.5 + j_im) * kv(1.5 - j_im, np.sqrt(d_im / c_im) * ax_)
            cd2 = c_12 / d_12
            r12 = 2 ** (1 - j_12) * a_12 * cd2 ** (-0.25 - j_12 / 2) * d_12 ** (-j_12) / gamma(j_12) * ax_ ** (-0.5 + j_12) * kv(0.5 - j_12, ax_ / np.sqrt(cd2))
            siv = (-massterm * r12) / (re - im)
            for k, v in (("ReA2B", re), ("ImA2B", im), ("f1", 2 * (re - im)), ("f1T", -2 * r12), ("ky", siv), ("xky", sx * siv)):
                R[k][0, j], R[k][1, j] = jk(v)
        for k in KEYS: out[f"{k}_{pl}"] = R[k]
    out["x"] = x_vals
    np.savez(CACHE, **out)
    return out


ZL = dict(ReA2B=r"$\tilde A^{[x]\mathrm{Re}}_{2B}$", ImA2B=r"$\tilde A^{[x]\mathrm{Im}}_{2B}$", f1=r"$\tilde f_1^{(0)}$", f1T=r"$\tilde f_{1T}^{\perp(1)}$",
          ky=r"$\langle k_y\rangle_{TU}$ (GeV)", xky=r"$x\langle k_y\rangle_{TU}$ (GeV)")
TAG = dict(ReA2B="(a)", ImA2B="(b)", f1="(c)", f1T="(d)", ky="(a)", xky="(b)")


def panel(D, key):
    fig = plt.figure(figsize=(ps.W, ps.H)); ps.apply()
    ax = fig.add_axes([-0.02, 0.0, 0.96, 1.0], projection="3d")
    x = D["x"]; col = ps.QCOL[key]; inv = []
    mask = x >= 0 if key in ("ky", "xky") else np.ones_like(x, bool)
    order = sorted((-1, -2, -3, -4), key=lambda p: 1.0 / ZETA[p])   # ascending 1/zeta-hat; drawn at equal spacing, tick labels give 1/zeta-hat
    ypos = {p: i for i, p in enumerate(order)}
    for pl in (-1, -2, -3, -4):
        y = ypos[pl]; inv.append(y); m, e = D[f"{key}_{pl}"]
        xs, m, e = x[mask], m[mask], e[mask]
        ax.plot(xs, np.full_like(xs, y), m, color=col, lw=1.3)
        ax.add_collection3d(Poly3DCollection([list(zip(np.r_[xs, xs[::-1]], np.full(2 * len(xs), y), np.r_[m - e, (m + e)[::-1]]))], color=col, alpha=0.3))
    inv = np.array(sorted(inv))
    allz = np.concatenate([np.r_[D[f"{key}_{pl}"][0][mask] - D[f"{key}_{pl}"][1][mask], D[f"{key}_{pl}"][0][mask] + D[f"{key}_{pl}"][1][mask]] for pl in (-1, -2, -3, -4)])
    pad = 0.05 * (allz.max() - allz.min())
    ax.set_xlim(x[mask].min(), 1); ax.set_ylim(-0.4, 3.4); ax.set_zlim(allz.min() - pad, allz.max() + pad)
    ax.set_yticks(range(4)); ax.set_yticklabels([f"{1.0 / ZETA[p]:.2f}" for p in order], fontsize=7)
    ax.xaxis.set_major_locator(plt.MaxNLocator(3))
    ax.set_xlabel(r"$x$", fontsize=8.5, labelpad=-3); ax.set_ylabel(r"$1/\hat\zeta$", fontsize=8.5, labelpad=2); ax.set_zlabel(ZL[key], fontsize=9, labelpad=4)
    ax.tick_params(axis="x", labelsize=7, pad=-3); ax.tick_params(axis="z", labelsize=7, pad=-3); ax.tick_params(axis="y", pad=-3)
    ax.set_box_aspect((1, 1.5, 0.9), zoom=1.1); ax.view_init(elev=20, azim=-55)
    ps.tag(fig, TAG[key])
    ps.save(fig, f"{OUT}/zeta_{key}.pdf")


if __name__ == "__main__":
    D = dict(np.load(CACHE)) if os.path.exists(CACHE) and "--recompute" not in sys.argv else compute()
    for k in KEYS: panel(D, k)
    print("zeta panels written")
