#!/opt/homebrew/anaconda3/bin/python
"""Amplitude data panels (one PDF each): 3D (eta, b_L, A coloured by b_T, as in the thesis) and the eta=8 slice (A vs b_L coloured by b_T).
Data and jackknife as in Plot_Amps.py (jackknife over all samples). Usage: paper_amps.py [--pl 1 2 3 4] [--amps ReA2B ...]"""
import os, sys, argparse
import numpy as np, h5py
import matplotlib.pyplot as plt
from matplotlib import cm, colors as mc
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paper_style as ps

ROOT = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project"
H5 = f"{ROOT}/save_h5_A12B_A2B"
OUT = f"{ROOT}/python_fits/paper_figs/out/amps"
AMPL = {"ReA2B": r"$\tilde A^{\mathrm{Re}}_{2B}$", "ImA2B": r"$\tilde A^{\mathrm{Im}}_{2B}$", "ReA12B": r"$\tilde A^{\mathrm{Re}}_{12B}$", "ImA12B": r"$\tilde A^{\mathrm{Im}}_{12B}$"}
LETTER = {"ReA2B": "(a)", "ImA2B": "(b)", "ReA12B": "(c)", "ImA12B": "(d)"}
# appendix figures for P_L=-3,-4 are laid out as rows = amplitude, columns = (P_L=-3, P_L=-4); ImA12B has its own figure (3D row, then 2D row)
def tag(amp, pl, kind):
    if pl in (3, 4):
        if amp == "ImA12B": return "(" + "abcd"[(0 if kind == "3d" else 2) + (pl - 3)] + ")"
        return "(" + "abcdef"[2 * ["ReA2B", "ImA2B", "ReA12B"].index(amp) + (pl - 3)] + ")"
    return LETTER[amp]


def load(amp, pl):
    d = np.array(h5py.File(f"{H5}/{amp}_PL-{pl}_jackknife_data.h5", "r")["Dataset1"])
    eta, bL, bT, S = d[:, 0], d[:, 1], d[:, 2], d[:, 3:]
    n = S.shape[1]; m = S.mean(1); e = np.sqrt((n - 1) / n * ((S - m[:, None]) ** 2).sum(1))
    return dict(eta=eta, bL=bL, bT=bT, mean=m, err=e)


def cbar_bt(fig, bts, rect):
    cmap = plt.cm.viridis
    cols = cmap(np.linspace(0.0, 0.95, len(bts)))
    cm_ = mc.ListedColormap(cols)
    norm = mc.BoundaryNorm(np.append(bts, bts[-1] + 1) - 0.5, cm_.N)
    cax = fig.add_axes(rect)
    cb = fig.colorbar(cm.ScalarMappable(norm=norm, cmap=cm_), cax=cax, ticks=bts[bts % 2 == 0] if len(bts) > 9 else bts)
    cb.ax.set_title(r"$b_T/a$", fontsize=9, pad=3); cb.ax.tick_params(labelsize=8, length=2)
    return {b: cols[i] for i, b in enumerate(bts)}


def panel3d(amp, pl):
    D = load(amp, pl); fig = plt.figure(figsize=(ps.W, ps.H)); ps.apply()
    bts = np.unique(D["bT"]); ax = fig.add_axes([-0.04, 0.0, 0.80, 1.0], projection="3d")
    cmap = cbar_bt(fig, bts, [0.90, 0.20, 0.028, 0.56])
    for b in bts:
        m = D["bT"] == b
        ax.scatter(D["eta"][m], D["bL"][m], D["mean"][m], color=cmap[b], s=9, edgecolors="k", linewidths=0.2, depthshade=False)
        for x_, y_, z_, e_ in zip(D["eta"][m], D["bL"][m], D["mean"][m], D["err"][m]):
            ax.plot([x_, x_], [y_, y_], [z_ - e_, z_ + e_], color=cmap[b], lw=0.6, alpha=0.6)
    ax.set_xlabel(r"$\eta|v|/a$", fontsize=8.5, labelpad=-2); ax.set_ylabel(r"$b_L/a$", fontsize=8.5, labelpad=-2)
    ax.set_zlabel(AMPL[amp], fontsize=9, labelpad=-6)
    ax.tick_params(labelsize=7, pad=-3); ax.view_init(elev=20, azim=-50)
    ax.set_box_aspect((1, 1.05, 0.8), zoom=1.0)
    ps.tag(fig, tag(amp, pl, "3d"))
    ps.save(fig, f"{OUT}/amp3d_{amp}_PL{pl}.pdf")


def panel2d(amp, pl, eta=8):
    D = load(amp, pl); fig, ax = ps.new_panel(); ax.set_position([0.185, 0.175, 0.64, 0.70]); ps.tag(fig, tag(amp, pl, "2d"))
    sel = np.isclose(D["eta"], eta); bts = np.unique(D["bT"][sel])
    cmap = cbar_bt(fig, bts, [0.875, 0.175, 0.03, 0.70])
    for b in bts:
        m = sel & (D["bT"] == b)
        ax.errorbar(D["bL"][m], D["mean"][m], D["err"][m], fmt="o", color=cmap[b], ms=3.2, mec="k", mew=0.2, elinewidth=0.8, capsize=1.5)
    ax.set_xlabel(r"$b_L/a$"); ax.set_ylabel(AMPL[amp], fontsize=10)
    ps.save(fig, f"{OUT}/amp2d_eta{eta}_{amp}_PL{pl}.pdf")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(); ap.add_argument("--pl", type=int, nargs="*", default=[1, 2, 3, 4]); ap.add_argument("--amps", nargs="*", default=list(AMPL)); a = ap.parse_args()
    os.makedirs(OUT, exist_ok=True)
    for pl in a.pl:
        for amp in a.amps:
            panel3d(amp, pl); panel2d(amp, pl)
        print("PL", pl, "done")
