#!/opt/homebrew/anaconda3/bin/python
"""Factorization ratio test on the lattice data (eta|v|/a=8): T(P.b,b^2)=A(P.b,b^2)/A(P.b=4|P_L|,b^2) against b^2, B(P.b,b^2)=A(P.b,b^2)/A(P.b,b^2=18) against P.b,
for Re A2B, Im A2B, Re A12B. All numbers from factorization_ratio_test_PLscaled.py (imported, not rewritten); single panels in the shared style."""
import os, sys
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); PF = os.path.dirname(HERE)
sys.path.insert(0, PF); sys.path.insert(0, HERE)
import factorization_ratio_test_PLscaled as F
import paper_style as ps
from matplotlib.lines import Line2D
H5 = os.path.dirname(PF) + "/save_h5_A12B_A2B"
OUT = f"{HERE}/out/factdata"; os.makedirs(OUT, exist_ok=True)
AMPS = ["ReA2B", "ImA2B", "ReA12B"]; ETA = 8.0
AL = {"ReA2B": r"$\tilde A^{\mathrm{Re}}_{2B}$", "ImA2B": r"$\tilde A^{\mathrm{Im}}_{2B}$", "ReA12B": r"$\tilde A^{\mathrm{Re}}_{12B}$"}
COL = [ps.OKABE["blue"], ps.OKABE["green"], ps.OKABE["vermillion"]]


def compute(PL):
    SC = -PL; nodes, b2ref = [18, 20, 25, 32], 18
    pbs_all = {"ReA2B": [0, 3 * SC, 4 * SC], "ImA2B": [3 * SC, 4 * SC], "ReA12B": [0, 3 * SC, 4 * SC]}
    qm = {0: "quad", 3 * SC: "lin", 4 * SC: "quad"}; lin, quad = {}, {}
    for amp, pbs in pbs_all.items():
        lines = F.load_lines(f"{H5}/{amp}_PL{PL}_jackknife_data.h5", ETA, PL, include_zero=(0 in pbs))
        lin[amp] = F.grid_ratios(lines, pbs, nodes, 4 * SC, b2ref)
        quad[amp] = F.grid_ratios(lines, pbs, nodes, 4 * SC, b2ref, methods=qm)
    return lin, quad, 4 * SC, b2ref


def draw(ax, lc, qc, keyfmt, xlabel, ylabel, dx):
    off = (np.arange(len(lc)) - (len(lc) - 1) / 2) * dx
    for (key, lp), col, o in zip(lc.items(), COL, off):
        qp = qc[key]; xs = np.array([p["x"] for p in lp]) + o
        ax.errorbar(xs, [p["mean"] for p in lp], [p["err"] for p in lp], fmt="o", ms=3.5, capsize=2, color=col, elinewidth=0.8, label=keyfmt(key))
        d = [(x_, q) for x_, p, q in zip(xs, lp, qp) if not F.same_point(p, q)]
        if d:
            ax.errorbar([a for a, _ in d], [q["mean"] for _, q in d], [q["err"] for _, q in d], fmt="^", ms=4, capsize=2, color=col, mfc="white", mec=col, mew=0.9, elinewidth=0.8)
    ax.set_xticks([p["x"] for p in next(iter(lc.values()))]); ax.set_xlabel(xlabel); ax.set_ylabel(ylabel, fontsize=9)


def make(PL):
    lin, quad, pbref, b2ref = compute(PL)
    for ia, amp in enumerate(AMPS):
        lt, lb, _, _ = (lin[amp] + (0, 0)); qt, qb = quad[amp][0], quad[amp][1]
        for row, (lc, qc, kf, xl, yl) in enumerate(((lt, qt, lambda x: rf"$P\!\cdot\! b={x}$", r"$b^2/a^2$", r"$T$"), (lb, qb, lambda y: rf"$b^2={y}$", r"$P\cdot b$", r"$B$"))):
            fig, ax = ps.new_panel('(' + 'abcdef'[2 * ia + row] + ')'); ax.set_position([0.20, 0.175, 0.76, 0.70])
            draw(ax, lc, qc, kf, xl, yl, 0.4 if row == 0 else 0.12)
            ax.set_title(AL[amp], fontsize=9, pad=3)
            if PL == -2 and amp == "ReA12B" and row == 0: ax.set_ylim(-1.0, 4.0)
            h, l = ax.get_legend_handles_labels()
            h += [Line2D([], [], ls="none", marker="o", color="k", ms=3.5), Line2D([], [], ls="none", marker="^", color="k", mfc="w", ms=4, mew=0.9)]; l += ["linear", "quadratic"]
            ax.legend(h, l, loc="best", fontsize=7.5, frameon=False, handletextpad=0.3, labelspacing=0.25, borderaxespad=0.3, ncol=2, columnspacing=0.8)
            ps.save(fig, f"{OUT}/fd_PL{-PL}_{amp}_{'T' if row == 0 else 'B'}.pdf")


if __name__ == "__main__":
    for PL in (-1, -2): make(PL)
    print("fact data panels written")
