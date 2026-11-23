#!/opt/homebrew/anaconda3/bin/python
"""Single 3.4 x 2.55 in panels of the x-b_T factorization figures, drawn from out/factshift/*.npz (written by paper_fact_dump.py)."""
import os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paper_style as ps
HERE = os.path.dirname(os.path.abspath(__file__)); D = f"{HERE}/out/factshift"; OUT = f"{D}/panels"; os.makedirs(OUT, exist_ok=True)
WIN = ["0_1", "0.1_0.9", "0.2_0.8", "0.3_0.8"]; WCOL = [ps.OKABE[k] for k in ("blue", "vermillion", "green", "orange")]
KY = r"$\langle k_y\rangle_{TU}$"


def band(ax, x, m, e, col, ls="-", lab=None, a=0.25):
    ax.plot(x, m, ls=ls, color=col, lw=1.4, label=lab)
    ax.fill_between(x, m - e, m + e, color=col, alpha=a, lw=0)


def lab_win(w): a, b = w.split("_"); return rf"$x\in[{a},{b}]$"


def run():
    G = np.load(f"{D}/fact_gh.npz")
    fig, ax = ps.new_panel(); ax.set_position([0.20, 0.175, 0.76, 0.70])
    for w, c in zip(WIN, WCOL): band(ax, G["x_" + w], *G["g_" + w], c, lab=lab_win(w))
    ax.set_xlabel(r"$x$"); ax.set_ylabel(r"$g(x)$", fontsize=9); ax.legend(loc="best", fontsize=8, handlelength=1.6, labelspacing=0.25)
    ps.tag(fig, "(a)"); ps.save(fig, f"{OUT}/gh_g.pdf")
    fig, ax = ps.new_panel(); ax.set_position([0.20, 0.175, 0.76, 0.70])
    for w, c in zip(WIN, WCOL): band(ax, G["b_" + w], *G["h_" + w], c, lab=lab_win(w))
    ax.set_xlabel(r"$|b_T|$ (fm)"); ax.set_ylabel(r"$h(|b_T|)$ (GeV)", fontsize=9); ax.legend(loc="best", fontsize=8, handlelength=1.6, labelspacing=0.25)
    ps.tag(fig, "(b)"); ps.save(fig, f"{OUT}/gh_h.pdf")
    fig, ax = ps.new_panel(); ax.set_position([0.20, 0.175, 0.76, 0.70])
    for k, c in (("lo", ps.OKABE["blue"]), ("hi", ps.OKABE["vermillion"])):
        x = G["x_0_1"]; bt = float(G["bt_" + k])
        band(ax, x, *G["act_" + k], c, lab=rf"data, $|b_T|={bt:.2f}$ fm"); band(ax, x, *G["rec_" + k], c, ls="--", lab=rf"$g\,h$, $|b_T|={bt:.2f}$ fm", a=0.12)
    ax.set_xlabel(r"$x$"); ax.set_ylabel(KY + " (GeV)", fontsize=9); ax.legend(loc="upper right", fontsize=8, handlelength=1.6, labelspacing=0.25)
    ps.save(fig, f"{OUT}/gh_recon.pdf")
    R = np.load(f"{D}/fact_ratios.npz"); cm = [ps.OKABE[k] for k in ("blue", "vermillion", "green", "orange")]
    fig, ax = ps.new_panel(); ax.set_position([0.20, 0.175, 0.76, 0.70]); bref = float(R["bref"])
    for b2, c in zip((16, 25, 36, 49), cm): band(ax, R["x1"], *R[f"Rb_{b2}"], c, lab=rf"$|b_T|={np.sqrt(b2)*0.11403:.2f}$ fm")
    ax.set_xlabel(r"$x$"); ax.set_ylabel(r"$R_b(x)$", fontsize=9); ax.set_xlim(0, 1); ax.legend(loc="best", fontsize=8, handlelength=1.6, labelspacing=0.25); ps.save(fig, f"{OUT}/ratio_x.pdf")
    fig, ax = ps.new_panel(); ax.set_position([0.20, 0.175, 0.76, 0.70])
    for xv, c in zip((0.2, 0.4, 0.6, 0.8), cm): band(ax, R["b2"], *R[f"Rx_{xv:g}"], c, lab=rf"$x={xv}$")
    ax.set_xlabel(r"$|b_T|$ (fm)"); ax.set_ylabel(r"$R_x(|b_T|)$", fontsize=9); ax.legend(loc="best", fontsize=8, handlelength=1.6, labelspacing=0.25); ps.save(fig, f"{OUT}/ratio_bT.pdf")
    print("fact panels written", float(R["bref"]), float(R["xref"]))


if __name__ == "__main__": run()
