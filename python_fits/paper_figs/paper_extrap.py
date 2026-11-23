#!/opt/homebrew/anaconda3/bin/python
"""Single 3.4 x 2.55 in panels for the zeta-hat -> infinity extrapolation: parameter extrapolations (12), extrapolated amplitudes and Sivers shift at b^2=9
(2D), Sivers shift over (x, |b_T|) (3D surfaces). Data from out/extrap/*.npz written by paper_extrap_dump.py."""
import os, sys
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paper_style as ps
HERE = os.path.dirname(os.path.abspath(__file__)); D = f"{HERE}/out/extrap"; OUT = f"{D}/panels"; os.makedirs(OUT, exist_ok=True)
LATA = 0.11403
PN = {"re": ("Re", r"\mathrm{Re}"), "im": ("Im", r"\mathrm{Im}"), "reA12B": ("12B", r"12B")}
GROUPS = [("ReA2B", "re", r"\tilde A^{\mathrm{Re}}_{2B}"), ("ImA2B", "im", r"\tilde A^{\mathrm{Im}}_{2B}"), ("ReA12B", "reA12B", r"\tilde A^{\mathrm{Re}}_{12B}")]


def plabel(kind, suf):
    sub = {"re": r"\mathrm{Re}", "im": r"\mathrm{Im}", "reA12B": r"12B,\mathrm{Re}"}[suf]
    extra = {"c": r"/P_L^2", "a": (r"/P_L" if suf == "im" else "")}.get(kind, "")
    return rf"${kind}_{{{sub}}}{extra}$"


def params():
    P = np.load(f"{D}/params.npz"); letters = "abcd"
    for gi, (gname, suf, _) in enumerate(GROUPS):
        for i, kind in enumerate("acjd"):
            key = f"{kind}_{suf}"; g = lambda n: P[f"{key}__{n}"]
            fig, ax = ps.new_panel(); ax.set_position([0.20, 0.175, 0.76, 0.70])
            ax.errorbar(g("x"), g("y"), g("e"), fmt="o", color="k", ms=3.5, elinewidth=0.8, label="data")
            ax.plot(g("px"), g("fm"), "--", color=ps.OKABE["vermillion"], lw=1.3)
            ax.fill_between(g("px"), g("fm") - g("fe"), g("fm") + g("fe"), color=ps.OKABE["vermillion"], alpha=0.3, lw=0)
            ax.errorbar([0], [float(g("c0"))], [float(g("c0e"))], fmt="s", color=ps.OKABE["blue"], ms=4, elinewidth=0.8)
            ax.set_xlim(-0.15, g("px").max() * 1.02); ax.set_xlabel(r"$1/\hat\zeta$"); ax.set_ylabel(plabel(kind, suf), fontsize=9)
            TG = "abcdef"[2 * gi + (i % 2)]; c = g("chi"); ps.tag(fig, f"({TG})"); ax.text(0.97, 0.96, rf"$\chi^2/\mathrm{{dof}}={c[0]:.1f}\pm{c[1]:.1f}$", transform=ax.transAxes, ha="right", va="top", fontsize=8)
            if gi == 0 and i < 2:
                ax.legend(handles=[Line2D([0], [0], color="k", marker="o", ls="", ms=3, label="data"),
                                   Line2D([0], [0], color=ps.OKABE["vermillion"], ls="--", lw=1.3, label=r"$p_0+p_1/\hat\zeta^2$"),
                                   Line2D([0], [0], color=ps.OKABE["blue"], marker="s", ls="", ms=4, label=r"$\hat\zeta\to\infty$")], loc="lower left", fontsize=8, frameon=False, handlelength=1.6, labelspacing=0.25)
            ps.save(fig, f"{OUT}/par_{gname}_{kind}.pdf")


YL = dict(ReA2B=r"$\tilde A^{[x]\mathrm{Re}}_{2B}$", ImA2B=r"$\tilde A^{[x]\mathrm{Im}}_{2B}$", f1=r"$\tilde f_1^{(0)}$", f1T=r"$\tilde f_{1T}^{\perp(1)}$",
          ky=r"$\langle k_y\rangle_{TU}$ (GeV)", xky=r"$x\langle k_y\rangle_{TU}$ (GeV)")


def curves():
    C = np.load(f"{D}/curves.npz"); x = C["x"]
    for k, tag in (("ReA2B", "(a)"), ("ImA2B", "(b)"), ("f1", "(c)"), ("f1T", "(d)"), ("ky", "(a)"), ("xky", "(b)")):
        fig, ax = ps.new_panel(); m, e = C[{"ReA2B":"reA2B","ImA2B":"imA2B"}.get(k,k)]; msk = x >= 0 if k in ("ky", "xky") else np.ones_like(x, bool)
        ax.plot(x[msk], m[msk], color=ps.QCOL[k], lw=1.5); ax.fill_between(x[msk], (m - e)[msk], (m + e)[msk], color=ps.QCOL[k], alpha=0.3, lw=0)
        if k in ("ImA2B",): ax.axhline(0, color="0.5", lw=0.6)
        ax.set_xlabel(r"$x$"); ax.set_ylabel(YL[k], fontsize=9); ax.set_xlim(x[msk].min(), 1)
        ps.tag(fig, tag)
        ps.save(fig, f"{OUT}/ext_{k}.pdf")


def surf3d():
    G = np.load(f"{D}/grid3d.npz"); x = G["x"]; b2 = G["b2"]; bT = np.sqrt(b2) * LATA
    msk = x >= 0; X, B = np.meshgrid(x[msk], bT)
    for k, tag in (("ky", "(a)"), ("xky", "(b)")):
        m, e = G[k][0][:, msk], G[k][1][:, msk]
        fig = plt.figure(figsize=(ps.W, ps.H)); ps.apply(); ax = fig.add_axes([-0.02, 0.07, 0.93, 0.93], projection="3d")
        col = ps.QCOL[k]
        ax.plot_surface(X, B, m, color=col, alpha=0.75, edgecolor="none", rstride=1, cstride=1)
        ax.plot_surface(X, B, m + e, color=col, alpha=0.2, edgecolor="none"); ax.plot_surface(X, B, m - e, color=col, alpha=0.2, edgecolor="none")
        ax.set_xlabel(r"$x$", fontsize=8.5, labelpad=-3); ax.set_ylabel(r"$|b_T|$ (fm)", fontsize=8.5, labelpad=-2); ax.set_zlabel(YL[k], fontsize=9, labelpad=1)
        ax.tick_params(labelsize=7, pad=-3); ax.xaxis.set_major_locator(plt.MaxNLocator(3)); ax.view_init(elev=22, azim=-55); ax.set_box_aspect((1, 1.1, 0.8), zoom=0.95)
        ps.tag(fig, tag); ps.save(fig, f"{OUT}/ext3d_{k}.pdf")


if __name__ == "__main__":
    for w in sys.argv[1:] or ["params", "curves", "surf3d"]:
        {"params": params, "curves": curves, "surf3d": surf3d}[w]()
    print("extrap panels written")
