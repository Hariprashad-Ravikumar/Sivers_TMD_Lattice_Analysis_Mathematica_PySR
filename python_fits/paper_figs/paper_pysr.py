#!/opt/homebrew/anaconda3/bin/python
"""PySR-section panels (one PDF each, 3.4 x 2.55 in): benchmark of the PySR models against Re A2B data, Gaussian-versus-Lorentzian straight-line test,
exponential straight-line test. Same data, models and fits as PySR/make_paper_PL_figs.py and PySR/make_exp_straight_PL.py (P_L=-2)."""
import os, sys
import numpy as np, h5py
from scipy.optimize import curve_fit
import matplotlib.pyplot as plt
from matplotlib import cm, colors as mc
from matplotlib.lines import Line2D
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paper_style as ps

ROOT = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project"
OUT = f"{ROOT}/python_fits/paper_figs/out/pysr"; os.makedirs(OUT, exist_ok=True)
PL = 2
f = h5py.File(f"{ROOT}/save_h5_A12B_A2B/eta_bL_bT_Amp_Re_Im_err.h5", "r")
ld = lambda amp, e: np.array(f[f"Pl-{PL}/eta_{e}_bL_bT_{amp}_err"])
dat = np.vstack([ld("ReA2B", e) for e in range(6, 11)]); dat = dat[np.hypot(dat[:, 1], dat[:, 2]) >= 3]
eta, bL, bT, A, E = dat.T
b = np.hypot(bL, bT)
ETAS = (6, 7, 8, 10)
lor = lambda x, y: 1 / (1 + x ** 2 + y ** 2) ** 2
MODELS = {
    "C=11": (lambda n, l, t: lor(t, l) ** 0.7822748 * (7.0341153 / n) ** 4.122877, "-", r"$C=11$ ($\eta^{-4.1}$)"),
    "C=13": (lambda n, l, t: lor(t / 2.3932884, l / 2.4880378) * 9.715478 / 1.769082 ** n, "--", r"$C=13$ (exp.)"),
    "C=15": (lambda n, l, t: lor(t / 4.516797, l / 4.606309) ** 1.6135204 * 4.5963902 / 1.7676761 ** n, "-.", r"$C=15$ (exp.)"),
    "C=17": (lambda n, l, t: lor(l / 3.9305274, t / 3.852527) ** 1.3183862 * 4.1718407 / 1.7194582 ** n - 0.00039604199, ":", r"$C=17$ (exp.+offset)")}
LET = "abcd"; LET5 = "abcde"


def legend_panel(handles, name):
    fig, ax = ps.new_panel(); ax.axis("off")
    ax.legend(handles=handles, loc="center", fontsize=8, frameon=False, labelspacing=0.7, handlelength=2.8)
    ps.save(fig, f"{OUT}/{name}.pdf")


def benchmark():
    absbT = sorted(set(np.abs(bT))); cmap = plt.cm.viridis; bLc = np.linspace(-8.5, 8.5, 300)
    for ie, ev in enumerate(ETAS):
        fig, ax = ps.new_panel(f"({LET[ie]})"); ax.set_position([0.185, 0.175, 0.64, 0.70])
        me = eta == ev
        for i, ab in enumerate(absbT):
            col = cmap(ab / max(absbT))
            for sgn, face in ((1, col), (-1, "white")):
                m = me & (bT == sgn * ab)
                if m.any():
                    ax.errorbar(bL[m], A[m], E[m], fmt="o", color=col, mfc=face, ms=3, mew=0.6, elinewidth=0.7)
            ok = np.where(bLc ** 2 + ab ** 2 >= 9, 1.0, np.nan)
            for fn, ls, _ in MODELS.values():
                ax.plot(bLc, ok * fn(ev, bLc, ab), ls=ls, color=col, lw=1.0)
        ax.set_xlabel(r"$b_L/a$"); ax.set_ylabel(r"$\tilde A^{\mathrm{Re}}_{2B}$", fontsize=10); ax.text(0.97, 0.96, rf"$\eta={ev}$", transform=ax.transAxes, ha="right", va="top")
        cax = fig.add_axes([0.875, 0.175, 0.03, 0.70]); cb = fig.colorbar(cm.ScalarMappable(norm=plt.Normalize(0, max(absbT)), cmap=cmap), cax=cax)
        cb.ax.set_title(r"$|b_T|/a$", fontsize=9, pad=3); cb.ax.tick_params(labelsize=8, length=2)
        ps.save(fig, f"{OUT}/bench_eta{ev}.pdf")
    hs = [Line2D([0], [0], color="k", ls=v[1], lw=1.5, label=v[2]) for v in MODELS.values()]
    hs += [Line2D([0], [0], color="k", marker="o", ls="", ms=3.5, label=r"data, $b_T\geq0$"), Line2D([0], [0], color="k", marker="o", mfc="w", ls="", ms=3.5, label=r"data, $b_T<0$")]
    ps.apply(); fig = plt.figure(figsize=(7.0, 0.32))     # one-line legend strip, full text width
    fig.legend(handles=hs, loc="center", ncol=6, fontsize=8, frameon=False, handlelength=2.2, columnspacing=1.0, handletextpad=0.5)
    ps.save(fig, f"{OUT}/bench_legend.pdf")


def gb(X, Ag, c, f_): n, l, t = X; return Ag * np.exp(-c * (l ** 2 + t ** 2)) * np.exp(-f_ * (n - 6))
def lb(X, Ag, c, j, f_): n, l, t = X; return Ag * np.exp(-f_ * (n - 6)) / (1 + c * (l ** 2 + t ** 2)) ** j


def gauss_straight():
    pg, _ = curve_fit(gb, (eta, bL, bT), A, sigma=E, absolute_sigma=True, p0=[.05, .05, .5], maxfev=20000)
    pl_, _ = curve_fit(lb, (eta, bL, bT), A, sigma=E, absolute_sigma=True, p0=[.05, .05, 1.5, .5], maxfev=40000)
    bq = np.linspace(9, 75, 300)
    for ie, ev in enumerate(ETAS):
        fig, ax = ps.new_panel(f"({LET[ie]})"); m = eta == ev
        ax.errorbar(bL[m] ** 2 + bT[m] ** 2, A[m], E[m], fmt="o", color="k", ms=3, elinewidth=0.7)
        ax.plot(bq, lb((ev, np.sqrt(bq), 0), *pl_), color=ps.OKABE["blue"], lw=1.5)
        ax.plot(bq, gb((ev, np.sqrt(bq), 0), *pg), color=ps.OKABE["vermillion"], lw=1.5, ls="--")
        ax.set_yscale("log"); ax.set_position([0.20, 0.175, 0.76, 0.70]); ax.set_xlabel(r"$b^2/a^2$"); ax.set_ylabel(r"$\tilde A^{\mathrm{Re}}_{2B}$", fontsize=10)
        ax.text(0.97, 0.96, rf"$\eta={ev}$", transform=ax.transAxes, ha="right", va="top")
        if ie == 0:
            ax.legend(handles=[Line2D([0],[0],color="k",marker="o",ls="",ms=3,label="data"), Line2D([0],[0],color=ps.OKABE["blue"],lw=1.5,label="Lorentzian"), Line2D([0],[0],color=ps.OKABE["vermillion"],lw=1.5,ls="--",label="Gaussian")], loc="lower left", fontsize=8, frameon=False, handlelength=1.8, labelspacing=0.3)
        ps.save(fig, f"{OUT}/gauss_eta{ev}.pdf")


def e1(X, A0, c, f_): n, l, t = X; return A0 * np.exp(-c * np.hypot(l, t)) * np.exp(-f_ * n)


def exp_straight():
    pe, _ = curve_fit(e1, (eta, bL, bT), A, sigma=E, absolute_sigma=True, p0=[5, .5, .5], maxfev=200000)
    bc = np.linspace(3, 8.5, 300); c15 = MODELS["C=15"][0]
    for ie, ev in enumerate((6, 7, 8, 9, 10)):
        fig, ax = ps.new_panel(f"({LET5[ie]})"); m = eta == ev
        ax.errorbar(b[m], A[m], E[m], fmt="o", color="k", ms=3, elinewidth=0.7)
        ax.plot(bc, c15(ev, bc, 0 * bc), color=ps.OKABE["blue"], lw=1.5)
        ax.plot(bc, e1((ev, bc, 0 * bc), *pe), color=ps.OKABE["vermillion"], lw=1.5, ls="--")
        ax.set_yscale("log"); ax.set_position([0.20, 0.175, 0.76, 0.70]); ax.set_xlabel(r"$|\vec b|/a$"); ax.set_ylabel(r"$\tilde A^{\mathrm{Re}}_{2B}$", fontsize=10); ax.set_xlim(2.8, 8.5)
        ax.text(0.97, 0.96, rf"$\eta={ev}$", transform=ax.transAxes, ha="right", va="top")
        ps.save(fig, f"{OUT}/exp_eta{ev}.pdf")
    legend_panel([Line2D([0], [0], color="k", marker="o", ls="", ms=3.5, label=r"data ($|\vec b|\geq3a$)"), Line2D([0], [0], color=ps.OKABE["blue"], lw=1.5, label="PySR $C=15$"),
                  Line2D([0], [0], color=ps.OKABE["vermillion"], lw=1.5, ls="--", label=r"$e^{-c|\vec b|}e^{-f\eta}$ fit")], "exp_legend")
    print("exp fit", pe)


if __name__ == "__main__":
    benchmark(); gauss_straight(); exp_straight(); print("pysr panels written")
