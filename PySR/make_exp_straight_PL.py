#!/opt/homebrew/anaconda3/bin/python
"""Straight-line test of exp(-c|b|) for Re A2B at a chosen P_L (Appendix C of the Sivers paper).
Uses the PySR custom loss (chi2/(n-3) + 0.1*sum of squared predictions at five large-b points) so the numbers
are comparable with the PySR Pareto table. Usage: make_exp_straight_PL.py --pl 2"""
import argparse, os, csv, h5py, numpy as np
import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
from scipy.optimize import curve_fit
ap = argparse.ArgumentParser(); ap.add_argument("--pl", type=int, default=2); PL = ap.parse_args().pl
ROOT = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project"
OUT = f"{ROOT}/PySR/paper_PL{PL}"; os.makedirs(OUT, exist_ok=True)
f = h5py.File(f"{ROOT}/save_h5_A12B_A2B/eta_bL_bT_Amp_Re_Im_err.h5", "r")
d = np.vstack([np.array(f[f"Pl-{PL}/eta_{e}_bL_bT_ReA2B_err"]) for e in range(6, 11)])
d = d[np.sqrt(d[:, 1]**2 + d[:, 2]**2) >= 3.0]
eta, bL, bT, A, E = d.T; b = np.hypot(bL, bT); N = len(A)
pts = np.array([[10, 50, 1], [10, 80, 1], [10, 10, 1], [8, 20, 1], [6, 30, 2]], float)
def loss(fn, p):
    w = ((A - fn((eta, bL, bT), *p))**2 / E**2).sum() / (N - 3)
    pen = (fn((pts[:, 0], pts[:, 1], pts[:, 2]), *p)**2).sum()
    return w + 0.1*pen, w
def e1(X, A0, c, f): n, l, t = X; return A0*np.exp(-c*np.hypot(l, t))*np.exp(-f*n)
def e2(X, A0, c, f, k): return e1(X, A0, c, f) + k
res = {}
for nm, fn, p0 in (("exp", e1, [5, .5, .5]), ("exp+const", e2, [5, .5, .5, 0])):
    p, _ = curve_fit(fn, (eta, bL, bT), A, sigma=E, absolute_sigma=True, p0=p0, maxfev=200000)
    L, w = loss(fn, p); res[nm] = (fn, p); print(f"{nm}: params={p}, L={L:.3f}, wmse(chi2/(n-3))={w:.3f}, N={N}")
rows = list(csv.DictReader(open(f"{ROOT}/PySR/outputs_A2B_real_PL{PL}/hall_of_fame_summary.csv")))
print("Pareto losses:", [(r["complexity"], round(float(r["loss"]), 3)) for r in rows])
C = {"C13": "9.715478/((0.161542221770668*l**2 + 0.174586206427553*t**2 + 1)**2*1.769082**n)",
     "C15": "((0.0471296119770946*l**2 + 0.0490161115065821*t**2 + 1)**(-2))**1.6135204*4.5963902/1.7676761**n"}
def pysr(n, l, t): return eval(C["C15"])
print("C15 loss check:", loss(lambda X, *p: pysr(*X), [])[0])
fig, axs = plt.subplots(2, 2, figsize=(10, 7.4), sharex=True); axs = axs.flatten(); bc = np.linspace(3, 8.5, 300)
for i, ev in enumerate((6, 7, 8, 10)):
    ax = axs[i]; m = eta == ev
    ax.errorbar(b[m], A[m], E[m], fmt="o", color="k", ms=6, alpha=.75, elinewidth=1.3, capsize=2.5, label=r"Lattice data ($|b|\geq3a$)" if i == 0 else "", zorder=4)
    ax.plot(bc, pysr(ev, bc, 0*bc), "b-", lw=2.4, label=r"\texttt{PySR} $C=15$" if False else "PySR $C=15$ power law" if i == 0 else "", zorder=3)
    fn, p = res["exp"]
    ax.plot(bc, fn((ev, bc, 0*bc), *p), "r--", lw=2.4, label=rf"Exponential $\propto e^{{-{p[1]:.3f}|b|}}$ (straight line)" if i == 0 else "", zorder=2)
    ax.set_yscale("log"); ax.set_title(rf"$\eta={ev}$", fontsize=16); ax.grid(True, which="both", ls="--", alpha=.35); ax.set_xlim(2.8, 8.5)
    ax.tick_params(labelsize=13)
    if i >= 2: ax.set_xlabel(r"$|b|/a=\sqrt{b_L^2+b_T^2}$", fontsize=16)
fig.supylabel(r"$\tilde A_{2B}^{\rm Re}$ (log scale)", fontsize=16, x=.01)
fig.tight_layout(rect=[.02, .1, 1, 1], h_pad=1, w_pad=1.2)
fig.legend(loc="upper center", bbox_to_anchor=(.5, .09), ncol=2, frameon=False, fontsize=13)
fig.savefig(f"{OUT}/exp_straight_PL{PL}.pdf", bbox_inches="tight"); print("saved")
