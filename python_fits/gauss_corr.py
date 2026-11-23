#!/opt/homebrew/anaconda3/bin/python
"""eta=8 Gaussian profile gamma*exp(-alpha bL^2 - beta bT^2) for Re A2B / Re A12B with the lsqfit correlated chi2/dof
(same convention as paper_fits.py: full jackknife covariance of all rows, svdcut 1e-12, per-sample fits, jackknife error).
Uses all |b| (no |b|>=3a cut), as in the paper's Gaussian-failure figure. Usage: gauss_corr.py --pl 2"""
import argparse, warnings
import numpy as np
import paper_fits as pf
ap = argparse.ArgumentParser(); ap.add_argument("--pl", type=int, default=2); PL = ap.parse_args().pl
warnings.filterwarnings("ignore")
import h5py
for amp, g0 in (("ReA2B", .4), ("ReA12B", -.03)):
    d = np.array(h5py.File(f"{pf.H5DIR}/{amp}_PL-{PL}_jackknife_data.h5", "r")["Dataset1"])
    d = d[d[:, 0] == 8]; l, t = d[:, 1], d[:, 2]; S = np.ascontiguousarray(d[:, 3:]); Ns = S.shape[1]; n = len(d)
    D = S - S.mean(1, keepdims=True); cov = (Ns-1)/Ns*(D @ D.T)
    W = pf._whiten(cov)
    gau = lambda g, a, b: g*np.exp(-a*l**2 - b*t**2)
    best = pf.best_start(lambda p: gau(*p), S[:, 0], W, [[g0, .1, .1], [g0, .05, .05], [g0, .01, .01], [g0, .1, .02]])
    def fcn(x, p): return p["g"]*np.exp(-p["a"]*l**2 - p["b"]*t**2)
    cur = dict(g=float(best.x[0]), a=float(best.x[1]), b=float(best.x[2]))
    P, C, stops = [], [], 0
    for i in range(Ns):
        f = pf.lsq_fit(fcn, S[:, i], cov, cur); P.append([f["pmean"][k] for k in "gab"]); C.append(f["chi2"]/f["dof"]); stops += (not f["stop"])
    P = np.array(P); C = np.array(C); dof = f["dof"]
    ab = P[:, 1]-P[:, 2]; m, e = pf.jackknife(ab); cm, ce = pf.jackknife(C)
    pm, pe = pf.jackknife(P)
    if amp == "ReA2B":
        import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt, os
        plt.rcParams.update({"font.size": 12, "axes.labelsize": 14})
        fig, ax = plt.subplots(figsize=(7, 4)); bLc = np.linspace(-8.5, 8.5, 300)
        for i, bt in enumerate(sorted(set(np.abs(t)))):
            col = plt.cm.tab10(i % 10); m_ = np.abs(t) == bt
            ax.errorbar(l[m_], S[m_, 0], np.sqrt(np.diag(cov))[m_], fmt="o", ms=3, color=col, label=rf"$|b_T|={int(bt)}$")
            ax.plot(bLc, pm[0]*np.exp(-pm[1]*bLc**2 - pm[2]*bt**2), color=col, lw=1)
        ax.set_xlabel(r"$b_L/a$"); ax.set_ylabel(r"$\tilde A^{\rm Re}_{2B}$"); ax.set_title(rf"$P_L=-{PL}$, $\eta=8$"); ax.legend(ncol=2, fontsize=8, frameon=False)
        out = f"{pf.ROOT}/PySR/paper_PL{PL}"; os.makedirs(out, exist_ok=True)
        fig.tight_layout(); fig.savefig(f"{out}/gaussian_fail_A2B_corr_PL{PL}.pdf"); plt.close()
    print(f"PL=-{PL} {amp}: rows={n} dof={dof} noconv={stops}  gamma={pm[0]:.4f}({pe[0]:.4f}) alpha={pm[1]:.5f}({pe[1]:.5f}) beta={pm[2]:.5f}({pe[2]:.5f})  alpha-beta={m:.4f}({e:.4f})  chi2/dof={cm:.3f}({ce:.3f})  start chi2/dof={best.cost*2/dof:.2f}")
