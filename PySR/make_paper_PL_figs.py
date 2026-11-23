#!/opt/homebrew/anaconda3/bin/python
"""Paper figures/numbers for the PySR/Gaussian/short-distance part of the fitting section at a chosen P_L.
Usage: make_paper_PL_figs.py --pl 2
Writes PDFs to PySR/paper_PL<pl>/ and prints every number quoted in the text."""
import argparse, os, h5py, numpy as np
import matplotlib; matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy.optimize import curve_fit

ap = argparse.ArgumentParser(); ap.add_argument("--pl", type=int, default=2); a = ap.parse_args()
PL = a.pl
ROOT = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project"
OUT = f"{ROOT}/PySR/paper_PL{PL}"; os.makedirs(OUT, exist_ok=True)
f = h5py.File(f"{ROOT}/save_h5_A12B_A2B/eta_bL_bT_Amp_Re_Im_err.h5", "r")
ld = lambda amp, e: np.array(f[f"Pl-{PL}/eta_{e}_bL_bT_{amp}_err"])
plt.rcParams.update({"font.size": 12, "axes.labelsize": 14})

# ---------- Gaussian profile (single eta=8 slice, all |b|, as in the PL=-1 paper figure) ----------
def gau(X, g, al, be): bL, bT = X; return g*np.exp(-al*bL**2 - be*bT**2)
print(f"=== PL={PL}: Gaussian fits at eta=8, all b (66 pts) ===")
for amp, p0 in (("ReA2B", [0.4, .1, .1]), ("ReA12B", [-.03, .05, .05])):
    d = ld(amp, 8)
    p, c = curve_fit(gau, (d[:, 1], d[:, 2]), d[:, 3], sigma=d[:, 4], absolute_sigma=True, p0=p0, maxfev=20000)
    chi = (((d[:, 3]-gau((d[:, 1], d[:, 2]), *p))/d[:, 4])**2).sum()/(len(d)-3)
    print(f"{amp}: gamma,alpha,beta={p}  alpha-beta={p[1]-p[2]:.4f}({np.sqrt(c[1,1]+c[2,2]-2*c[1,2]):.4f}) chi2/dof={chi:.1f}")
    if amp == "ReA2B": pg, dg = p, d
fig, ax = plt.subplots(figsize=(7, 4))
bLc = np.linspace(-8.5, 8.5, 300)
for i, bt in enumerate(sorted(set(np.abs(dg[:, 2])))):
    col = plt.cm.tab10(i % 10)
    m = np.abs(dg[:, 2]) == bt
    ax.errorbar(dg[m, 1], dg[m, 3], dg[m, 4], fmt="o", ms=3, color=col, label=rf"$|b_T|={int(bt)}$")
    ax.plot(bLc, gau((bLc, bt), *pg), color=col, lw=1)
ax.set_xlabel(r"$b_L/a$"); ax.set_ylabel(r"$\tilde A^{\rm Re}_{2B}$")
ax.set_title(rf"$P_L={-PL}$, $\eta=8$"); ax.legend(ncol=2, fontsize=8, frameon=False)
fig.tight_layout(); fig.savefig(f"{OUT}/gaussian_fail_A2B_PL{PL}.pdf"); plt.close()

# ---------- Short distance (eta=9) ----------
d = ld("ReA2B", 9)
bsq = np.rint(d[:, 1]**2 + d[:, 2]**2).astype(int)
x = PL*d[:, 1]  # (P.b) L/(2pi) = PL*bL, same convention as the PL=-1 figure
fig, axs = plt.subplots(1, 2, figsize=(13, 4))
for ax, sel, title in ((axs[0], bsq < 9, r"$|b|<3a$"), (axs[1], bsq >= 9, r"$|b|\geq3a$")):
    cm = plt.cm.gist_rainbow
    levels = sorted(set(bsq[sel]))
    for k, bb in enumerate(levels):
        xs, ys, es = [], [], []
        for xv in sorted(set(x[sel & (bsq == bb)])):
            m = sel & (bsq == bb) & (x == xv)
            xs.append(xv); ys.append(d[m, 3].mean()); es.append(np.sqrt((d[m, 4]**2).sum())/m.sum())
        ax.errorbar(xs, ys, es, fmt="o-", ms=6, lw=1, color=cm(k/max(len(levels)-1, 1)*0.85), label=rf"$b^2/a^2={bb}$")
    ax.set_yscale("log"); ax.set_title(title); ax.grid(True, which="both", ls="--", alpha=.3)
    ax.set_xlabel(r"$(P\cdot b)\cdot\hat L/(2\pi)$"); ax.set_ylabel(r"$\tilde A^{\rm Re}_{2B}$")
    ax.legend(ncol=2 if sel is bsq >= 9 else 1, fontsize=9, frameon=False, loc="center left", bbox_to_anchor=(1, .5))
fig.tight_layout(); fig.savefig(f"{OUT}/short_distance_PL{PL}.pdf"); plt.close()
print(f"=== PL={PL}: short-distance, eta=9, relative change across P.b at fixed b^2 ===")
for bb in (5, 20, 45):
    xs, ys = [], []
    for xv in sorted(set(x[bsq == bb])):
        m = (bsq == bb) & (x == xv); xs.append(xv); ys.append(d[m, 3].mean())
    print(f"b^2={bb}: x={xs}  A={np.round(ys,5)}  max/min-1={max(ys)/min(ys)-1:.3f}")
# also report the first-principles variation with errors
for bb in (5, 20, 45):
    m = bsq == bb; i0 = np.argmin(abs(x[m])); print(f"  b^2={bb}: |P.b| extremes vs smallest: ", end="")
    xm = x[m]; am = d[m, 3]; em = d[m, 4]
    big = np.argmax(abs(xm)); print(f"A(|x|={abs(xm[big]):g})={am[big]:.5f}({em[big]:.5f}) vs A(|x|={abs(xm[i0]):g})={am[i0]:.5f}({em[i0]:.5f})")

# ---------- PySR models and data (b>=3a, eta 6..10) ----------
dat = np.vstack([ld("ReA2B", e) for e in range(6, 11)]); dat = dat[np.hypot(dat[:, 1], dat[:, 2]) >= 3]
eta, bL, bT, A, E = dat.T
lor = lambda x, y: 1/(1+x**2+y**2)**2
if PL == 2:
    models = {
     "C=11": (lambda n, l, t: lor(t, l)**0.7822748*(7.0341153/n)**4.122877, "-", r"$C=11$ (power $\eta^{-4.1}$)"),
     "C=13": (lambda n, l, t: lor(t/2.3932884, l/2.4880378)*9.715478/1.769082**n, "--", r"$C=13$ (exp.)"),
     "C=15": (lambda n, l, t: lor(t/4.516797, l/4.606309)**1.6135204*4.5963902/1.7676761**n, "-.", r"$C=15$ (exp.)"),
     "C=17": (lambda n, l, t: lor(l/3.9305274, t/3.852527)**1.3183862*4.1718407/1.7194582**n-0.00039604199, ":", r"$C=17$ (exp.+offset)")}
    for k, (fn, _, _) in models.items():
        r = (A-fn(eta, bL, bT))/E; print(f"{k}: chi2/dof(npar not subtracted)={ (r**2).sum()/len(A):.2f}, N={len(A)}")
    fig, axs = plt.subplots(2, 2, figsize=(10, 7.4), sharex=True); axs = axs.flatten()
    absbT = sorted(set(np.abs(bT))); bLc = np.linspace(-8.5, 8.5, 300)
    for ie, ev in enumerate((6, 7, 8, 10)):
        ax = axs[ie]; me = eta == ev
        for i, ab in enumerate(absbT):
            col = plt.cm.tab10(i)
            for s, face in ((1, col), (-1, "white")):
                m = me & (bT == s*ab)
                if m.any(): ax.errorbar(bL[m], A[m], E[m], fmt="o", color=col, mfc=face, ms=5, lw=1)
            ok = np.where(bLc**2+ab**2 >= 9, 1., np.nan)
            for fn, ls, _ in models.values(): ax.plot(bLc, ok*fn(ev, bLc, ab), ls=ls, color=col, lw=1.8)
        ax.set_title(rf"$\eta={ev}$"); ax.grid(True, ls="--", alpha=.3)
        if ie >= 2: ax.set_xlabel(r"$b_L/a$")
    fig.supylabel(r"$\tilde A^{\rm Re}_{2B}$")
    from matplotlib.lines import Line2D
    hs = [Line2D([0], [0], color="k", ls=v[1], lw=2) for v in models.values()]
    fig.legend(hs, [v[2] for v in models.values()], loc="lower center", ncol=4, frameon=False)
    fig.tight_layout(rect=[.02, .06, 1, 1]); fig.savefig(f"{OUT}/pysr_benchmark_PL{PL}.pdf"); plt.close()

# ---------- Straight-line test: Gaussian vs Lorentzian power-law, same eta factor ----------
def gb(X, Ag, c, f): n, l, t = X; return Ag*np.exp(-c*(l**2+t**2))*np.exp(-f*(n-6))
def lb(X, Ag, c, j, f): n, l, t = X; return Ag*np.exp(-f*(n-6))/(1+c*(l**2+t**2))**j
pg2, _ = curve_fit(gb, (eta, bL, bT), A, sigma=E, absolute_sigma=True, p0=[.05, .05, .5], maxfev=20000)
pl2, _ = curve_fit(lb, (eta, bL, bT), A, sigma=E, absolute_sigma=True, p0=[.05, .05, 1.5, .5], maxfev=40000)
_chi2 = {}
for nm, fn, p in (("Gaussian", gb, pg2), ("Lorentzian", lb, pl2)):
    _chi2[nm] = (((A-fn((eta,bL,bT),*p))/E)**2).sum()
    print(f"{nm}: params={p}, chi2/dof={_chi2[nm]/(len(A)-len(p)):.2f}")
print(f"Delta chi2 (Gaussian - Lorentzian, one extra parameter) = {_chi2['Gaussian']-_chi2['Lorentzian']:.1f}")
fig, axs = plt.subplots(2, 2, figsize=(11, 8), sharey=True); axs = axs.flatten(); bq = np.linspace(9, 75, 300)
for ie, ev in enumerate((6, 7, 8, 10)):
    ax = axs[ie]; m = eta == ev
    ax.errorbar(bL[m]**2+bT[m]**2, A[m], E[m], fmt="ko", ms=4, alpha=.75, label="Lattice data ($b\\geq3a$)")
    ax.plot(bq, lb((ev, np.sqrt(bq), 0), *pl2), "b-", lw=2, label=rf"Lorentzian $(1+{pl2[1]:.3f}\,b^2)^{{-{pl2[2]:.2f}}}$")
    ax.plot(bq, gb((ev, np.sqrt(bq), 0), *pg2), "r--", lw=2, label=rf"Gaussian $e^{{-{pg2[1]:.3f}\,b^2}}$")
    ax.set_yscale("log"); ax.set_title(rf"$\eta={ev}$"); ax.set_xlabel(r"$b^2/a^2$"); ax.grid(True, which="both", ls="--", alpha=.3)
    if ie == 0: ax.legend(fontsize=9)
axs[0].set_ylabel(r"$\tilde A^{\rm Re}_{2B}$"); axs[2].set_ylabel(r"$\tilde A^{\rm Re}_{2B}$")
fig.tight_layout(); fig.savefig(f"{OUT}/pysr_gauss_straight_PL{PL}.pdf"); plt.close()
