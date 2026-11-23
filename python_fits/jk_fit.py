#!/opt/homebrew/anaconda3/bin/python
"""Python jackknife fits of Re A2B: three estimators vs the Mathematica thesis fits.

 A  diag   : diagonal weights 1/sigma^2 (sigma = jackknife error of the full-data point), refit on every jackknife sample
              (what the Mathematica NonlinearModelFit + Weights notebook does).
 B  fullcov_mean : correlated chi^2 with the full jackknife covariance, fit on the full-data mean, Hessian errors.
 C  fullcov_jk   : same correlated chi^2 (covariance fixed), refit on every jackknife sample, jackknife errors.
Usage: jk_fit.py --pl 1 [--models G1,P1 ...] [--nproc 8]
"""
import argparse, os, sys, json
import h5py, numpy as np
from scipy.optimize import least_squares
from multiprocessing import Pool

ROOT = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project"

def load(pl, bmin=3.0, e0=6, e1=10):
    d = np.array(h5py.File(f"{ROOT}/save_h5_A12B_A2B/ReA2B_PL-{pl}_jackknife_data.h5", "r")["Dataset1"])
    keep = (np.hypot(d[:, 1], d[:, 2]) >= bmin) & (d[:, 0] >= e0) & (d[:, 0] <= e1)
    d = d[keep]
    X = d[:, :3]
    y0 = d[:, 3]          # full-data value (first column)
    Y = d[:, 4:]          # jackknife samples
    N = Y.shape[1]
    ybar = Y.mean(1)
    dev = Y - ybar[:, None]
    C = (N - 1)/N*dev@dev.T
    sig = np.sqrt(np.diag(C))
    return X, y0, Y, C, sig

# ---------------- models: (npar, f(p, eta, bL, bT, PL), init, param names) ----------------
def gauss(cfun, dfun):
    def f(p, n, l, t, PL, names):
        P = dict(zip(names, p))
        c = cfun(P, n); d = dfun(P, n)
        return P["a"]*np.exp(-P["f"]*n)*np.exp(-c*(l*PL)**2 - d*(l**2 + t**2))
    return f
const = lambda k: (lambda P, n: P[k])
def power(gfun):
    def f(p, n, l, t, PL, names):
        P = dict(zip(names, p))
        c = P["c"]*gfun(P, n); d = P["d"]
        return P["a"]*np.exp(-P["f"]*n)*(1 + (d + c)*l**2 + d*t**2)**(-P["j"])
    return f

# Mathematica thesis values at PL=-1, mean(err); chi2/dof from the thesis tables
M = {}
def add(key, desc, names, f, ref, chi2):
    M[key] = dict(desc=desc, names=names, f=f, ref=ref, chi2=chi2, init=[r[0] for r in ref])
add("G1", "c, d const", ["a","c","d","f"], gauss(const("c"), const("d")),
    [(2.04,.13),(.0005,.0018),(.0578,.0016),(.5367,.0086)], 5.19673)
add("G2", "c(1-k1/eta)", ["a","c","kc1","d","f"], gauss(lambda P,n: P["c"]*(1-P["kc1"]/n), const("d")),
    [(1.48,.11),(.0397,.0089),(6.45,.29),(.0579,.0016),(.489,.011)], 4.64804)
add("G4", "c(1-k1/eta-k2/eta^2)", ["a","c","kc1","kc2","d","f"], gauss(lambda P,n: P["c"]*(1-P["kc1"]/n-P["kc2"]/n**2), const("d")),
    [(1.43,.11),(.122,.033),(11.61,.48),(-32.8,2.9),(.0579,.0016),(.483,.012)], 4.58644)
add("G5", "d(1-l1/eta)", ["a","c","d","kd1","f"], gauss(const("c"), lambda P,n: P["d"]*(1-P["kd1"]/n)),
    [(.742,.072),(.0004,.0018),(.1216,.0090),(3.41,.18),(.384,.017)], 4.08215)
add("G6", "d(1+l1/eta-l2/sqrt(eta))", ["a","c","d","kd1","kd2","f"], gauss(const("c"), lambda P,n: P["d"]*(1+P["kd1"]/n-P["kd2"]/np.sqrt(n))),
    [(.458,.065),(.0002,.0017),(.661,.097),(4.60,.19),(4.14,.10),(.311,.024)], 3.67038)
add("G7", "d(1-l1/eta-l2/eta^2)", ["a","c","d","kd1","kd2","f"], gauss(const("c"), lambda P,n: P["d"]*(1-P["kd1"]/n-P["kd2"]/n**2)),
    [(.459,.065),(.0002,.0017),(.287,.034),(8.91,.33),(-23.9,1.3),(.311,.024)], 3.66774)
add("G8", "c(1-k1/eta), d(1-l1/eta)", ["a","c","kc1","d","kd1","f"], gauss(lambda P,n: P["c"]*(1-P["kc1"]/n), lambda P,n: P["d"]*(1-P["kd1"]/n)),
    [(.737,.070),(.015,.010),(6.03,.69),(.1147,.0096),(3.23,.22),(.383,.017)], 4.04672)
add("P0", "c const", ["a","c","d","f","j"], power(lambda P,n: 1.0),
    [(2.19,.16),(.0218,.0044),(.0218,.0044),(.5382,.0088),(2.62,.33)], 24.778)
add("P1", "c(1-k1/eta)", ["a","c","d","f","k1","j"], power(lambda P,n: 1-P["k1"]/n),
    [(2.85,.30),(.078,.014),(.078,.014),(.4625,.0089),(6.60,.15),(2.16,.15)], 2.113)
add("P2", "c(1-k1/eta-k2/eta^2)", ["a","c","d","f","k1","k2","j"], power(lambda P,n: 1-P["k1"]/n-P["k2"]/n**2),
    [(4.01,.58),(.146,.051),(.094,.018),(.496,.012),(12.27,.50),(-36.2,2.8),(2.06,.14)], 1.56788)
add("P4", "c(1-k1 ln(eta)/eta)", ["a","c","d","f","k1","j"], power(lambda P,n: 1-P["k1"]*np.log(n)/n),
    [(3.90,.43),(.092,.017),(.092,.017),(.4929,.0086),(3.616,.083),(2.07,.14)], 1.66147)

def fit_one(args):
    key, y, W, p0, X, PL = args   # W: either 1/sigma (vector) or Cholesky-inverse matrix Linv
    m = M[key]; n, l, t = X.T
    if W.ndim == 1:
        res = lambda p: (y - m["f"](p, n, l, t, PL, m["names"]))*W
    else:
        res = lambda p: W@(y - m["f"](p, n, l, t, PL, m["names"]))
    r = least_squares(res, p0, method="lm", xtol=1e-12, ftol=1e-12, gtol=1e-12, max_nfev=4000)
    return r.x, 2*r.cost, r.jac

def run(pl, keys, nproc):
    X, y0, Y, C, sig = load(pl)
    n = len(y0); PL = -pl
    # exact duplicates: (bL,bT) and (-bL,bT) are stored with identical jackknife vectors
    _, uidx = np.unique(np.round(Y, 12), axis=0, return_index=True)
    u = np.sort(uidx); nu = len(u)
    Xu, y0u, Yu, Cu, sigu = X[u], y0[u], Y[u], C[np.ix_(u, u)], sig[u]
    ev = np.linalg.eigvalsh(Cu)
    print(f"PL={PL}: {n} points ({nu} unique, {n-nu} exact duplicates), {Y.shape[1]} jackknife samples")
    print(f"  covariance of the {nu} unique points: eigenvalues min={ev.min():.3e} max={ev.max():.3e} cond={ev.max()/ev.min():.2e}")
    Linv = np.linalg.inv(np.linalg.cholesky(Cu)); Cinv = np.linalg.inv(Cu)
    out = {}
    def jk(Pm):
        Nj = Pm.shape[0]; mean = Pm.mean(0); return mean, np.sqrt((Nj-1)/Nj*((Pm-mean)**2).sum(0))
    class _Serial:
        def map(self, f, jobs, chunksize=1): return [f(j) for j in jobs]
        def __enter__(self): return self
        def __exit__(self, *a): return False
    with (_Serial() if nproc == 1 else Pool(nproc)) as pool:
        for key in keys:
            m = M[key]; npar = len(m["names"]); dof, dofu = n - npar, nu - npar
            p_init = np.array(m["init"], float)
            pA, _, _ = fit_one((key, y0, 1/sig, p_init, X, PL))                 # A : 225 pts, diagonal (Mathematica)
            pAu, _, _ = fit_one((key, y0u, 1/sigu, pA, Xu, PL))                 # A': 140 unique, diagonal
            pB, _, JB = fit_one((key, y0u, Linv, pAu, Xu, PL))                  # B : 140 unique, full cov, mean
            covB = np.linalg.inv(JB.T@JB)
            F = lambda p, XX: m["f"](p, *XX.T, PL, m["names"])
            chi_d = lambda p, XX, yy, ss: (((yy - F(p, XX))/ss)**2).sum()
            chi_c = lambda p: (y0u - F(p, Xu))@Cinv@(y0u - F(p, Xu))
            Ns = Y.shape[1]
            rA  = pool.map(fit_one, [(key, Y[:, k],  1/sig,  pA,  X,  PL) for k in range(Ns)], chunksize=64)
            rAu = pool.map(fit_one, [(key, Yu[:, k], 1/sigu, pAu, Xu, PL) for k in range(Ns)], chunksize=64)
            rC  = pool.map(fit_one, [(key, Yu[:, k], Linv,   pB,  Xu, PL) for k in range(Ns)], chunksize=64)
            mA, eA = jk(np.array([r[0] for r in rA])); mAu, eAu = jk(np.array([r[0] for r in rAu])); mC, eC = jk(np.array([r[0] for r in rC]))
            out[key] = dict(names=m["names"], desc=m["desc"], ref=m["ref"], ref_chi2=m["chi2"], dof=dof, dofu=dofu,
                A=dict(p=pA, jk_mean=mA, jk_err=eA, chi2_diag=chi_d(pA, X, y0, sig)/dof),
                Au=dict(p=pAu, jk_mean=mAu, jk_err=eAu, chi2_diag=chi_d(pAu, Xu, y0u, sigu)/dofu, chi2_corr=chi_c(pAu)/dofu),
                B=dict(p=pB, hess_err=np.sqrt(np.diag(covB)), chi2_diag=chi_d(pB, Xu, y0u, sigu)/dofu, chi2_corr=chi_c(pB)/dofu),
                C=dict(jk_mean=mC, jk_err=eC))
            r = out[key]
            print(f"\n[{key}] {m['desc']}")
            print(f"  chi2/dof  Mathematica {m['chi2']:.3f} | A(225 diag) {r['A']['chi2_diag']:.3f} | A'(140 diag) {r['Au']['chi2_diag']:.3f} | "
                  f"B(140 corr) {r['B']['chi2_corr']:.3f}  [B pars, diag chi2 {r['B']['chi2_diag']:.2f}]  [A' pars, corr chi2 {r['Au']['chi2_corr']:.2f}]")
            print(f"  {'par':4s} {'Mathematica':>14s} {'A jk(225,diag)':>16s} {'Aprime jk(140)':>16s} {'B mean(Hess)':>16s} {'C jk':>14s}  | (A-M)/eM (Ap-A)/eA (B-Ap)/eAp (C-Ap)/eAp")
            for i, nm in enumerate(m["names"]):
                rm, re_ = m["ref"][i]
                print(f"  {nm:4s} {rm:8.4g}({re_:<6.2g}) {mA[i]:9.4g}({eA[i]:<6.2g}) {mAu[i]:9.4g}({eAu[i]:<6.2g}) {pB[i]:9.4g}({np.sqrt(covB[i,i]):<6.2g}) {mC[i]:8.4g}({eC[i]:<6.2g}) | {(mA[i]-rm)/re_:7.2f} {(mAu[i]-mA[i])/eA[i]:9.2f} {(pB[i]-mAu[i])/eAu[i]:9.2f} {(mC[i]-mAu[i])/eAu[i]:9.2f}")
    return out

if __name__ == "__main__":
    ap = argparse.ArgumentParser(); ap.add_argument("--pl", type=int, default=1)
    ap.add_argument("--models", default=",".join(M)); ap.add_argument("--nproc", type=int, default=8)
    a = ap.parse_args()
    res = run(a.pl, a.models.split(","), a.nproc)
    import pickle; pickle.dump(res, open(f"{ROOT}/python_fits/results_PL-{a.pl}_{a.models.replace(',','-')}.pkl", "wb"))
