#!/opt/homebrew/anaconda3/bin/python
"""Re A2B, power law with c(1-k1/eta-k2/eta^2) (model P2), PL=-2: correlated chi2/dof with all 225 rows (as in the paper tables)
versus only the independent rows (one of each +-bL duplicate pair; the covariance of these rows is nonsingular).
Same lsqfit settings as paper_fits.py. Usage: independent_rows.py [--nsamp N]"""
import sys, os, argparse, warnings, json
sys.path.insert(0, "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/python_fits")
import numpy as np
import paper_fits as pf
ap = argparse.ArgumentParser(); ap.add_argument("--nsamp", type=int, default=None); a = ap.parse_args()
warnings.filterwarnings("ignore")
kin, S, cov = pf.load_amp("ReA2B", 2)
key = "P2"; m = pf.MODELS[key]; names = m["names"]; PL = -2
# independent rows: first occurrence of each (eta, |bL|, bT)
seen, keep = set(), []
for i, (e, l, t) in enumerate(kin):
    k = (e, abs(l), t)
    if k not in seen:
        seen.add(k); keep.append(i)
keep = np.array(keep)
n_all, n_ind = len(kin), len(keep)
Si = S[keep]; ci = cov[np.ix_(keep, keep)]
print(f"rows: all={n_all}, independent={n_ind}; cond(cov_ind)={np.linalg.cond(ci):.3g}", flush=True)
n, l, t = kin[keep].T
def fn_vec(p): return m["f"](dict(zip(names, p)), n, l, t, PL)
def fcn(x, p): return m["f"]({k: p[k] for k in names}, n, l, t, PL)
W = pf._whiten(ci)
best = pf.best_start(fn_vec, Si[:, 0], W, pf.starts(key))
cur = {k: float(v) for k, v in zip(names, best.x)}
Ns = S.shape[1] if a.nsamp is None else a.nsamp
chi = []
for i in range(Ns):
    f = pf.lsq_fit(fcn, Si[:, i], ci, cur); chi.append(f["chi2"]/f["dof"]); dof = f["dof"]
chi = np.array(chi); cm, ce = pf.jackknife(chi)
z = np.load(f"{pf.OUT}/PL2/fit_{key}.npz", allow_pickle=True)
print(f"INDEPENDENT rows: chi2/dof = {cm:.3f}({ce:.3f}) dof={dof} nsamp={Ns}")
print(f"ALL rows (paper_fits, saved): chi2/dof = {float(z['chi2']):.3f}({float(z['chi2err']):.3f}) dof={int(z['dof'])}")
print(f"RATIO independent/all = {cm/float(z['chi2']):.3f}")
