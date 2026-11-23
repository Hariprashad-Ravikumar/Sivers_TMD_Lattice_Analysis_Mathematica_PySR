#!/opt/homebrew/anaconda3/bin/python
"""Extrapolation ansatz comparison for the paper: p(zeta) = c + d/zeta (power 1) versus c + d/zeta^2 (power 2), fitted to P_L=-2,-3,-4
with the correlated jackknife fit of extrapolation_para_level.py (same loading, scaling, priors, fit routine; only the exponent differs).
Prints per parameter the jackknife chi2/dof of both forms, and the means over the 12 parameters."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, gvar as gv, lsqfit, h5py
import extrapolation_para_level as ex

PLS = [-2, -3, -4]
zeta = {-4: 0.785756, -3: 0.539684, -2: 0.294367, -1: 0.090772}
inv = np.array([1.0 / zeta[p] for p in PLS]); order = np.argsort(inv); inv = inv[order]; pls = [PLS[i] for i in order]
D = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/TMD_fit/h5data"
names = ['a_re', 'c_re', 'j_re', 'd_re', 'a_im', 'c_im', 'j_im', 'd_im', 'a_reA12B', 'c_reA12B', 'j_reA12B', 'd_reA12B']
P = [ex.load_params_from_h5(f"{D}/FitParams_SimulFit_f_A2BRe_cetasq_A2BIm_A12BRe_bmin3_eta610_PL{pl}.h5") for pl in pls]
N = len(P[0]['a_re']); raw = {k: np.zeros((len(pls), N)) for k in names}
for i, (pl, p) in enumerate(zip(pls, P)):
    for k in names:
        v = p[k]
        if k.startswith('c_'): v = v / pl**2
        if k == 'a_im': v = v / pl
        raw[k][i] = v

def fit(samples, power):
    n = samples.shape[1]
    cov = np.cov(samples, bias=True) * (n - 1)
    cov_e = gv.evalcov(gv.gvar(samples.mean(1), cov))
    prior = {'c0': gv.gvar(0, 5000000), 'c1': gv.gvar(0, 5000000)}
    f = lambda x, p: p['c0'] + p['c1'] * x**power
    chi = []; c0 = []
    for k in range(n):
        ft = lsqfit.nonlinear_fit(data=(inv, gv.gvar(samples[:, k], cov_e)), fcn=f, prior=prior)
        chi.append(ft.chi2 / ft.dof); c0.append(ft.pmean['c0'])
    return np.array(c0), np.array(chi)

res = {}
for k in names:
    r = {}
    for power in (1, 2):
        c0, chi = fit(raw[k], power)
        r[power] = (ex.Jackknife(c0), ex.Jackknife(chi))
    res[k] = r
    print(f"ZETA {k}: power1 chi2/dof {r[1][1][0]:.3f}({r[1][1][1]:.3f}) extrap {r[1][0][0]:.5g}  | power2 chi2/dof {r[2][1][0]:.3f}({r[2][1][1]:.3f}) extrap {r[2][0][0]:.5g}")
m1 = np.mean([res[k][1][1][0] for k in names]); m2 = np.mean([res[k][2][1][0] for k in names])
lower = sum(res[k][2][1][0] < res[k][1][1][0] for k in names)
print(f"ZETA mean chi2/dof over 12 parameters: power1 {m1:.3f} power2 {m2:.3f}; power2 lower for {lower} of 12 parameters")
