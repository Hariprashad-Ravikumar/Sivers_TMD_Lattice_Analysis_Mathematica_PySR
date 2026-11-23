#!/opt/homebrew/anaconda3/bin/python
"""Individual Re A2B fits with EXACTLY the simultaneous-fit machinery (validated against FitParams_SimulFit_..._PL-1.h5,
see validate_simul.py): lsqfit.nonlinear_fit, svdcut=1e-12 (default), all rows (duplicates kept), covariance
(Ns-1)/Ns * D D^T over all 2903 columns, one fit per column (column 0 included), chi2/dof = fit.chi2/fit.dof averaged with the
jackknife formula (Ns-1)/Ns sum(.)^2.  lsqfit dof = nrows + nprior - npar  (=225 with priors on every parameter,
= 225 - npar without).
Modes:  prior : gvar priors centred on the Mathematica value, width = WIDTH x Mathematica jackknife error
        free  : no priors, start at the Mathematica values
Usage: jk_fit_lsqfit.py --pl 1 --models G1 [--width 2.0] [--nsamp N]"""
import argparse, os, pickle, sys, time, warnings
import numpy as np, gvar as gv, lsqfit
warnings.filterwarnings("ignore")
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import jk_fit as J0

def setup(pl):
    X, y0, Y, C, sig = J0.load(pl)           # J0.load drops column 0; rebuild with all 2903 columns exactly like the script
    import h5py
    d = np.array(h5py.File(f"{J0.ROOT}/save_h5_A12B_A2B/ReA2B_PL-{pl}_jackknife_data.h5", "r")["Dataset1"])
    keep = (np.hypot(d[:, 1], d[:, 2]) >= 3.0) & (d[:, 0] >= 6) & (d[:, 0] <= 10)
    d = d[keep]; X = d[:, :3]; S = d[:, 3:]  # S: 225 x 2903, column 0 = full-data value
    Ns = S.shape[1]; D = S - S.mean(1, keepdims=True); cov = (Ns-1)/Ns*D@D.T
    return X, S, cov

def jackknife(v):
    v = np.asarray(v, float); N = v.shape[0]; m = v.mean(0)
    return m, np.sqrt((N-1)/N*((v-m)**2).sum(0))

def run(pl, key, mode, width, nsamp):
    X, S, cov = setup(pl); PL = -pl
    m = J0.M[key]; names = m["names"]; n, l, t = X.T
    def fcn(x, p): return m["f"]([p[k] for k in names], n, l, t, PL, names)
    ref = m["ref"]
    prior = {k: gv.gvar(r[0], max(width*r[1], 1e-6)) for k, r in zip(names, ref)} if mode == "prior" else None
    p0 = None if mode == "prior" else {k: r[0] for k, r in zip(names, ref)}
    Ns = S.shape[1]; idx = range(Ns if nsamp is None else nsamp)
    P, chi, dofs, fails = [], [], [], 0
    pstart = dict(p0) if p0 else None
    for i in idx:
        try:
            yg = gv.gvar(S[:, i], cov)
            kw = dict(prior=prior) if prior is not None else dict(p0=pstart)
            fit = lsqfit.nonlinear_fit(data=(None, yg), fcn=fcn, debug=False, **kw)
            P.append([float(fit.pmean[k]) for k in names]); chi.append(fit.chi2/fit.dof); dofs.append(fit.dof)
        except Exception as e:
            fails += 1
    P = np.array(P); chi = np.array(chi)
    mp, ep = jackknife(P); mc, ec = jackknife(chi)
    return dict(key=key, mode=mode, names=names, jk_mean=mp, jk_err=ep, chi2dof=(mc, ec), dof=dofs[0] if dofs else None,
                fails=fails, nsamp=len(P), prior_width=width, P=P, chi=chi)

if __name__ == "__main__":
    ap = argparse.ArgumentParser(); ap.add_argument("--pl", type=int, default=1); ap.add_argument("--models", default="G1")
    ap.add_argument("--width", type=float, default=2.0); ap.add_argument("--nsamp", type=int, default=None)
    a = ap.parse_args(); out = {}
    for key in a.models.split(","):
        for mode in ("prior", "free"):
            t0 = time.time(); r = run(a.pl, key, mode, a.width, a.nsamp); out[(key, mode)] = r
            m = J0.M[key]
            print(f"\n[{key}] {m['desc']}  mode={mode}  dof={r['dof']}  samples={r['nsamp']} (failed {r['fails']})  "
                  f"chi2/dof = {r['chi2dof'][0]:.3f}({r['chi2dof'][1]:.3f})   Mathematica chi2/dof {m['chi2']}   [{time.time()-t0:.0f}s]")
            print(f"  {'par':5s} {'Mathematica':>16s} {'lsqfit '+mode:>18s}   (lsq-M)/errM")
            for i, nm in enumerate(r["names"]):
                rm, re_ = m["ref"][i]
                print(f"  {nm:5s} {rm:9.4g}({re_:<6.2g}) {r['jk_mean'][i]:11.4g}({r['jk_err'][i]:<7.2g}) {(r['jk_mean'][i]-rm)/re_:9.2f}")
    pickle.dump(out, open(f"{J0.ROOT}/python_fits/results_lsqfit_PL-{a.pl}_{a.models.replace(',','-')}.pkl", "wb"))
