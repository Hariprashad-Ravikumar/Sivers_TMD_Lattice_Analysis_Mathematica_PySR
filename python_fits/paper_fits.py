#!/opt/homebrew/anaconda3/bin/python
"""
paper_fits.py -- Python reproduction of the Mathematica fit exploration (thesis chapter "Fitting methodologies and stability
analysis") for the Sivers paper.  Every chi^2/dof in this file is the *simultaneous-fit definition*:

  * lsqfit.nonlinear_fit, svdcut = 1e-12 (lsqfit default), no priors
  * covariance C = (Ns-1)/Ns * D D^T over ALL Ns = 2903 jackknife columns (column 0, the full-data value, is one of them),
    D = samples - row mean            (identical to SimultaneousFit_A12bA2B.py)
  * one fit per column; the reported number is the jackknife mean/error of fit.chi2/fit.dof,
    jackknife error = sqrt((Ns-1)/Ns * sum (x_k - xbar)^2)
  * dof = fit.dof = (#rows - #parameters); duplicate rows (bL -> -bL copies) are counted, as in the simultaneous fit.
NOTE (statistics audit): these are unconstrained, SINGLE-amplitude fits (no priors, no c>d reparametrisation, no cross-amplitude
covariance), so chi2/dof shares the data covariance, svdcut, per-sample averaging and jackknife with the simultaneous fit but is not
numerically the simultaneous-fit number (which has priors on every parameter and dof = number of data rows).

Sub-commands (all take --pl; PL=1 means P_L = -1, PL=2 means P_L = -2):
  fit     Re A2B global fits: 16 Gaussian ansaetze + 6 power-law c(eta) forms + 4 'wider' forms
  slices  eta-slice Lorentzian fits (c, d vs eta) for Re A2B, Re A12B, Im A2B with the other parameters fixed
  slopes  straight-line fits c(eta), d(eta) with the full jackknife covariance across eta
  tables  write revtex .tex tables
  plots   c, d vs eta figure
Designed for an 8 GB M1: <= 4 worker processes, one thread each, per-model results streamed to .npz (resumable).
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ[_v] = "1"          # must be set BEFORE numpy is imported (also in spawned workers, which re-import this file)
import argparse, sys, time, warnings, itertools, math, json
import numpy as np

ROOT = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project"
H5DIR = f"{ROOT}/save_h5_A12B_A2B"
OUT = f"{ROOT}/python_fits/paper_out"
BMIN, ETA_MIN, ETA_MAX = 3.0, 6, 10
SVDCUT = 1e-12
ETAS = list(range(ETA_MIN, ETA_MAX + 1))


# --------------------------------------------------------------------------------------------------------------------
# data
# --------------------------------------------------------------------------------------------------------------------
_CACHE = {}


def load_amp(amp, pl, drop_bL0=False):
    """amp in {'ReA2B','ReA12B','ImA2B'}.  Returns kin (n,3) [eta,bL,bT], S (n,Ns) incl. column 0, cov (n,n)."""
    key = (amp, pl, drop_bL0)
    if key in _CACHE:
        return _CACHE[key]
    import h5py
    d = np.array(h5py.File(f"{H5DIR}/{amp}_PL-{pl}_jackknife_data.h5", "r")["Dataset1"])
    keep = (np.hypot(d[:, 1], d[:, 2]) >= BMIN) & (d[:, 0] >= ETA_MIN) & (d[:, 0] <= ETA_MAX)
    if drop_bL0:
        keep &= d[:, 1] != 0
    d = d[keep]
    kin, S = d[:, :3].copy(), np.ascontiguousarray(d[:, 3:])
    Ns = S.shape[1]
    D = S - S.mean(1, keepdims=True)
    cov = (Ns - 1) / Ns * (D @ D.T)
    _CACHE[key] = (kin, S, cov)
    return _CACHE[key]


def jackknife(v):
    v = np.asarray(v, float)
    N = v.shape[0]
    m = v.mean(0)
    return m, np.sqrt((N - 1) / N * ((v - m) ** 2).sum(0))


# --------------------------------------------------------------------------------------------------------------------
# model library: Re A2B global fits
# --------------------------------------------------------------------------------------------------------------------
# eta-dependent forms (functions of eta only; parameters read from P)
CFORMS = {  # name: (extra parameter names, g(P, n))
    "c0": ([], lambda P, n: 1.0),
    "c1": (["kc1"], lambda P, n: 1 - P["kc1"] / n),
    "c2": (["kc1", "kc2"], lambda P, n: 1 + P["kc1"] / n - P["kc2"] / n ** 0.5),
    "c3": (["kc1", "kc2"], lambda P, n: 1 - P["kc1"] / n - P["kc2"] / n ** 2),
}
DFORMS = {
    "d0": ([], lambda P, n: 1.0),
    "d1": (["kd1"], lambda P, n: 1 - P["kd1"] / n),
    "d2": (["kd1", "kd2"], lambda P, n: 1 + P["kd1"] / n - P["kd2"] / n ** 0.5),
    "d3": (["kd1", "kd2"], lambda P, n: 1 - P["kd1"] / n - P["kd2"] / n ** 2),
}
# power-law c(eta) forms: c_eff = c * g
PFORMS = {
    "P0": (["k1"][:0], lambda P, n: 1.0, "c const"),
    "P1": (["k1"], lambda P, n: 1 - P["k1"] / n, "c(1-k1/eta)"),
    "P2": (["k1", "k2"], lambda P, n: 1 - P["k1"] / n - P["k2"] / n ** 2, "c(1-k1/eta-k2/eta^2)"),
    "P3": (["k1", "k2", "k3"], lambda P, n: 1 - P["k1"] / n - P["k2"] / n ** 2 - P["k3"] / n ** 3, "c(1-k1/eta-k2/eta^2-k3/eta^3)"),
    "P4": (["k1"], lambda P, n: 1 - P["k1"] * np.log(n) / n, "c(1-k1 ln(eta)/eta)"),
    "P5": (["k1", "k2", "nu"], lambda P, n: 1 - np.exp(-P["nu"] * n) * P["k2"] - P["k1"] / n, "c(1-exp(-nu eta) k2-k1/eta)"),
    "W1": (["k1", "k2"], lambda P, n: 1 - P["k1"] / n - P["k2"] * np.log(n) / n, "c(1-k1/eta-k2 ln(eta)/eta)"),
    "W2": (["k1", "k2"], lambda P, n: 1 - P["k1"] / n + P["k2"] / n ** 0.5, "c(1-k1/eta+k2/sqrt(eta))"),
    "W3": (["k1", "k2"], lambda P, n: 1 - P["k1"] / n + P["k2"] * np.log(n) / n ** 0.5, "c(1-k1/eta+k2 ln(eta)/sqrt(eta))"),
    "W4": (["k1", "k2"], lambda P, n: 1 + P["k1"] * n ** 0.5 / (1 + P["k2"] * n), "c(1+k1 sqrt(eta)/(1+k2 eta))"),
}
GAUSS_ORDER = ["a", "c", "kc1", "kc2", "d", "kd1", "kd2", "f"]
POWER_ORDER = ["a", "c", "d", "f", "k1", "k2", "k3", "nu", "j"]


def _gauss(cf, df):
    def f(P, n, l, t, PL):
        c = P["c"] * CFORMS[cf][1](P, n)
        d = P["d"] * DFORMS[df][1](P, n)
        return P["a"] * np.exp(-P["f"] * n) * np.exp(-c * (l * PL) ** 2 - d * (l ** 2 + t ** 2))
    return f


def _power(pf):
    def f(P, n, l, t, PL):
        c = P["c"] * PFORMS[pf][1](P, n)
        return P["a"] * np.exp(-P["f"] * n) * (1 + (P["d"] + c) * l ** 2 + P["d"] * t ** 2) ** (-P["j"])
    return f


def build_models():
    M = {}
    gi = 0
    for cf in CFORMS:
        for df in DFORMS:
            gi += 1
            names = ["a", "c"] + CFORMS[cf][0] + ["d"] + DFORMS[df][0] + ["f"]
            names = [x for x in GAUSS_ORDER if x in names]
            M[f"G{cf[1]}{df[1]}"] = dict(family="gauss", names=names, f=_gauss(cf, df), cform=cf, dform=df)
    for pf, (ex, g, desc) in PFORMS.items():
        names = [x for x in POWER_ORDER if x in (["a", "c", "d", "f", "j"] + ex)]
        M[pf] = dict(family="power", names=names, f=_power(pf), desc=desc)
    return M


MODELS = build_models()

INIT_BASE = dict(a=1.0, c=0.01, d=0.07, f=0.45, kc1=6.0, kc2=-10.0, kd1=3.0, kd2=4.0,
                 k1=8.0, k2=-20.0, k3=-100.0, nu=0.6, j=2.0)
POWER_INIT = dict(a=3.0, c=0.15, d=0.09, f=0.47, j=2.0, k1=10.0, k2=-30.0, k3=-100.0, nu=0.6)


def starts(key, nstart=12, seed=1):
    m = MODELS[key]
    base = dict(INIT_BASE)
    if m["family"] == "power":
        base.update(POWER_INIT)
    rng = np.random.default_rng(seed)
    out = [np.array([base[k] for k in m["names"]], float)]
    for _ in range(nstart - 1):
        out.append(np.array([base[k] * np.exp(rng.normal(0, 0.6)) * (1 if rng.random() < 0.8 else -1) if base[k] != 0 else rng.normal()
                             for k in m["names"]], float))
    return out


# --------------------------------------------------------------------------------------------------------------------
# fitting core (lsqfit)
# --------------------------------------------------------------------------------------------------------------------
def _whiten(cov):
    """eigen-decomposition with the same relative floor lsqfit's svdcut uses: eigenvalues < svdcut*max are raised to it."""
    w, U = np.linalg.eigh(cov)
    w = np.maximum(w, SVDCUT * w.max())
    return (U / np.sqrt(w)).T            # W such that chi2 = |W (y-f)|^2


def best_start(fn_vec, y0, W, p0s):
    from scipy.optimize import least_squares
    best = None
    for p0 in p0s:
        def res(p):
            f = fn_vec(p)
            return W @ (y0 - f) if np.all(np.isfinite(f)) else np.full(len(y0), 1e6)
        try:
            r = least_squares(res, p0, method="lm", xtol=1e-12, ftol=1e-12, gtol=1e-12, max_nfev=3000)
        except Exception:
            continue
        if np.all(np.isfinite(r.x)) and (best is None or r.cost < best.cost):
            best = r
    return best


def lsq_fit(fcn, y, cov, p0):
    """One lsqfit.nonlinear_fit with the same options as the simultaneous fit. gvar keeps every dense covariance it builds in a
    global store (~0.5 MB/call for 225 rows -> 1.5 GB per 2903-sample task), so each call uses a private store that is dropped
    afterwards; everything needed is read out as plain floats (results are bit-identical)."""
    import gvar as gv, lsqfit
    gv.switch_gvar()
    try:
        yg = gv.gvar(y, cov)
        fit = lsqfit.nonlinear_fit(data=(None, yg), fcn=fcn, p0=p0, svdcut=SVDCUT, debug=False)
        return dict(pmean={k: float(v) for k, v in fit.pmean.items()}, chi2=float(fit.chi2), dof=int(fit.dof),
                    stop=getattr(fit, "stopping_criterion", 1))
    finally:
        gv.restore_gvar()


def fit_model_samples(key, pl, nsamp=None):
    """Global Re A2B fit of one model over all jackknife samples."""
    import gvar as gv
    warnings.filterwarnings("ignore")
    kin, S, cov = load_amp("ReA2B", pl)
    m = MODELS[key]
    names = m["names"]
    n, l, t = kin.T
    PL = -pl
    W = _whiten(cov)

    def fn_vec(p):
        return m["f"](dict(zip(names, p)), n, l, t, PL)

    def fcn(x, p):
        return m["f"]({k: p[k] for k in names}, n, l, t, PL)

    best = best_start(fn_vec, S[:, 0], W, starts(key))
    if best is None:
        return dict(key=key, ok=False)
    p0 = {k: float(v) for k, v in zip(names, best.x)}
    Ns = S.shape[1] if nsamp is None else nsamp
    P, chi, dofs, failed, noconv = [], [], [], [], []
    cur = dict(p0)
    for i in range(Ns):
        try:
            fit = lsq_fit(fcn, S[:, i], cov, cur)
            if not np.all(np.isfinite(list(fit["pmean"].values()))) or not np.isfinite(fit["chi2"]):
                raise FloatingPointError("non-finite fit")
            P.append([fit["pmean"][k] for k in names])
            chi.append(fit["chi2"] / fit["dof"])
            dofs.append(fit["dof"])
            if not fit["stop"]:      # 0 = did not converge
                noconv.append(i)
        except Exception:
            failed.append(i)
    P, chi = np.array(P), np.array(chi)
    if len(failed) > 0 or len(P) == 0:
        # never average over a subset of the jackknife samples silently
        return dict(key=key, ok=False, reason=f"{len(failed)} failed samples, first {failed[:5]}", fails=len(failed))
    pm, pe = jackknife(P)
    cm, ce = jackknife(chi)
    return dict(key=key, ok=True, names=names, pmean=pm, perr=pe, chi2=cm, chi2err=ce, dof=int(dofs[0]), nsamp=len(P),
                fails=0, noconv=len(noconv), chi2max=float(chi.max()), chi2med=float(np.median(chi)), start_cost=float(best.cost) * 2)


AMP_SIGN = dict(ReA12B=-1.0, ImA2B=+1.0)


def fit_amp_samples(amp, pl, nsamp=None):
    """Separate global fit of Re A12B or Im A2B (constant c): sign*a*exp(-f eta)*[bL for Im A2B]*(1+(d+c) bL^2+d bT^2)^(-j); a, c, d, f, j free.
    Same lsqfit setup as fit_model_samples (full jackknife covariance of the rows, svdcut, per-sample fits)."""
    warnings.filterwarnings("ignore")
    odd = amp == "ImA2B"
    kin, S, cov = load_amp(amp, pl, drop_bL0=odd)
    names = ["a", "c", "d", "f", "j"]
    n, l, t = kin.T
    W = _whiten(cov)

    def mod(P):
        den = 1 + (P["d"] + P["c"]) * l ** 2 + P["d"] * t ** 2
        if np.any(den <= 0):
            return np.full(len(l), np.nan)
        return AMP_SIGN[amp] * P["a"] * np.exp(-P["f"] * n) * (l if odd else 1.0) * den ** (-P["j"])

    fn_vec = lambda p: mod(dict(zip(names, p)))
    fcn = lambda x, p: mod({k: p[k] for k in names})
    rng = np.random.default_rng(1)
    base = dict(a=0.5, c=0.07, d=0.07, f=0.5, j=2.0)
    starts_ = [np.array([base[k] for k in names])] + [np.array([base[k] * np.exp(rng.normal(0, 0.5)) for k in names]) for _ in range(15)]
    best = best_start(fn_vec, S[:, 0], W, starts_)
    if best is None:
        return dict(key=amp + "_c0", ok=False)
    cur = {k: float(v) for k, v in zip(names, best.x)}
    Ns = S.shape[1] if nsamp is None else nsamp
    P, chi, dofs, failed, noconv = [], [], [], [], []
    for i in range(Ns):
        try:
            f = lsq_fit(fcn, S[:, i], cov, cur)
            if not np.all(np.isfinite(list(f["pmean"].values()))) or not np.isfinite(f["chi2"]):
                raise FloatingPointError("non-finite fit")
            P.append([f["pmean"][k] for k in names]); chi.append(f["chi2"] / f["dof"]); dofs.append(f["dof"])
            if not f["stop"]:
                noconv.append(i)
        except Exception:
            failed.append(i)
    if failed or not P:
        return dict(key=amp + "_c0", ok=False, reason=f"{len(failed)} failed samples")
    P, chi = np.array(P), np.array(chi)
    pm, pe = jackknife(P); cm, ce = jackknife(chi)
    return dict(key=amp + "_c0", ok=True, names=names, pmean=pm, perr=pe, chi2=cm, chi2err=ce, dof=int(dofs[0]), nsamp=len(P), fails=0, noconv=len(noconv),
                chi2max=float(chi.max()), chi2med=float(np.median(chi)), start_cost=float(best.cost) * 2)


# --------------------------------------------------------------------------------------------------------------------
# eta-slice fits
# --------------------------------------------------------------------------------------------------------------------
THESIS_FIXED_PL1 = {   # a, f, j exactly as printed in the thesis slice tables (PL=-1)
    "ReA2B": dict(a=4.0, f=0.5, j=2.0, sign=+1, odd=False),
    "ReA12B": dict(a=0.658, f=0.4702, j=2.0054, sign=-1, odd=False),
    "ImA2B": dict(a=0.267, f=0.4702, j=1.108, sign=+1, odd=True),
}


def fixed_params(pl, source):
    """source='thesis' (PL=-1 only) or 'h5' (simultaneous-fit h5 for this PL, read-only)."""
    if source == "thesis":
        assert pl == 1
        return THESIS_FIXED_PL1
    if source == "seq":      # everything from the sequential/separate fits: Re A2B from the global fit of the adopted form P2, Re A12B and Im A2B from their own constant-c global fits
        od = outdir(pl)
        zp = np.load(f"{od}/fit_P2.npz", allow_pickle=True)
        nm = list(zp["names"])
        fx = {"ReA2B": dict(a=float(zp["pmean"][nm.index("a")]), f=float(zp["pmean"][nm.index("f")]), j=float(zp["pmean"][nm.index("j")]), sign=+1, odd=False)}
        for amp, odd in (("ReA12B", False), ("ImA2B", True)):
            z = np.load(f"{od}/fit_{amp}_c0.npz", allow_pickle=True)
            nm = list(z["names"])
            fx[amp] = dict(a=float(z["pmean"][nm.index("a")]), f=float(z["pmean"][nm.index("f")]), j=float(z["pmean"][nm.index("j")]), sign=int(AMP_SIGN[amp]), odd=odd)
        return fx
    if source == "own":      # Re A2B: (a, f, j) of my own correlated Re A2B fit (model P2); the other two amplitudes: simultaneous-fit h5
        fx = fixed_params(pl, "h5")
        z = np.load(f"{outdir(pl)}/fit_P2.npz", allow_pickle=True)
        nm = list(z["names"])
        fx["ReA2B"] = dict(a=float(z["pmean"][nm.index("a")]), f=float(z["pmean"][nm.index("f")]), j=float(z["pmean"][nm.index("j")]), sign=+1, odd=False)
        return fx
    import h5py
    fn = f"{H5DIR}/SimultaniousFit/FitParams_SimulFit_f_A2BRe_cetasq_A2BIm_A12BRe_bmin3_eta610_PL-{pl}.h5"
    h = h5py.File(fn, "r")
    g = lambda k: float(np.mean(np.array(h["jackknife_samples"][k])))
    return {
        "ReA2B": dict(a=g("a_re"), f=g("f"), j=g("j_re"), sign=+1, odd=False),
        "ReA12B": dict(a=g("a_reA12B"), f=g("f"), j=g("j_reA12B"), sign=-1, odd=False),
        "ImA2B": dict(a=g("a_im"), f=g("f"), j=g("j_im"), sign=+1, odd=True),
    }


def slice_fit(amp, pl, eta, fx, nsamp=None):
    warnings.filterwarnings("ignore")
    kin, S, cov_all = load_amp(amp, pl, drop_bL0=(amp == "ImA2B"))
    rows = np.where(kin[:, 0] == eta)[0]
    kin_s, S_s = kin[rows], S[rows]
    Ns = S.shape[1]
    D = S_s - S_s.mean(1, keepdims=True)
    cov = (Ns - 1) / Ns * (D @ D.T)
    n, l, t = kin_s.T
    pref = fx["sign"] * fx["a"] * np.exp(-fx["f"] * eta) * (l if fx["odd"] else 1.0)
    j = fx["j"]

    def model(c, d):
        den = 1 + (c + d) * l ** 2 + d * t ** 2
        if np.any(den <= 0):          # unphysical (negative denominator): reject
            return np.full(len(l), np.nan)
        return pref * den ** (-j)

    W = _whiten(cov)
    from scipy.optimize import least_squares
    best = None
    for c0, d0 in [(0.05, 0.1), (0.0, 0.05), (0.2, 0.2), (0.01, 0.3), (-0.02, 0.09)]:
        def res(p):
            f = model(*p)
            return W @ (S_s[:, 0] - f) if np.all(np.isfinite(f)) else np.full(len(l), 1e6)
        r = least_squares(res, [c0, d0], method="lm", xtol=1e-12, ftol=1e-12, gtol=1e-12)
        if best is None or r.cost < best.cost:
            best = r
    cur = dict(c=float(best.x[0]), d=float(best.x[1]))

    def fcn(x, p):
        return model(p["c"], p["d"])

    P, chi, dofs, failed, noconv = [], [], [], [], []
    for i in range(Ns if nsamp is None else nsamp):
        try:
            fit = lsq_fit(fcn, S_s[:, i], cov, cur)
            if not np.all(np.isfinite(list(fit["pmean"].values()))) or not np.isfinite(fit["chi2"]):
                raise FloatingPointError("non-finite fit")
            P.append([fit["pmean"]["c"], fit["pmean"]["d"]])
            chi.append(fit["chi2"] / fit["dof"])
            dofs.append(fit["dof"])
            if not fit["stop"]:
                noconv.append(i)
        except Exception:
            failed.append(i)
    P, chi = np.array(P), np.array(chi)
    if len(failed) > 0 or len(P) == 0:
        return dict(amp=amp, eta=eta, ok=False, reason=f"{len(failed)} failed samples, first {failed[:5]}", fails=len(failed))
    pm, pe = jackknife(P)
    cm, ce = jackknife(chi)
    return dict(amp=amp, eta=eta, ok=True, c=pm[0], cerr=pe[0], d=pm[1], derr=pe[1], chi2=cm, chi2err=ce, dof=int(dofs[0]), nrows=len(rows),
                nsamp=len(P), fails=0, noconv=len(noconv), P=P)


def line_fit(eta, Pcols):
    """Straight-line fit y = y0 + s*(eta-8) for one parameter. Pcols: (Nsamples, 5) per-sample estimates of the parameter at the 5 etas.
    Full jackknife covariance across eta (same (Ns-1)/Ns convention); lsqfit correlated chi2; dof = 5-2."""
    import gvar as gv, lsqfit
    N = Pcols.shape[0]
    ybar = Pcols.mean(0)
    D = Pcols - ybar
    cov = (N - 1) / N * (D.T @ D)
    eta = np.asarray(eta, float)
    fcn = lambda x, p: p["y0"] + p["s"] * (x - 8.0)
    fit = lsqfit.nonlinear_fit(data=(eta, gv.gvar(ybar, cov)), fcn=fcn, p0=dict(y0=float(ybar.mean()), s=0.0), svdcut=SVDCUT, debug=False)
    s = fit.p["s"]
    cv = gv.evalcov([fit.p["y0"], fit.p["s"]])
    return dict(slope=s.mean, slope_err=s.sdev, y0=fit.p["y0"].mean, y0_err=fit.p["y0"].sdev, cov_y0_s=float(cv[0][1]), chi2=fit.chi2, dof=fit.dof,
                chi2dof=fit.chi2 / fit.dof, ybar=ybar, yerr=np.sqrt(np.diag(cov)), cov=cov)


# --------------------------------------------------------------------------------------------------------------------
# multiprocessing driver
# --------------------------------------------------------------------------------------------------------------------
def _init():
    for v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
        os.environ[v] = "1"
    warnings.filterwarnings("ignore")


def _task(args):
    kind = args[0]
    t0 = time.time()
    if kind == "fit":
        _, key, pl, nsamp = args
        r = fit_model_samples(key, pl, nsamp)
        r["kind"], r["pl"], r["secs"] = "fit", pl, time.time() - t0
        return r
    if kind == "fitamp":
        _, amp, pl, nsamp = args
        r = fit_amp_samples(amp, pl, nsamp)
        r["kind"], r["pl"], r["secs"] = "fitamp", pl, time.time() - t0
        return r
    _, amp, pl, eta, fx, nsamp = args
    r = slice_fit(amp, pl, eta, fx, nsamp)
    r["kind"], r["pl"], r["secs"] = "slice", pl, time.time() - t0
    return r


def run_pool(tasks, workers):
    import multiprocessing as mp
    ctx = mp.get_context("spawn")
    with ctx.Pool(workers, initializer=_init, maxtasksperchild=1) as pool:
        for r in pool.imap_unordered(_task, tasks, chunksize=1):
            yield r


def outdir(pl):
    d = f"{OUT}/PL{pl}"
    os.makedirs(d, exist_ok=True)
    return d


def cmd_fit(a):
    keys = a.models.split(",") if a.models else list(MODELS)
    od = outdir(a.pl)
    todo = [k for k in keys if a.force or not os.path.exists(f"{od}/fit_{k}.npz")]
    HEAVY = ["P5", "W1", "P4", "G13", "G22"]               # ill-conditioned / slowest first so the pool does not idle at the end
    todo.sort(key=lambda k: HEAVY.index(k) if k in HEAVY else 99)
    print(f"[fit] PL={-a.pl}: {len(todo)} models to run ({len(keys)-len(todo)} cached), workers={a.workers}", flush=True)
    for r in run_pool([("fit", k, a.pl, a.nsamp) for k in todo], a.workers):
        if not r["ok"]:
            print(f"  {r['key']}: FAILED ({r.get('reason','no start converged')})", flush=True)
            continue
        tmp = f"{od}/.tmp_fit_{r['key']}.npz"
        np.savez(tmp, **{k: v for k, v in r.items() if k not in ("kind",)})
        os.replace(tmp, f"{od}/fit_{r['key']}.npz")
        print(f"  {r['key']:3s} chi2/dof={r['chi2']:.3f}({r['chi2err']:.3f}) dof={r['dof']} samples={r['nsamp']} noconv={r['noconv']} max/median chi2={r['chi2max']:.2f}/{r['chi2med']:.2f} [{r['secs']:.0f}s]", flush=True)


def cmd_fitamp(a):
    od = outdir(a.pl)
    print(f"[fitamp] PL={-a.pl}: separate global fits of Re A12B and Im A2B (constant c)", flush=True)
    for r in run_pool([("fitamp", amp, a.pl, a.nsamp) for amp in ("ReA12B", "ImA2B")], min(a.workers, 2)):
        if not r["ok"]:
            print(f"  {r['key']}: FAILED ({r.get('reason','no start converged')})", flush=True)
            continue
        np.savez(f"{od}/fit_{r['key']}.npz", **{k: v for k, v in r.items() if k != "kind"})
        pr = " ".join(f"{nm}={m:.5g}({e:.2g})" for nm, m, e in zip(r["names"], r["pmean"], r["perr"]))
        print(f"  {r['key']}: {pr} chi2/dof={r['chi2']:.3f}({r['chi2err']:.3f}) dof={r['dof']} noconv={r['noconv']} [{r['secs']:.0f}s]", flush=True)


def cmd_slices(a):
    fx_all = fixed_params(a.pl, a.fixed)
    od = outdir(a.pl)
    tasks = [("slice", amp, a.pl, eta, fx_all[amp], a.nsamp) for amp in fx_all for eta in ETAS]
    print(f"[slices] PL={-a.pl}, fixed from '{a.fixed}': {json.dumps(fx_all)}", flush=True)
    res = {}
    for r in run_pool(tasks, a.workers):
        if not r["ok"]:
            print(f"  {r['amp']:6s} eta={r['eta']:2d} FAILED: {r['reason']}", flush=True)
            continue
        res[(r["amp"], r["eta"])] = r
        print(f"  {r['amp']:6s} eta={r['eta']:2d} c={r['c']:.4g}({r['cerr']:.2g}) d={r['d']:.4g}({r['derr']:.2g}) chi2/dof={r['chi2']:.3f} dof={r['dof']} "
              f"noconv={r['noconv']} [{r['secs']:.0f}s]", flush=True)
    for amp in fx_all:
        if any((amp, e) not in res for e in ETAS):
            print(f"  {amp}: incomplete (a slice failed) -> NOT saved", flush=True)
            continue
        np.savez(f"{od}/.tmp_slices_{amp}.npz", eta=np.array(ETAS), c=[res[(amp, e)]["c"] for e in ETAS], cerr=[res[(amp, e)]["cerr"] for e in ETAS],
                 d=[res[(amp, e)]["d"] for e in ETAS], derr=[res[(amp, e)]["derr"] for e in ETAS],
                 chi2=[res[(amp, e)]["chi2"] for e in ETAS], chi2err=[res[(amp, e)]["chi2err"] for e in ETAS],
                 dof=[res[(amp, e)]["dof"] for e in ETAS], Pc=np.stack([res[(amp, e)]["P"][:, 0] for e in ETAS], 1),
                 Pd=np.stack([res[(amp, e)]["P"][:, 1] for e in ETAS], 1), fixed=json.dumps(fx_all[amp]))
        os.replace(f"{od}/.tmp_slices_{amp}.npz", f"{od}/slices_{amp}_{a.fixed}.npz")


def cmd_cfits(a):
    """Fit every c(eta) = c*g(eta) form to the five slice c values (means of the sequential individual fits) with the jackknife covariance across eta."""
    from scipy.optimize import least_squares
    od = outdir(a.pl)
    z = np.load(f"{od}/slices_ReA2B_{a.fixed}.npz")
    eta = z["eta"].astype(float)
    Pc = z["Pc"]
    N = Pc.shape[0]
    ybar = Pc.mean(0)
    D = Pc - ybar
    cov = (N - 1) / N * (D.T @ D)
    W = _whiten(cov)
    out = {}
    for key, (ex, g, desc) in PFORMS.items():
        names = ["c"] + ex
        starts_ = []
        zf = _load_fit(od, key)
        if zf is not None:
            pm = dict(zip([str(x) for x in zf["names"]], zf["pmean"]))
            starts_.append([pm[k] for k in names])
        rng = np.random.default_rng(2)
        base = dict(c=0.05, k1=6.0, k2=-5.0, k3=100.0, nu=0.3)
        starts_ += [[base[k] * np.exp(rng.normal(0, 0.7)) * (1 if rng.random() < 0.7 else -1) for k in names] for _ in range(40)]

        def mod(p):
            P = dict(zip(names, p))
            return P["c"] * g(P, eta) * np.ones_like(eta)

        best = None
        for p0 in starts_:
            def res(p):
                m = mod(p)
                return W @ (ybar - m) if np.all(np.isfinite(m)) else np.full(len(eta), 1e6)
            try:
                r = least_squares(res, p0, method="lm", xtol=1e-14, ftol=1e-14, gtol=1e-14, max_nfev=4000)
            except Exception:
                continue
            if np.all(np.isfinite(r.x)) and (best is None or r.cost < best.cost):
                best = r
        npar = len(names)
        chi2 = 2 * best.cost
        out[key] = dict(names=names, params=[float(v) for v in best.x], chi2=float(chi2), npar=npar, dof=len(eta) - npar,
                        chi2dof=float(chi2 / (len(eta) - npar)) if len(eta) > npar else None, c_eff=[float(v) for v in mod(best.x)])
        pr = " ".join(f"{nm}={v:.5g}" for nm, v in zip(names, best.x))
        print(f"  {key}: {pr}  chi2={chi2:.3f} dof={len(eta)-npar}", flush=True)
    json.dump(dict(eta=eta.tolist(), cbar=ybar.tolist(), forms=out), open(f"{od}/cfits_{a.fixed}.json", "w"), indent=1)


def cmd_slopes(a):
    od = outdir(a.pl)
    out = {}
    for amp in ("ReA2B", "ReA12B", "ImA2B"):
        z = np.load(f"{od}/slices_{amp}_{a.fixed}.npz")
        for par, col in (("c", "Pc"), ("d", "Pd")):
            lf = line_fit(z["eta"], z[col])
            out[f"{amp}_{par}"] = {k: (v.tolist() if isinstance(v, np.ndarray) else float(v)) for k, v in lf.items()}
            print(f"  {amp:6s} {par}: slope = {lf['slope']:.4g}({lf['slope_err']:.2g})  [{lf['slope']/lf['slope_err']:.2f} sigma]  "
                  f"chi2/dof = {lf['chi2dof']:.3f} (dof {lf['dof']})  y0 = {lf['y0']:.4g}({lf['y0_err']:.2g})", flush=True)
    json.dump(out, open(f"{od}/slopes_{a.fixed}.json", "w"), indent=1)


# --------------------------------------------------------------------------------------------------------------------
# tables (revtex) and plots
# --------------------------------------------------------------------------------------------------------------------
def fmt_err(mean, err):
    """value(err) with 2 significant digits of the error (same rule as SimultaneousFit_A12bA2B.py), LaTeX math-mode safe.
    Handles carry (0.0996 -> 0.10), scientific notation chosen on max(|mean|, err), no negative zero."""
    if not (np.isfinite(mean) and np.isfinite(err)):
        return r"\text{n/a}"
    if err <= 0:
        return f"{mean:.6g}".replace("e-0", "e-").replace("e+0", "e+")
    big = max(abs(mean), err)
    sci = big < 1e-3 or big >= 1e3
    e = int(math.floor(math.log10(big))) if sci else 0
    ms, es = mean / 10 ** e, err / 10 ** e
    place = int(math.floor(math.log10(es)))
    nd = max(0, -(place - 1))
    ei = int(round(es * 10 ** nd))
    if ei >= 100:                         # rounding carried the error to 3 digits
        nd = max(0, nd - 1)
        ei = int(round(es * 10 ** nd))
    mr = round(ms, nd)
    if sci and abs(mr) >= 10:             # keep the mantissa normalised
        e += 1
        ms, es = mean / 10 ** e, err / 10 ** e
        place = int(math.floor(math.log10(es)))
        nd = max(0, -(place - 1))
        ei = int(round(es * 10 ** nd))
        if ei >= 100:
            nd = max(0, nd - 1)
            ei = int(round(es * 10 ** nd))
        mr = round(ms, nd)
    mstr = f"{mr:.{nd}f}"
    if float(mstr) == 0:
        mstr = mstr.lstrip("-")
    out = f"{mstr}({ei})"
    return out + (rf"\times10^{{{e}}}" if sci else "")


PNAME = dict(a="a", c="c", d="d", f="f", j="j", kc1="k_{c1}", kc2="k_{c2}", kd1="k_{d1}", kd2="k_{d2}", k1="k_1", k2="k_2", k3="k_3", nu=r"\nu")
GAUSS_DESC = {
    "c0": "c", "c1": r"c(1-k_{c1}/\eta)", "c2": r"c(1+k_{c1}/\eta-k_{c2}/\sqrt{\eta})", "c3": r"c(1-k_{c1}/\eta-k_{c2}/\eta^2)",
}
GAUSS_DDESC = {
    "d0": "d", "d1": r"d(1-k_{d1}/\eta)", "d2": r"d(1+k_{d1}/\eta-k_{d2}/\sqrt{\eta})", "d3": r"d(1-k_{d1}/\eta-k_{d2}/\eta^2)",
}
POWER_TEX = {
    "P0": "c", "P1": r"c(1-k_1/\eta)", "P2": r"c(1-k_1/\eta-k_2/\eta^2)", "P3": r"c(1-k_1/\eta-k_2/\eta^2-k_3/\eta^3)",
    "P4": r"c(1-k_1\ln\eta/\eta)", "P5": r"c(1-k_1/\eta-k_2e^{-\nu\eta})",
    "W1": r"c(1-k_1/\eta-k_2\ln\eta/\eta)", "W2": r"c(1-k_1/\eta+k_2/\sqrt{\eta})", "W3": r"c(1-k_1/\eta+k_2\ln\eta/\sqrt{\eta})",
    "W4": r"c\left(1+\dfrac{k_1\sqrt{\eta}}{1+k_2\eta}\right)",
}


def degenerate(z):
    """True if an eta-shape parameter (k*, nu) is unconstrained (error >= |value|) or degenerate (|value| > 1e4): only combinations
    of the parameters are then determined and the printed values are not meaningful."""
    for nm, v, e in zip(z["names"], z["pmean"], z["perr"]):
        if str(nm).startswith("k") or str(nm) == "nu":
            if e >= abs(v) or abs(v) > 1e4:
                return True
    return False


def _load_fit(od, k):
    f = f"{od}/fit_{k}.npz"
    return np.load(f, allow_pickle=True) if os.path.exists(f) else None


GAUSS_C_TEX = {"c0": r"c", "c1": r"c(1-k_{c1}/\eta)", "c2": r"c(1+k_{c1}/\eta-k_{c2}/\sqrt{\eta})", "c3": r"c(1-k_{c1}/\eta-k_{c2}/\eta^2)"}
GAUSS_D_TEX = {"d0": r"d", "d1": r"d(1-k_{d1}/\eta)", "d2": r"d(1+k_{d1}/\eta-k_{d2}/\sqrt{\eta})", "d3": r"d(1-k_{d1}/\eta-k_{d2}/\eta^2)"}


def cmd_tables(a):
    od = outdir(a.pl)
    tag = f"PL{a.pl}"
    pls = f"P_L={-a.pl}"
    foot = r"The $\chi^2/\mathrm{dof}$ is the correlated value, given as the jackknife mean (error)."
    dag = ""
    foot_slice = (r"The $\chi^2/\mathrm{dof}$ is the correlated value with the jackknife covariance matrix of the rows in the slice (no correlations between different $\eta$), "
                  r"from \texttt{lsqfit} (singular-value cut $10^{-12}$), given as the jackknife mean (error) over the 2903 jackknife columns (including the central value); "
                  r"$\mathrm{dof}$ is the number of rows minus 2 and counts the duplicated ($b_L\to-b_L$) rows. The rows with $b_L=0$ of $\tAmp_{2B}^{\text{Im}}$, which vanish identically, are removed.")
    # Gaussian
    L = []
    cols = GAUSS_ORDER
    L.append(r"\begin{table*}")
    L.append(rf"\caption{{Fits of $\tAmp_{{2B}}^{{\text{{Re}}}}(b_L,b_T,\eta)$ at ${pls}$ ($|\vect b|\ge3a$, $6\le\eta\le10$) to $a\,e^{{-f\eta}}\exp[-c(\eta)(b_LP_L)^2-d(\eta)(b_L^2+b_T^2)]$ for different $c(\eta)$ and $d(\eta)$. Here $c$ multiplies $(b_LP_L)^2$, so it differs from the $c$ of the other tables by $P_L^2$. {foot}}}")
    L.append(rf"\label{{tab:gauss_family_{tag}}}")
    L.append(r"\scriptsize")
    L.append(r"\begin{ruledtabular}")
    L.append(r"\begin{tabular}{l@{\hspace{3pt}}l" + r"@{\hspace{3pt}}c" * (len(cols) + 1) + "}")
    L.append(r"$c(\eta)$ & $d(\eta)$ & " + " & ".join(f"${PNAME[c]}$" for c in cols) + r" & $\chi^2/\mathrm{dof}$ \\")
    L.append(r"\hline")
    for cf in CFORMS:
        for df in DFORMS:
            key = f"G{cf[1]}{df[1]}"
            z = _load_fit(od, key)
            desc = f"${GAUSS_C_TEX[cf]}$ & ${GAUSS_D_TEX[df]}$"
            if z is None:
                L.append(desc + " & " + " & ".join("---" for _ in cols) + r" & not run \\")
                continue
            nm = list(z["names"])
            cells = [(f"${fmt_err(z['pmean'][nm.index(c)], z['perr'][nm.index(c)])}$" if c in nm else "") for c in cols]
            L.append(desc + " & " + " & ".join(cells) + f" & ${fmt_err(float(z['chi2']), float(z['chi2err']))}$ \\\\")
    L += [r"\end{tabular}", r"\end{ruledtabular}", r"\end{table*}"]
    open(f"{od}/table_gauss_family_{tag}.tex", "w").write("\n".join(L) + "\n")
    # power law
    L = []
    cols = POWER_ORDER
    L.append(r"\begin{table*}")
    L.append(rf"\caption{{Fits of $\tAmp_{{2B}}^{{\text{{Re}}}}$ at ${pls}$ ($|\vect b|\ge3a$, $6\le\eta\le10$) to $a\,e^{{-f\eta}}\{{1+[d+c\,g(\eta)]b_L^2+d\,b_T^2\}}^{{-j}}$ for different $c(\eta)=c\,g(\eta)$. {foot}}}")
    L.append(rf"\label{{tab:powerlaw_family_{tag}}}")
    L.append(r"\scriptsize")
    L.append(r"\begin{ruledtabular}")
    L.append(r"\begin{tabular}{l" + r"@{\hspace{3pt}}c" * (len(cols) + 1) + "}")
    L.append(r"$c(\eta)$ & " + " & ".join(f"${PNAME[c]}$" for c in cols) + r" & $\chi^2/\mathrm{dof}$ \\")
    L.append(r"\hline")
    for key in PFORMS:
        z = _load_fit(od, key)
        desc = f"${POWER_TEX[key]}$"
        if z is None:
            L.append(desc + " & " + " & ".join("---" for _ in cols) + r" & not run \\")
            continue
        nm = list(z["names"])
        cells = [(f"${fmt_err(z['pmean'][nm.index(c)], z['perr'][nm.index(c)])}$" if c in nm else "") for c in cols]
        L.append(desc + " & " + " & ".join(cells) + f" & ${fmt_err(float(z['chi2']), float(z['chi2err']))}$ \\\\")
    L += [r"\end{tabular}", r"\end{ruledtabular}", r"\end{table*}"]
    open(f"{od}/table_powerlaw_family_{tag}.tex", "w").write("\n".join(L) + "\n")
    # (the per-eta slice table and the slopes table are no longer in the paper; slopes and chi2/dof are quoted in the text and shown in the figure)
    fcj = f"{od}/cfits_{a.fixed}.json"
    if os.path.exists(fcj):
        cf = json.load(open(fcj))["forms"]
        def g3(v):
            return f"{v:.3g}".replace("e-0", "e-").replace("e+0", "e+")
        L = [r"\begin{table*}",
             rf"\caption{{Forms $c(\eta)=c\,g(\eta)$ fitted to the five values of $c$ from the fits of individual $\eta$ slices of $\tAmp_{{2B}}^{{\text{{Re}}}}$ at ${pls}$ (dashed curves in Fig.~\ref{{fig:c_d_eta_PL2}}). The $\chi^2/\mathrm{{dof}}$ is the correlated value with the jackknife covariance of the five $c$ across $\eta$.}}",
             r"\label{tab:c_eta_forms_PL2}", r"\scriptsize", r"\begin{ruledtabular}", r"\begin{tabular}{l@{\hspace{3pt}}c@{\hspace{3pt}}c@{\hspace{3pt}}c@{\hspace{3pt}}c@{\hspace{3pt}}c@{\hspace{3pt}}c}",
             r"$c(\eta)$ & $c$ & $k_1$ & $k_2$ & $k_3$ & $\nu$ & $\chi^2/\mathrm{dof}$ \\", r"\hline"]
        for key in PFORMS:
            f_ = cf[key]; P = dict(zip(f_["names"], f_["params"]))
            cells = [f"${g3(P[k])}$" if k in P else "" for k in ("c", "k1", "k2", "k3", "nu")]
            L.append(f"${POWER_TEX[key]}$ & " + " & ".join(cells) + f" & ${f_['chi2'] / f_['dof']:.2f}$ \\\\")
        L += [r"\end{tabular}", r"\end{ruledtabular}", r"\end{table*}"]
        open(f"{od}/table_c_eta_forms_{tag}.tex", "w").write("\n".join(L) + "\n")
    print(f"[tables] written to {od}", flush=True)


def power_c_eff(od, key, eta, fixed="seq"):
    """c(eta) = c * g(eta) of the form `key`, with c and k's from the fit of that form to the five slice c values (cmd_cfits)"""
    cf = json.load(open(f"{od}/cfits_{fixed}.json"))["forms"].get(key)
    if cf is None:
        return None
    P = dict(zip(cf["names"], cf["params"]))
    e = np.asarray(eta, float)
    return P["c"] * PFORMS[key][1](P, e) * np.ones_like(e)


def cmd_plots(a):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.gridspec import GridSpec
    from matplotlib.lines import Line2D
    od = outdir(a.pl)
    s = json.load(open(f"{od}/slopes_{a.fixed}.json"))
    # text about the size of the paper text: figure is 7.0 in wide and is included at \textwidth
    plt.rcParams.update({"font.size": 9, "axes.labelsize": 10.5, "axes.titlesize": 10.5, "xtick.labelsize": 9, "ytick.labelsize": 9,
                         "legend.fontsize": 8.5, "mathtext.fontset": "cm", "pdf.fonttype": 42, "ps.fonttype": 42})
    amps = [("ReA2B", r"$\tilde A_{2B}^{\rm Re}$"), ("ReA12B", r"$\tilde A_{12B}^{\rm Re}$"), ("ImA2B", r"$\tilde A_{2B}^{\rm Im}$")]
    fig = plt.figure(figsize=(7.0, 6.9))
    gs = GridSpec(2, 3, figure=fig, width_ratios=[1.9, 1, 1], height_ratios=[1.25, 1], left=0.105, right=0.99, top=0.955, bottom=0.285, wspace=0.40, hspace=0.34)
    colors = plt.cm.tab10(np.arange(10))
    pkeys = list(PFORMS)
    xx = np.linspace(5.6, 10.4, 80)
    axs = {}
    for j, (amp, tit) in enumerate(amps):
        z = np.load(f"{od}/slices_{amp}_{a.fixed}.npz", allow_pickle=True)
        eta = z["eta"].astype(float)
        for i, (par, y, ye) in enumerate((("c", z["c"], z["cerr"]), ("d", z["d"], z["derr"]))):
            ax = fig.add_subplot(gs[i, j], sharex=axs.get((0, 0)))
            axs[(i, j)] = ax
            r = s[f"{amp}_{par}"]
            line = r["y0"] + r["slope"] * (xx - 8)
            var = r["y0_err"] ** 2 + 2 * (xx - 8) * r["cov_y0_s"] + (xx - 8) ** 2 * r["slope_err"] ** 2
            band = np.sqrt(np.maximum(var, 0))
            ax.fill_between(xx, line - band, line + band, color="C3", alpha=0.18, lw=0)
            ax.plot(xx, line, color="C3", lw=1.6, zorder=2)
            if amp == "ReA2B" and par == "c":
                for k, key in enumerate(pkeys):
                    ce = power_c_eff(od, key, xx, a.fixed)
                    if ce is not None:
                        ax.plot(xx, ce, color=colors[k], lw=1.3, ls="--", zorder=1)
            ax.errorbar(eta, y, ye, fmt="o", color="k", ms=4.5, capsize=3, lw=1.2, zorder=4)
            ax.set_title(f"{tit}: ${par}$")
            ax.set_ylabel(f"${par}$")
            ax.margins(y=0.35)
            sl = fmt_err(r["slope"], r["slope_err"])
            ax.text(0.04, 0.96, rf"$s={sl}$" + "\n" + rf"$\chi^2/\mathrm{{dof}}={r['chi2dof']:.2f}$", transform=ax.transAxes, fontsize=8.5, va="top",
                    bbox=dict(fc="w", ec="none", alpha=0.85, pad=1.5))
            ax.grid(True, ls="--", alpha=0.3)
            if i == 0:
                plt.setp(ax.get_xticklabels(), visible=False)
            else:
                ax.set_xlabel(r"$\eta|\vec v|/a$")
    # c(eta) range of the model curves is allowed to leave the data range: clip the Re A2B c panel to the slice data plus margin
    axc = axs[(0, 0)]
    zc = np.load(f"{od}/slices_ReA2B_{a.fixed}.npz", allow_pickle=True)
    lo, hi = float((zc["c"] - zc["cerr"]).min()), float((zc["c"] + zc["cerr"]).max())
    pad = 0.25 * (hi - lo)
    axc.set_ylim(lo - pad, hi + pad)
    handles = [Line2D([0], [0], color="k", marker="o", ls="", ms=4.5, label="slice fits"), Line2D([0], [0], color="C3", lw=1.6, label=r"straight line $y_0+s(\eta-8)$")]
    handles += [Line2D([0], [0], color=colors[k], lw=1.3, ls="--", label=f"${POWER_TEX[key]}$") for k, key in enumerate(pkeys) if power_c_eff(od, key, [8.0], a.fixed) is not None]
    fig.legend(handles=handles, loc="lower center", ncol=3, frameon=False, bbox_to_anchor=(0.5, 0.005), handlelength=2.4, columnspacing=1.4, labelspacing=0.55,
               title=r"$c(\eta)=c\,g(\eta)$ fitted to the slice values of $c$ (dashed, $\tilde A_{2B}^{\rm Re}$ panel)", title_fontsize=9)
    fn = f"{od}/c_d_vs_eta_PL{a.pl}.pdf"
    fig.savefig(fn)
    print(f"[plots] {fn}", flush=True)
    for key in pkeys:
        ce = power_c_eff(od, key, np.array([6., 7., 8., 9., 10.]), a.fixed)
        if ce is not None:
            print(f"[plots] c_eff {key}: " + " ".join(f"{v:.4f}" for v in ce), flush=True)


def cmd_panels(a):
    """c(eta) and d(eta) of the slice fits as single panels (3.4 x 2.55 in each) in the common paper style, plus a legend-only panel."""
    import sys as _sys
    _sys.path.insert(0, f"{ROOT}/python_fits/paper_figs")
    import paper_style as ps
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D
    od = outdir(a.pl); out = f"{ROOT}/python_fits/paper_figs/out/cd"; os.makedirs(out, exist_ok=True)
    s = json.load(open(f"{od}/slopes_{a.fixed}.json"))
    amps = [("ReA2B", r"$\tilde A_{2B}^{\rm Re}$"), ("ReA12B", r"$\tilde A_{12B}^{\rm Re}$"), ("ImA2B", r"$\tilde A_{2B}^{\rm Im}$")]
    pkeys = [k for k in PFORMS if power_c_eff(od, k, [8.0], a.fixed) is not None]
    _c6 = [ps.OKABE[k] for k in ("blue", "green", "pink", "orange", "sky", "black")]
    cols = [_c6[i % 6] for i in range(len(pkeys))]
    styles = ["-", "--", "-.", ":"]
    xx = np.linspace(5.6, 10.4, 80)
    for amp, tit in amps:
        z = np.load(f"{od}/slices_{amp}_{a.fixed}.npz", allow_pickle=True); eta = z["eta"].astype(float)
        for par, y, ye in (("c", z["c"], z["cerr"]), ("d", z["d"], z["derr"])):
            r = s[f"{amp}_{par}"]
            fig, ax = ps.new_panel()
            line = r["y0"] + r["slope"] * (xx - 8)
            var = r["y0_err"] ** 2 + 2 * (xx - 8) * r["cov_y0_s"] + (xx - 8) ** 2 * r["slope_err"] ** 2
            band = np.sqrt(np.maximum(var, 0))
            ax.fill_between(xx, line - band, line + band, color=ps.OKABE["vermillion"], alpha=0.2, lw=0)
            ax.plot(xx, line, color=ps.OKABE["vermillion"], lw=1.5, zorder=2)
            if amp == "ReA2B" and par == "c":
                for k, key in enumerate(pkeys):
                    ax.plot(xx, power_c_eff(od, key, xx, a.fixed), color=cols[k], ls=styles[k % 4], lw=1.0, zorder=1)
            ax.errorbar(eta, y, ye, fmt="o", color="k", ms=4, capsize=2, lw=1.0, zorder=4)
            ax.set_xlabel(r"$\eta|\vec v|/a$"); ax.set_ylabel(f"${par}$ of {tit}", fontsize=9); ax.set_xticks([6, 7, 8, 9, 10]); ax.margins(y=0.3)
            if amp == "ReA2B" and par == "c":
                lo, hi = float((y - ye).min()), float((y + ye).max()); pad = 0.25 * (hi - lo); ax.set_ylim(lo - pad, hi + pad)
            ax.text(0.04, 0.96, rf"$s={fmt_err(r['slope'], r['slope_err'])}$" + "\n" + rf"$\chi^2/\mathrm{{dof}}={r['chi2dof']:.2f}$", transform=ax.transAxes, va="top", fontsize=8,
                    bbox=dict(fc="w", ec="none", alpha=0.85, pad=1.5))
            ps.save(fig, f"{out}/cd_{amp}_{par}.pdf")
    # legend-only panel for the model curves
    fig, ax = ps.new_panel(); ax.set_position([0.0, 0.0, 1.0, 1.0]); ax.axis("off")
    hs = [Line2D([0], [0], color="k", marker="o", ls="", ms=4, label="slice fits"), Line2D([0], [0], color=ps.OKABE["vermillion"], lw=1.5, label=r"straight line $y_0+s(\eta-8)$")]
    hs += [Line2D([0], [0], color=cols[k], ls=styles[k % 4], lw=1.0, label=f"${POWER_TEX[key]}$") for k, key in enumerate(pkeys)]
    ax.legend(handles=hs, loc="center", fontsize=8, frameon=False, labelspacing=0.5, handlelength=2.0, ncol=2, columnspacing=1.0)
    ps.save(fig, f"{out}/cd_legend.pdf")
    print("[panels] written to", out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["fit", "fitamp", "slices", "slopes", "cfits", "tables", "plots", "panels", "list"])
    ap.add_argument("--pl", type=int, required=True, help="1 -> P_L=-1, 2 -> P_L=-2, ...")
    ap.add_argument("--models", default="")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--nsamp", type=int, default=None, help="debug: only first N samples")
    ap.add_argument("--fixed", default="h5", choices=["h5", "thesis", "own", "seq"], help="source of the fixed a,f,j in the slice fits")
    ap.add_argument("--force", action="store_true")
    a = ap.parse_args()
    if a.workers > 4:
        print("capping workers at 4 (8 GB machine)")
        a.workers = 4
    if a.cmd == "list":
        for k, m in MODELS.items():
            print(k, m["family"], m["names"])
        return
    {"fit": cmd_fit, "fitamp": cmd_fitamp, "slices": cmd_slices, "slopes": cmd_slopes, "cfits": cmd_cfits, "tables": cmd_tables, "plots": cmd_plots, "panels": cmd_panels}[a.cmd](a)


if __name__ == "__main__":
    main()
