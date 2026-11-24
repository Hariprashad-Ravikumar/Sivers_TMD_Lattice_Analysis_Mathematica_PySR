#!/opt/homebrew/anaconda3/bin/python
"""
paper_fits_separable.py -- separable longitudinal x transverse fits of Re A2B (same fit procedure as paper_fits.py, which is imported):

  EE  Exp|P.b| * Exp|b|        a e^{-f eta} exp(-c g(eta) |b_L P_L|)            exp(-d |b|)
  PE  Powerlaw|P.b| * Exp|b|   a e^{-f eta} (1 + c g(eta) (b_L P_L)^2)^(-j)      exp(-d |b|)
  EP  Exp|P.b| * Powerlaw|b|   a e^{-f eta} exp(-c g(eta) |b_L P_L|)            (1 + d b^2)^(-j)

  |b| = sqrt(b_L^2 + b_T^2), b^2 = b_L^2 + b_T^2,  d constant in eta,  c(eta) = c g(eta) with
  g0 = 1, g1 = 1-k1/eta, g2 = 1-k1/eta-k2/eta^2, g3 = 1-k1/eta-k2/eta^2-k3/eta^3, gs = 1-k1/sqrt(eta)

Fit procedure = paper_fits.py (simultaneous-fit definition of chi^2/dof): lsqfit.nonlinear_fit, svdcut 1e-12, no priors, covariance
(Ns-1)/Ns D D^T over all Ns = 2903 jackknife columns of the rows with |b| >= 3a, 6 <= eta <= 10, one fit per column,
chi^2/dof reported as jackknife mean (error), dof = rows - parameters (duplicated b_L -> -b_L rows counted).
A model is never averaged over a subset of the samples: if any sample fails the model is reported as failed.

  python paper_fits_separable.py fit    --pl 2 [--models EE0,PE1,...] [--workers 4] [--nsamp N] [--force]
  python paper_fits_separable.py tables --pl 2
"""
import os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ[_v] = "1"
import argparse, sys, time, warnings
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paper_fits as PF

GFORMS = {   # suffix: (shape parameters, g(P, eta), LaTeX of c(eta))
    "0": ([], lambda P, n: 1.0, r"c"),
    "1": (["k1"], lambda P, n: 1 - P["k1"] / n, r"c(1-k_1/\eta)"),
    "2": (["k1", "k2"], lambda P, n: 1 - P["k1"] / n - P["k2"] / n ** 2, r"c(1-k_1/\eta-k_2/\eta^2)"),
    "3": (["k1", "k2", "k3"], lambda P, n: 1 - P["k1"] / n - P["k2"] / n ** 2 - P["k3"] / n ** 3, r"c(1-k_1/\eta-k_2/\eta^2-k_3/\eta^3)"),
    "s": (["k1"], lambda P, n: 1 - P["k1"] / np.sqrt(n), r"c(1-k_1/\sqrt{\eta})"),
}
FAMS = {
    "EE": dict(title=r"Exp$|P\!\cdot\! b|\times$Exp$|b|$", eq=r"a\,e^{-f\eta}\exp[-c(\eta)|b_LP_L|]\,e^{-d|\vect b|}", extra=[]),
    "PE": dict(title=r"Powerlaw$|P\!\cdot\! b|\times$Exp$|b|$", eq=r"a\,e^{-f\eta}\,[1+c(\eta)(b_LP_L)^2]^{-j}\,e^{-d|\vect b|}", extra=["j"]),
    "EP": dict(title=r"Exp$|P\!\cdot\! b|\times$Powerlaw$|b|$", eq=r"a\,e^{-f\eta}\exp[-c(\eta)|b_LP_L|]\,(1+d\,b^2)^{-j}", extra=["j"]),
}
ORDER = ["a", "c", "k1", "k2", "k3", "d", "f", "j"]
PNAME = dict(a="a", c="c", k1="k_1", k2="k_2", k3="k_3", d="d", f="f", j="j")
INIT = dict(EE=dict(a=2.0, c=0.1, d=0.3, f=0.45, k1=5.0, k2=-10.0, k3=-50.0),
            PE=dict(a=3.0, c=0.01, d=0.3, f=0.45, k1=5.0, k2=-10.0, k3=-50.0, j=2.0),
            EP=dict(a=3.0, c=0.1, d=0.08, f=0.45, k1=5.0, k2=-10.0, k3=-50.0, j=2.0))


def model_names(key):
    fam, g = key[:2], key[2]
    names = ["a", "c"] + GFORMS[g][0] + ["d", "f"] + FAMS[fam]["extra"]
    return [x for x in ORDER if x in names]


def model_fn(key):
    fam, g = key[:2], key[2]
    gf = GFORMS[g][1]

    def f(P, n, l, t, PL):
        c = P["c"] * gf(P, n)
        x = l * PL
        if fam == "EE":
            return P["a"] * np.exp(-P["f"] * n) * np.exp(-c * np.abs(x)) * np.exp(-P["d"] * np.hypot(l, t))
        if fam == "PE":
            base = 1 + c * x ** 2
            if np.any(base <= 0):
                return np.full(len(l), np.nan)
            return P["a"] * np.exp(-P["f"] * n) * base ** (-P["j"]) * np.exp(-P["d"] * np.hypot(l, t))
        base = 1 + P["d"] * (l ** 2 + t ** 2)
        if np.any(base <= 0):
            return np.full(len(l), np.nan)
        return P["a"] * np.exp(-P["f"] * n) * np.exp(-c * np.abs(x)) * base ** (-P["j"])
    return f


ALLKEYS = [fam + g for fam in FAMS for g in GFORMS]


def starts(key, nstart=80, seed=1):
    """many starts: the base point, log-normal scatter around it, and wide log-uniform draws of c and j (the power-law
    longitudinal models have a nearly flat valley in (c, j, k))"""
    names = model_names(key)
    base = INIT[key[:2]]
    rng = np.random.default_rng(seed)
    out = [np.array([base[k] for k in names], float)]
    for i in range(nstart - 1):
        v = []
        for k in names:
            x = base[k] * np.exp(rng.normal(0, 0.6)) * (1 if rng.random() < 0.8 else -1)
            if i % 2 and k == "c" and key[:2] == "PE":
                x = 10 ** rng.uniform(-3, 2)
            if i % 2 and k == "j":
                x = 10 ** rng.uniform(-2, 0.7)
            v.append(x)
        out.append(np.array(v, float))
    if key[:2] == "PE":      # deterministic grid over the flat (c, j, k) valley of the power-law longitudinal models
        kset = [(6.0, -10.0, -50.0), (12.0, -37.0, 0.0), (21.0, -145.0, 335.0), (3.0, 0.0, 0.0)]
        for c0 in (0.1, 1.0, 5.0, 20.0, 60.0):
            for j0 in (0.01, 0.03, 0.1, 0.3, 1.0):
                for ks in kset:
                    v, ik = [], 0
                    for k in names:
                        if k in ("k1", "k2", "k3"):
                            v.append(ks[int(k[1]) - 1])
                        else:
                            v.append({"c": c0, "j": j0}.get(k, base[k]))
                    out.append(np.array(v, float))
    return out


def polish(fn_vec, y0, W, best, rounds=25, seed=7):
    """basin-hopping style refinement of the full-data optimum: perturb the best point and re-minimise, keep the lowest chi^2"""
    from scipy.optimize import least_squares
    rng = np.random.default_rng(seed)
    cur = best
    for r in range(rounds):
        scale = 0.02 if r % 2 == 0 else 0.15
        p0 = cur.x * (1 + scale * rng.normal(size=cur.x.size))
        def res(p):
            f = fn_vec(p)
            return W @ (y0 - f) if np.all(np.isfinite(f)) else np.full(len(y0), 1e6)
        try:
            t = least_squares(res, p0, method="lm", xtol=1e-14, ftol=1e-14, gtol=1e-14, max_nfev=20000)
        except Exception:
            continue
        if np.all(np.isfinite(t.x)) and t.cost < cur.cost:
            cur = t
    return cur


def lsq_fit_tight(fcn, y, cov, p0):
    """PF.lsq_fit with the same options (svdcut, no priors, private gvar store) and a tighter lsqfit convergence tolerance, so a flat valley is followed to its bottom"""
    import gvar as gv, lsqfit
    gv.switch_gvar()
    try:
        yg = gv.gvar(y, cov)
        fit = lsqfit.nonlinear_fit(data=(None, yg), fcn=fcn, p0=p0, svdcut=PF.SVDCUT, tol=1e-12, maxit=20000, debug=False)
        return dict(pmean={k: float(v) for k, v in fit.pmean.items()}, chi2=float(fit.chi2), dof=int(fit.dof), stop=getattr(fit, "stopping_criterion", 1))
    finally:
        gv.restore_gvar()


def fit_samples(key, pl, nsamp=None):
    warnings.filterwarnings("ignore")
    kin, S, cov = PF.load_amp("ReA2B", pl)
    names = model_names(key)
    f = model_fn(key)
    n, l, t = kin.T
    PL = -pl
    W = PF._whiten(cov)
    fn_vec = lambda p: f(dict(zip(names, p)), n, l, t, PL)
    fcn = lambda x, p: f({k: p[k] for k in names}, n, l, t, PL)
    best = PF.best_start(fn_vec, S[:, 0], W, starts(key))
    if best is None:
        return dict(key=key, ok=False, reason="no start converged")
    best = polish(fn_vec, S[:, 0], W, best)
    cur = {k: float(v) for k, v in zip(names, best.x)}
    Ns = S.shape[1] if nsamp is None else nsamp
    P, chi, dofs, failed, noconv = [], [], [], [], []
    for i in range(Ns):
        try:
            fit = lsq_fit_tight(fcn, S[:, i], cov, cur)
            if not np.all(np.isfinite(list(fit["pmean"].values()))) or not np.isfinite(fit["chi2"]):
                raise FloatingPointError("non-finite fit")
            P.append([fit["pmean"][k] for k in names]); chi.append(fit["chi2"] / fit["dof"]); dofs.append(fit["dof"])
            if not fit["stop"]:
                noconv.append(i)
        except Exception:
            failed.append(i)
    if failed or not P:
        return dict(key=key, ok=False, reason=f"{len(failed)} failed samples, first {failed[:5]}", fails=len(failed))
    P, chi = np.array(P), np.array(chi)
    pm, pe = PF.jackknife(P); cm, ce = PF.jackknife(chi)
    return dict(key=key, ok=True, names=names, pmean=pm, perr=pe, chi2=cm, chi2err=ce, dof=int(dofs[0]), nsamp=len(P), fails=0, noconv=len(noconv),
                chi2max=float(chi.max()), chi2med=float(np.median(chi)), start_cost=float(best.cost) * 2)


def _task(args):
    key, pl, nsamp = args
    t0 = time.time()
    r = fit_samples(key, pl, nsamp)
    r["secs"] = time.time() - t0
    return r


def run_pool(tasks, workers):
    import multiprocessing as mp
    ctx = mp.get_context("spawn")
    with ctx.Pool(workers, initializer=PF._init, maxtasksperchild=1) as pool:
        for r in pool.imap_unordered(_task, tasks, chunksize=1):
            yield r


def cmd_fit(a):
    keys = a.models.split(",") if a.models else ALLKEYS
    od = PF.outdir(a.pl)
    todo = [k for k in keys if a.force or not os.path.exists(f"{od}/sep_{k}.npz")]
    print(f"[sep fit] PL={-a.pl}: {len(todo)} models to run ({len(keys) - len(todo)} cached), workers={a.workers}", flush=True)
    for r in run_pool([(k, a.pl, a.nsamp) for k in todo], a.workers):
        if not r["ok"]:
            print(f"  {r['key']}: FAILED ({r.get('reason')})", flush=True)
            continue
        tmp = f"{od}/.tmp_sep_{r['key']}.npz"
        np.savez(tmp, **r)
        os.replace(tmp, f"{od}/sep_{r['key']}.npz")
        print(f"  {r['key']:4s} chi2/dof={r['chi2']:.3f}({r['chi2err']:.3f}) dof={r['dof']} samples={r['nsamp']} noconv={r['noconv']} "
              f"max/median chi2={r['chi2max']:.2f}/{r['chi2med']:.2f} {r['secs']:.0f}s", flush=True)


def cmd_tables(a):
    od = PF.outdir(a.pl)
    tag = f"PL{a.pl}"
    pls = f"P_L={-a.pl}"
    foot = r"The $\chi^2/\mathrm{dof}$ is the correlated value, given as the jackknife mean (error)."
    names = dict(EE="Exp|P.b| x Exp|b|", PE="Powerlaw|P.b| x Exp|b|", EP="Exp|P.b| x Powerlaw|b|")
    for fam, info in FAMS.items():
        cols = [c for c in ORDER if c in (["a", "c", "k1", "k2", "k3", "d", "f"] + info["extra"])]
        L = [r"\begin{table*}",
             rf"\caption{{Fits of $\tAmp_{{2B}}^{{\text{{Re}}}}(b_L,b_T,\eta)$ at ${pls}$ ($|\vect b|\ge3a$, $6\le\eta\le10$) to ${info['eq']}$ for different $c(\eta)$. "
             rf"Here $|\vect b|=\sqrt{{b_L^2+b_T^2}}$ and $b^2=b_L^2+b_T^2$. {foot}}}",
             rf"\label{{tab:sep_{fam}_{tag}}}", r"\scriptsize", r"\begin{ruledtabular}",
             r"\begin{tabular}{l" + r"@{\hspace{3pt}}c" * (len(cols) + 1) + "}",
             r"$c(\eta)$ & " + " & ".join(f"${PNAME[c]}$" for c in cols) + r" & $\chi^2/\mathrm{dof}$ \\", r"\hline"]
        for g in GFORMS:
            fn_ = f"{od}/sep_{fam}{g}.npz"; z = np.load(fn_, allow_pickle=True) if os.path.exists(fn_) else None
            desc = f"${GFORMS[g][2]}$"
            if z is None:
                L.append(desc + " & " + " & ".join("---" for _ in cols) + r" & not run \\")
                continue
            nm = list(z["names"])
            cells = [(f"${PF.fmt_err(z['pmean'][nm.index(c)], z['perr'][nm.index(c)])}$" if c in nm else "") for c in cols]
            L.append(desc + " & " + " & ".join(cells) + f" & ${PF.fmt_err(float(z['chi2']), float(z['chi2err']))}$ \\\\")
        L += [r"\end{tabular}", r"\end{ruledtabular}", r"\end{table*}"]
        open(f"{od}/table_sep_{fam}_{tag}.tex", "w").write("\n".join(L) + "\n")
    print(f"[sep tables] written to {od}", flush=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["fit", "tables"])
    ap.add_argument("--pl", type=int, required=True)
    ap.add_argument("--models", default="")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--nsamp", type=int, default=None)
    ap.add_argument("--force", action="store_true")
    a = ap.parse_args()
    {"fit": cmd_fit, "tables": cmd_tables}[a.cmd](a)


if __name__ == "__main__":
    main()
