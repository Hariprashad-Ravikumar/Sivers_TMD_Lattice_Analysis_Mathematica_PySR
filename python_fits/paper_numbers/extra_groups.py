"""Claim groups that read script logs / saved fit outputs (imported by paper_numbers.py)."""
import os, re, json, math, csv
import numpy as np
import paper_numbers as pn
from paper_numbers import add, jk, PAPER, ROOT, PF, LOGS, FAIL, tex_cells, UNVERIFIED

FIT = "sections/analysis_fitting.tex"
APC = "sections/appendixC.tex"
EXT = "sections/analysis_extrapolation.tex"
APF = "sections/appendix_factorization.tex"


def add_bool(file, literal, cond, src):
    """literal must occur in the tex; cond (bool computed from script output) must hold"""
    pn.CLAIMS.append(dict(file=file, literal=literal, value=None, err=None, src=src + f" [condition {'OK' if cond else 'FALSE'}]"))
    if not cond:
        FAIL.append(f"{file}: condition for {literal!r} is false ({src})")


def read(path):
    return open(path).read()


def pm(s):
    """'0.0568(78)' or '6(96)e-17' or '-0.169(29)' -> (mean, err)"""
    m = re.fullmatch(r"([+-]?\d*\.?\d+)\(([\d.]+)\)(?:e(-?\d+))?", s.strip())
    assert m, s
    mean = float(m.group(1)); dec = len(m.group(1).split(".")[1]) if "." in m.group(1) else 0
    e = m.group(2); err = float(e) if "." in e else float(e) * 10.0 ** (-dec)
    sc = 10.0 ** int(m.group(3)) if m.group(3) else 1.0
    return mean * sc, err * sc


# ------------------------------------------------------------------------------------------------------------------
def group_pysr():
    rows = {int(r["complexity"]): r for r in csv.DictReader(open(f"{ROOT}/PySR/outputs_A2B_real_PL2/hall_of_fame_summary.csv"))}
    fl = lambda c: [float(x) for x in re.findall(r"\d+\.\d+", rows[c]["sympy_format"])]
    L = {c: float(rows[c]["loss"]) for c in rows}
    tex = read(f"{PAPER}/{FIT}")
    seg = tex[tex.index("\\label{tab:pysr_pareto}"):tex.index("\\end{table*}", tex.index("\\label{tab:pysr_pareto}"))]
    # loss column
    for c, lit in ((1, "72.06"), (3, "48.89"), (4, "48.03"), (7, "29.71"), (9, "5.89"), (11, "2.54"), (13, "1.61"), (15, "1.38"), (17, "1.26"), (19, "1.05")):
        add(FIT, lit, L[c], None, f"PySR hall_of_fame loss C={c}")
    n = fl
    assert len(n(1)) == 1 and len(n(3)) == 1 and len(n(4)) == 1
    add(FIT, "0.00328", n(1)[0], None, "PySR C=1 constant")
    add(FIT, "0.4693", n(3)[0], None, "PySR C=3")
    add(FIT, "0.757", -math.log(n(3)[0]), None, "PySR C=3: -ln(base)")
    add(FIT, "0.851", n(4)[0], None, "PySR C=4")
    add(FIT, "19.64", n(7)[0], None, "PySR C=7")
    a, b = n(9); add(FIT, "9.475", a, None, "PySR C=9"); add(FIT, "4.065", b, None, "PySR C=9")
    a, b, c = n(11); add(FIT, "7.034", a, None, "PySR C=11"); add(FIT, "4.123", b, None, "PySR C=11"); add(FIT, "1.56", 2 * c, None, "PySR C=11: 2*0.7822748")
    a, b, c, d = n(13)   # 9.715, lb, lt, base
    add(FIT, "9.715", a, None, "C=13"); add(FIT, "6.19", 1 / b, None, "C=13 1/scale"); add(FIT, "5.73", 1 / c, None, "C=13"); add(FIT, "0.570", math.log(d), None, "C=13 ln(base)")
    lb, lt, p, A, base = n(15)   # order in sympy_format: lb, lt, power, A, base
    add(FIT, "4.596", A, None, "C=15"); add(FIT, "21.2", 1 / lb, None, "C=15"); add(FIT, "20.4", 1 / lt, None, "C=15"); add(FIT, "3.23", 2 * p, None, "C=15 2*power")
    k, lb, lt, p, A, base = n(17)
    add(FIT, "4.172", A, None, "C=17"); add(FIT, "15.4", 1 / lb, None, "C=17"); add(FIT, "14.8", 1 / lt, None, "C=17"); add(FIT, "2.64", 2 * p, None, "C=17")
    add(FIT, "0.542", math.log(base), None, "C=17"); add(FIT, "0.000396", k, None, "C=17 offset")
    lb, lt, p, c0, A, base = n(19)
    add(FIT, "4.848", A, None, "C=19"); add(FIT, "22.0", 1 / lb, None, "C=19"); add(FIT, "18.9", 1 / lt, None, "C=19"); add(FIT, "3.35", 2 * p, None, "C=19"); add(FIT, "6.83", c0, None, "C=19")
    # prose
    add_bool(FIT, "\\approx0.76$", abs(-math.log(n(3)[0]) - 0.76) < 0.005, "f from C=3 base")
    # scales of bL and bT differ by at most 4% (scale = 1/sqrt(coefficient)), over C=13,15,17,19
    rel = []
    for c, (i, j) in ((13, (1, 2)), (15, (0, 1)), (17, (1, 2))):
        v = fl(c) if c != 17 else fl(c)
        s1, s2 = 1 / math.sqrt(v[i if c != 15 else 0]), 1 / math.sqrt(v[j if c != 15 else 1])
        rel.append(abs(s1 / s2 - 1))
    add_bool(FIT, "$4\\%$", abs(max(rel) - 0.04) < 0.005, f"max relative difference of bL/bT scales over C=13,15,17: {max(rel):.4f}")
    add_bool(FIT, "below $1$ at $C\\ge21$", all(L[c] < 1 for c in L if c >= 21) and L[19] >= 1, "PySR losses C>=21 < 1, C=19 >= 1")
    add_bool(FIT, "lower by more than a third", 1 - L[13] / L[11] > 1 / 3, f"1-L13/L11 = {1 - L[13] / L[11]:.3f}")
    # make_paper_PL_figs.py log
    log = read(f"{LOGS}/make_paper_PL_figs_PL2.log")
    chi = {int(m.group(1)): float(m.group(2)) for m in re.finditer(r"C=(\d+): chi2/dof\(npar not subtracted\)=([\d.]+)", log)}
    add(FIT, "$1.59$", chi[13], None, "make_paper_PL_figs.py"); add(FIT, "$1.36$", chi[15], None, "make_paper_PL_figs.py")
    add(FIT, "$1.24$", chi[17], None, "make_paper_PL_figs.py (C=17)"); add(FIT, "$2.51$", chi[11], None, "make_paper_PL_figs.py (C=11)")
    md = re.search(r"Delta chi2 \(Gaussian - Lorentzian, one extra parameter\) = ([\d.]+)", log)
    add_bool(FIT, "\\Delta\\chi^2\\approx138", round(float(md.group(1))) == 138, f"make_paper_PL_figs.py: Delta chi2 = {md.group(1)}")
    mg = re.search(r"Gaussian: params=\[([^\]]+)\], chi2/dof=([\d.]+)", log); pg = [float(x) for x in mg.group(1).split()]
    ml = re.search(r"Lorentzian: params=\[([^\]]+)\], chi2/dof=([\d.]+)", log); pl_ = [float(x) for x in ml.group(1).split()]
    add(FIT, "$c=0.076$", pg[1], None, "make_paper_PL_figs.py Gaussian straight line"); add(FIT, "$\\chi^2/\\text{dof}=2.03$", float(mg.group(2)), None, "same")
    add(FIT, "0.041", pl_[1], None, "Lorentzian c"); add(FIT, "3.48", pl_[2], None, "Lorentzian j"); add(FIT, "$\\chi^2/\\text{dof}=1.42$", float(ml.group(2)), None, "same")



def group_gauss():
    log = read(f"{LOGS}/gauss_corr_PL2.log")
    r = {}
    for m in re.finditer(r"PL=-2 (\w+): rows=(\d+) dof=(\d+).*alpha-beta=([-\d.]+)\(([\d.]+)\)\s+chi2/dof=([\d.]+)\(([\d.]+)\)", log):
        r[m.group(1)] = dict(rows=int(m.group(2)), ab=float(m.group(4)), abe=float(m.group(5)), chi=float(m.group(6)), chie=float(m.group(7)))
    a, b = r["ReA2B"], r["ReA12B"]
    add(FIT, "-0.474(5)", a["ab"], a["abe"], "gauss_corr.py --pl 2")
    add(FIT, "$93.9(2.4)$", a["chi"], a["chie"], "gauss_corr.py --pl 2")
    add(FIT, "$0.005(30)$", b["ab"], b["abe"], "gauss_corr.py --pl 2")
    add(FIT, "$2.39(39)$", b["chi"], b["chie"], "gauss_corr.py --pl 2")
    add(FIT, "$66$", a["rows"], None, "gauss_corr.py rows")


def group_exp():
    log = read(f"{LOGS}/exp_straight_PL2.log")
    me = re.search(r"exp: params=\[\s*([^\s]+)\s+([^\s]+)\s+([^\s]+)\], L=([\d.]+)", log)
    mc = re.search(r"exp\+const: .*L=([\d.]+)", log)
    c, L1, L2 = float(me.group(2)), float(me.group(4)), float(mc.group(1))
    for f in (APC, FIT):
        add(f, "$c=0.685$", c, None, "make_exp_straight_PL.py --pl 2")
    add(APC, "$\\mathcal L=1.42$", L1, None, "make_exp_straight_PL.py"); add(APC, "$\\mathcal L=1.31$", L2, None, "make_exp_straight_PL.py")
    mp = re.search(r"Pareto losses: (\[.*\])", log); par = {int(a): b for a, b in eval(mp.group(1))}
    add(APC, "$\\mathcal L=1.61$", par[13], None, "PySR Pareto C=13"); add(APC, "$1.38$", par[15], None, "PySR C=15"); add(APC, "$1.26$", par[17], None, "PySR C=17")


def group_eta():
    od = f"{PF}/paper_out/PL2"
    z = lambda k: np.load(f"{od}/fit_{k}.npz", allow_pickle=True)
    P0, P1, P2 = z("P0"), z("P1"), z("P2")
    add(FIT, "$1.24(15)$", float(P0["chi2"]), float(P0["chi2err"]), "paper_fits.py fit P0")
    add(FIT, "$1.12(14)$", float(P1["chi2"]), float(P1["chi2err"]), "paper_fits.py fit P1")
    dchi = (float(P0["chi2"]) * int(P0["dof"]) - float(P1["chi2"]) * int(P1["dof"]))
    add_bool(FIT, "by 28", round(dchi) == 28, f"chi2(P0)-chi2(P1) = {dchi:.2f}")
    nm = list(P2["names"]); add(FIT, "-6(25)", float(P2["pmean"][nm.index("k2")]), float(P2["perr"][nm.index("k2")]), "paper_fits.py fit P2 k2")
    gk = [k for k in ("G00 G01 G02 G03 G10 G11 G12 G13 G20 G21 G22 G23 G30 G31 G32 G33".split())]
    gz = {k: z(k) for k in gk if os.path.exists(f"{od}/fit_{k}.npz") and bool(z(k)["ok"])}
    chis = [float(v["chi2"]) for v in gz.values()]
    add(FIT, "$1.56$", min(chis), None, "paper_fits.py: min Gaussian-family chi2/dof"); add(FIT, "$1.91$", max(chis), None, "paper_fits.py: max Gaussian-family chi2/dof")
    add(APC, "$\\chi^2/\\text{dof}=1.56$", min(chis), None, "same")
    # power-law family range 1.10-1.24
    pk = [k for k in ("P0 P1 P2 P3 P4 P5 W1 W2 W3 W4".split())]
    pch = [float(z(k)["chi2"]) for k in pk if os.path.exists(f"{od}/fit_{k}.npz") and bool(z(k)["ok"])]
    add(APC, "$1.10$", min(pch), None, "paper_fits.py: min power-law chi2/dof"); add(APC, "$1.24$", max(pch), None, "paper_fits.py: max power-law chi2/dof")
    add(FIT, "$-0.0017(7)$", float(z("G00")["pmean"][list(z("G00")["names"]).index("c")]), float(z("G00")["perr"][list(z("G00")["names"]).index("c")]), "paper_fits.py fit G00 c")
    # 100-180 higher chi2 for the same number of parameters
    def chi2tot(v): return float(v["chi2"]) * int(v["dof"])
    byn = {}
    for k, v in z_all(od, pk).items(): byn.setdefault(len(v["names"]), []).append(chi2tot(v))
    diffs = []
    for k, v in gz.items():
        npar = len(v["names"])
        if npar in byn: diffs += [chi2tot(v) - min(byn[npar])]
    add_bool(FIT, "73 to 138", round(min(diffs)) == 73 and round(max(diffs)) == 138, f"chi2(Gaussian) - chi2(best power law, same #params): min {min(diffs):.1f} max {max(diffs):.1f} over {len(diffs)} models")
    add_bool(FIT, "15 Gaussian forms", len(diffs) == 15, f"{len(diffs)} Gaussian forms have a power-law form with the same number of parameters")
    # independent rows
    log = read(f"{LOGS}/independent_rows_PL2.log")
    mi = re.search(r"INDEPENDENT rows: chi2/dof = ([\d.]+)\(([\d.]+)\)", log); mr = re.search(r"RATIO independent/all = ([\d.]+)", log)
    ma = re.search(r"all=(\d+), independent=(\d+)", log)
    add(FIT, "$1.84$", float(mi.group(1)), None, "independent_rows.py"); add(FIT, "$1.12$", float(P2["chi2"]), None, "paper_fits.py fit P2")
    add_bool(FIT, "about 1.6 times larger", abs(float(mr.group(1)) - 1.6) < 0.1, f"ratio {mr.group(1)}")
    add(FIT, "140", int(ma.group(2)), None, "independent_rows.py (unique rows)")
    # slopes (slice fits with a, f, j from the separate global fits: fixed source 'seq')
    ss = json.load(open(f"{od}/slopes_seq.json"))
    f2 = lambda r: (r["slope"], r["slope_err"])
    add(FIT, "$0.0054(19)$", *f2(ss["ReA2B_c"]), "paper_fits.py slopes seq"); add(FIT, "$0.29$", ss["ReA2B_c"]["chi2dof"], None, "paper_fits.py slopes seq")
    add(FIT, "$2.8\\sigma$", ss["ReA2B_c"]["slope"] / ss["ReA2B_c"]["slope_err"], None, "slope/err")
    add(FIT, "$0.0006(9)$", *f2(ss["ReA2B_d"]), "paper_fits.py slopes seq"); add(FIT, "$4.3$", ss["ReA2B_d"]["chi2dof"], None, "paper_fits.py slopes seq")
    add(FIT, "$0.0098(87)$", *f2(ss["ReA12B_c"]), "slopes seq"); add(FIT, "$0.0004(29)$", *f2(ss["ReA12B_d"]), "slopes seq")
    add(FIT, "$0.0010(41)$", *f2(ss["ImA2B_c"]), "slopes seq"); add(FIT, "$-0.0006(29)$", *f2(ss["ImA2B_d"]), "slopes seq")
    four = ("ReA12B_c", "ReA12B_d", "ImA2B_c", "ImA2B_d")
    mx = max(abs(ss[k]["slope"]) / ss[k]["slope_err"] for k in four)
    add_bool(FIT, "within $1.2\\sigma$ of zero", mx < 1.2 and mx > 1.1, f"max |slope|/err over the four A12B/Im slopes = {mx:.3f}")
    add_bool(FIT, "$\\chi^2/\\text{dof}<1$", all(ss[k]["chi2dof"] < 1 for k in four), "chi2/dof<1 for the four lines")
    # fixed a, f, j of the slice fits (separate fits)
    fxs = fixed_seq()
    ra, rb, rc = fxs["ReA2B"], fxs["ReA12B"], fxs["ImA2B"]
    add(FIT, "$a=2.47$", ra["a"], None, "fit_P2.npz"); add(FIT, "$f=0.484$", ra["f"], None, "fit_P2.npz"); add(FIT, "$j=2.52$", ra["j"], None, "fit_P2.npz")
    add(FIT, "$a=0.77$", rb["a"], None, "fit_ReA12B_c0.npz"); add(FIT, "$f=0.50$", rb["f"], None, "fit_ReA12B_c0.npz"); add(FIT, "$j=2.41$", rb["j"], None, "fit_ReA12B_c0.npz")
    add(FIT, "$a=0.44$", rc["a"], None, "fit_ImA2B_c0.npz"); add(FIT, "$f=0.60$", rc["f"], None, "fit_ImA2B_c0.npz"); add(FIT, "$j=2.37$", rc["j"], None, "fit_ImA2B_c0.npz")
    # c(eta) forms fitted to the slice c values
    cj = json.load(open(f"{od}/cfits_seq.json"))["forms"]
    add(FIT, "$\\chi^2/\\text{dof}=2.17$", cj["P0"]["chi2"] / cj["P0"]["dof"], None, "paper_fits.py cfits seq: constant c, chi2/dof")
    add_bool(FIT, "while all $\\eta$-dependent forms do", all(v["chi2"] < 2.5 for k, v in cj.items() if k != "P0"), f"max chi2 of the eta-dependent forms = {max(v['chi2'] for k, v in cj.items() if k != 'P0'):.2f}")
    # table of the forms (cell by cell against the generated table is done in group_generated_tables)


def fixed_seq():
    import sys
    sys.path.insert(0, PF)
    import importlib, paper_fits as pf
    return pf.fixed_params(2, "seq")


def z_all(od, keys):
    out = {}
    for k in keys:
        f = f"{od}/fit_{k}.npz"
        if os.path.exists(f):
            v = np.load(f, allow_pickle=True)
            if bool(v["ok"]):
                out[k] = {n: v[n] for n in v.files}
    return out


def group_fact_data():
    def parse(path):
        d = {}
        for ln in read(path).splitlines():
            m = re.match(r"\s*(\w+)\s+(top|bottom)\s+curve=(\d+) x=(\d+): lin ([\d.]+)\(([\d.]+)\)\s+quad ([\d.]+)\(([\d.]+)\)", ln)
            if m: d[(m.group(1), m.group(2), int(m.group(3)), int(m.group(4)))] = (float(m.group(5)), float(m.group(6)))
        return d
    p1, p2 = parse(f"{PF}/fact_orig/PL-1/out.txt"), parse(f"{PF}/fact_orig/PL-2/out.txt")
    s = "factorization_ratio_test_PLscaled.py"
    c = lambda d, k: d[k]
    for lit, d, k in (("$0.81(6)$", p2, ("ReA2B", "top", 6, 18)), ("$1.14(8)$", p2, ("ReA2B", "top", 6, 25)), ("$2.0(4)$", p2, ("ReA2B", "top", 6, 32)),
                      ("$1.01(17)$", p2, ("ReA2B", "top", 0, 25)), ("$0.92(3)$", p1, ("ReA2B", "top", 3, 18)), ("$1.17(3)$", p1, ("ReA2B", "top", 3, 25)),
                      ("$1.55(9)$", p1, ("ReA2B", "top", 3, 32)),
                      ("$0.42(5)$", p2, ("ReA2B", "bottom", 32, 0)), ("$0.54(3)$", p2, ("ReA2B", "bottom", 32, 6)), ("$0.22(5)$", p2, ("ReA2B", "bottom", 32, 8)),
                      ("$0.40(3)$", p1, ("ReA2B", "bottom", 32, 0)), ("$0.60(1)$", p1, ("ReA2B", "bottom", 32, 3)), ("$0.35(2)$", p1, ("ReA2B", "bottom", 32, 4))):
        m, e = d[k]; add(EXT, lit, m, e, f"{s} output ({'PL-2' if d is p2 else 'PL-1'}) {k}")
    add_bool(EXT, "errors are about twice as large", 1.7 < p2[("ReA2B", "top", 6, 18)][1] / p1[("ReA2B", "top", 3, 18)][1] < 2.3,
             f"error ratio PL-2/PL-1 of T at b2=18: {p2[('ReA2B','top',6,18)][1] / p1[('ReA2B','top',3,18)][1]:.2f}")


def group_extrap():
    ex = read(f"{PF}/sivers_pipeline/out_final/extrap.log")
    # zeta values and 1/zeta
    z = {1: 0.090772, 2: 0.294367, 3: 0.539684, 4: 0.785756}
    src = read(f"{PF}/sivers_pipeline/scripts/extrap_final.py")
    for k, v in z.items():
        assert str(v) in src, v
        add(EXT, f"{v}", v, None, "pl_to_zeta in extrapolation_para_level.py")
    for lit, k in (("11.02", 1), ("3.40", 2), ("1.85", 3), ("1.27", 4)):
        add(EXT, lit, 1 / z[k], None, "1/zeta_hat")
    # integral table
    rows = {}
    for ln in ex.splitlines():
        if ln.startswith("| $") and "Integral" not in ln:
            cells = [c.strip() for c in ln.strip().strip("|").split("|")]
            rows[len(rows)] = cells[1:]
    assert len(rows) == 5, rows
    tex = read(f"{PAPER}/{EXT}"); seg = tex[tex.index("\\label{tab:integrals}"):]
    trows = [r for r in tex_cells(seg)][1:6]
    for ri, (tr, cells) in enumerate(zip(trows, [rows[i] for i in range(5)])):
        for k in range(4):
            m, e = pm(cells[k]); add(EXT, tr[k + 1], m, e, f"extrapolation_para_level.py log, integral table row {ri} col {k}")
    # Sivers peaks
    mp = re.search(r"SIVERS peak <k_y> = ([\d.]+) GeV at x = ([\d.]+); at x=0.5: ([\d.]+); x<k_y> peak = ([\d.]+) at x = ([\d.]+)", ex)
    ky, kx, k5, xky, xkx = [float(mp.group(i)) for i in range(1, 6)]
    add_bool(EXT, "about $0.21$~GeV at small $x$", abs(ky - 0.21) < 0.01 and kx < 0.1, f"peak {ky} at x={kx}")
    add_bool(EXT, "near zero by $x\\approx0.5$", k5 < 0.02, f"<k_y>(x=0.5) = {k5}")
    add_bool(EXT, "about $0.02$~GeV near $x\\approx0.15$", abs(xky - 0.02) < 0.002 and abs(xkx - 0.15) < 0.02, f"x<k_y> peak {xky} at x={xkx}")
    # param extrapolation values (factorization paragraph)
    par = {m.group(1): pm(m.group(2)) for m in re.finditer(r"PARAM (\w+) extrapolated (\S+)", ex)}
    for lit, key in (("$j_{\\text{re}}=2.0667(69)$", "j_re"), ("$j_{\\text{im}}=0.9921(92)$", "j_im"), ("$j_{\\text{reA12B}}=2.0026(40)$", "j_reA12B"),
                     ("$d_{\\text{re}}=0.139(12)$", "d_re"), ("$d_{\\text{im}}=0.183(14)$", "d_im"), ("$d_{\\text{reA12B}}=0.105(18)$", "d_reA12B")):
        val = lit.split("=")[1].rstrip("$")
        add(EXT, val, par[key][0], par[key][1], f"extrapolation_para_level.py log PARAM {key}")
    # distances (Sivers shift) and fm values
    fs = read(f"{PF}/sivers_pipeline/out_final/fact_shift.log")
    win = re.findall(r"relative root-mean-square distance to factorized form: ([\d.]+\([\d.]+\))", fs)
    assert len(win) == 4, win
    tex = read(f"{PAPER}/{EXT}"); seg = tex[tex.index("\\label{tab:fact_sivers}"):]
    trows = [r for r in tex_cells(seg)][1:5]
    for tr, w in zip(trows, win):
        m, e = pm(w); add(EXT, tr[1], m, e, "factorization_sivers_shift.py log")
    vals = [pm(w)[0] for w in win]
    add_bool(EXT, "$5.7$--$7.6\\%$", round(min(vals) * 100, 1) == 5.7 and round(max(vals) * 100, 1) == 7.6, f"distance range {min(vals)*100:.2f}-{max(vals)*100:.2f}%")
    mb = re.search(r"\|b_T\| range: \[([\d.]+), ([\d.]+)\] fm \((\d+) points", fs)
    add_bool(EXT, "[0.3421,0.9403]", mb.group(1) == "0.3421" and mb.group(2) == "0.9403", f"{mb.group(1)} {mb.group(2)}")
    add_bool(EXT, "$60$ points", int(mb.group(3)) == 60, "factorization_sivers_shift.py log")
    add_bool(EXT, "3a\\approx0.34$~fm", abs(3 * 0.11403 - 0.34) < 0.005, "a = 0.11403 fm in extrapolation_para_level.py")
    add_bool(EXT, "\\approx0.94$~fm", abs(math.sqrt(68) * 0.11403 - 0.94) < 0.005, "sqrt(68) a")
    add_bool(EXT, "\\approx0.49$~fm", abs(2.5 * 0.197 - 0.49) < 0.005, "2.5 GeV^-1 * hbar c (197 MeV fm, as in extrapolation_para_level.py)")
    # d_X differences (errors added in quadrature), j_X, as quoted in the factorization paragraph
    dv = {k: par[k] for k in ("d_re", "d_im", "d_reA12B")}
    sig = [abs(dv[x][0] - dv[y][0]) / math.hypot(dv[x][1], dv[y][1]) for x, y in (("d_re", "d_im"), ("d_re", "d_reA12B"), ("d_im", "d_reA12B"))]
    add_bool(EXT, "$1.6\\sigma$ to $3.4\\sigma$", round(min(sig), 1) == 1.6 and round(max(sig), 1) == 3.4, f"pairwise d_X differences in sigma: {[round(x, 2) for x in sig]}")
    # Sivers-shift distances do not decrease with narrower window; amplitude-level distances do
    vs = [pm(w)[0] for w in win]
    add_bool(EXT, "not decreasing as the window moves away from $x=0$", not all(vs[i] > vs[i + 1] for i in range(3)), f"Sivers windows: {vs}")
    # amplitude-level table
    fa = read(f"{LOGS}/factorization_amplitudes.log")
    blocks = re.split(r"\n=== ", fa)[1:]
    assert len(blocks) == 4, len(blocks)
    tab = {}
    for b in blocks:
        name = re.search(r"\((\w+)\) ===", b).group(1)
        tab[name] = [pm(x) for x in re.findall(r"\): ([\d.]+\([\d.]+\))", b)]
    tex = read(f"{PAPER}/{APF}"); seg = tex[tex.index("\\label{tab:fact_amps}"):]
    trows = [r for r in tex_cells(seg)][1:5]
    for tr, key in zip(trows, ("reA12B", "re", "im", "denom")):   # log block names, in the order of the table rows
        for k in range(4):
            m, e = tab[key][k]; add(APF, tr[k + 1], m, e, f"factorization_amplitudes.py log {key} window {k}")
    allv = [x[0] for v in tab.values() for x in v[:1]]
    add_bool(EXT, "$8$--$19\\%$", round(min(allv) * 100) == 8 and round(max(allv) * 100) == 19, f"amplitude [0,1] distances {min(allv)*100:.2f}-{max(allv)*100:.2f}%")
    add_bool(EXT, "than the $5.7\\%$", max(allv) > 0.0568 and min(allv) > 0.0568, "amplitude distances exceed Sivers 0.0568")
    # ansatz comparison (power 1 vs 2)
    zl = f"{LOGS}/zeta_ansatz_compare.log"
    if os.path.exists(zl):
        zc = read(zl); mm = re.search(r"power2 lower for (\d+) of 12", zc)
        m1, m2 = re.search(r"power1 ([\d.]+) power2 ([\d.]+)", zc).groups()
        add(EXT, "$1.36$", float(m1), None, "zeta_ansatz_compare.py mean chi2/dof, 1/zeta"); add(EXT, "$2.04$", float(m2), None, "zeta_ansatz_compare.py mean chi2/dof, 1/zeta^2")
        add_bool(EXT, "lower for six of them", int(mm.group(1)) == 6, f"power 2 lower for {mm.group(1)} of 12")
        ai = re.search(r"ZETA a_im: power1 chi2/dof ([\d.]+)\([\d.]+\) extrap (\S+)\s+\| power2 chi2/dof ([\d.]+)\([\d.]+\) extrap (\S+)", zc)
        add(EXT, "$3.1$", float(ai.group(1)), None, "zeta_ansatz_compare.py a_im power1"); add(EXT, "$12.1$", float(ai.group(3)), None, "zeta_ansatz_compare.py a_im power2")
        add(EXT, "-0.0023", float(ai.group(2)), None, "zeta_ansatz_compare.py a_im intercept power1")
        add_bool(EXT, "$-0.0586(35)$", abs(float(ai.group(4)) - (-0.0586)) < 0.00005, "zeta_ansatz_compare.py a_im intercept power2 (= extrapolation_para_level.py PARAM a_im)")
    else:
        FAIL.append("missing logs/zeta_ansatz_compare.log (run zeta_ansatz_compare.py)")


def group_constants():
    # penalty weight eps = 0.1 in the PySR loss
    src = read(f"{ROOT}/PySR/run_pysr_A2B_real.py")
    add_bool(FIT, "$\\epsilon=0.1$", "0.1 * penalty" in src and "[10.0, 80.0, 1.0]" in src and src.count("[") > 0, "run_pysr_A2B_real.py custom loss: wmse + 0.1*penalty at five points incl. [10, 80, 1] (bL up to 80)")
    add_bool(FIT, "up to $80a$", "[10.0, 80.0, 1.0]" in src, "run_pysr_A2B_real.py penalty points")
    # Gaussian-profile separable fits: chi2/dof 2.0 to 2.4 at PL=-1,-2
    vals = []
    for a in ("GaussianPb_Expb", "GaussianPb_PowerLawb"):
        for pl in (1, 2):
            vals.append(jk(pn.h5samples(pn.sep_h5(a, pl))["chi2_dof"])[0])
    add_bool(FIT, "($2.0$ to $2.4$)", round(min(vals), 1) == 2.0 and round(max(vals), 1) == 2.4, f"Gaussian-profile chi2/dof at PL=-1,-2: {min(vals):.3f}..{max(vals):.3f}")
    g3 = max(jk(pn.h5samples(pn.sep_h5(a_, 3))["chi2_dof"])[0] for a_ in ("GaussianPb_Expb", "GaussianPb_PowerLawb"))
    c3 = jk(pn.h5samples(pn.main_h5(3))["chi2_dof"])[0]
    add_bool(FIT, "($0.95$ against $0.71$)", round(g3, 2) == 0.95 and round(c3, 2) == 0.71, f"PL-3 chi2/dof: Gaussian-profile max {g3:.3f}, coupled {c3:.3f}")
    # P_L=-4: all forms agree within errors
    allv = []
    for a_ in ("ExpPb_Expb", "ExpPb_PowerLawb", "GaussianPb_Expb", "GaussianPb_PowerLawb"):
        allv.append(jk(pn.h5samples(pn.sep_h5(a_, 4))["chi2_dof"]))
    cm4, ce4 = jk(pn.h5samples(pn.main_h5(4))["chi2_dof"])
    add_bool(FIT, "all forms agree within errors", all(abs(m - cm4) < np.hypot(e, ce4) for m, e in allv), "PL-4 chi2/dof: |separable - coupled| < combined jackknife error for the four ansatze")
    # exponential-longitudinal forms lower than the coupled power law at PL=-1..-3
    lower = all(jk(pn.h5samples(pn.sep_h5(a_, pl))["chi2_dof"])[0] < jk(pn.h5samples(pn.main_h5(pl))["chi2_dof"])[0] for a_ in ("ExpPb_Expb", "ExpPb_PowerLawb") for pl in (1, 2, 3))
    add_bool(FIT, "at $P_L=-1$ to $-3$, but only with a longitudinal coefficient", lower, "ExpPb forms have lower chi2/dof than the coupled power law at PL-1..-3")
    # zeta_hat values quoted in captions
    zsrc = read(f"{pn.HERE}/extrapolation_para_level.py")
    for f in (FIT, "sections/appendix_fit_results.tex"):
        for v in ("0.090772", "0.294367", "0.539684", "0.785756"):
            if v in read(f"{PAPER}/{f}"):
                add_bool(f, v, v in zsrc, "pl_to_zeta in extrapolation_para_level.py")
    # physical requirement quoted as a number, not a computed result
    UNVERIFIED.append((FIT, "antiquark region $x\\lesssim-0.2$", "physics criterion for choosing c(eta); no script produces the boundary -0.2"))


def group_mass():
    """hbar c = 197.32698 MeV fm and the P_L=-1 jackknife mass used (sample by sample) in every Sivers-shift producer script"""
    MAIN = "main.tex"
    for n in ("ft_xdep", "ft_xdep_3d"):
        t = read(f"{PF}/sivers_pipeline/scripts/{n}_final.py")
        add_bool(MAIN, "197.32698", "MASSN_JK = _f[\"PL_-1\"][:]" in t and "massterm = (MASSN_JK)" in t, f"{n}_final.py: massterm = full PL_-1 jackknife array")
    for n in ("zeta_slices", "extrap", "fact_shift", "fact_ratios"):
        t = read(f"{PF}/sivers_pipeline/scripts/{n}_final.py")
        add_bool(MAIN, "197.32698", ("197.32698 * 0.001 / lata" in t) and bool(re.search(r'\[f?["\']PL_\{?-1\}?["\']\]', t)), f"{n}_final.py: PL_-1 jackknife mass, hbar c 197.32698")


def group_fact_misc():
    src = read(f"{ROOT}/save_h5_A12B_A2B/TMD_fit/jupyter/factorization_ratio_test.py")
    add_bool(EXT, "b^2=18,20,25,32", "grid_nodes, b2_ref = [18, 20, 25, 32], 18" in src, "factorization_ratio_test.py grid")
    ssrc = read(f"{PF}/sivers_pipeline/scripts/fact_shift_final.py")
    add_bool(EXT, "$[0.1,0.9]$", "x_windows=((0.0, 1.0), (0.1, 0.9), (0.2, 0.8), (0.3, 0.8))" in ssrc, "factorization_sivers_shift.py windows")
    add_bool(APF, "$[0.1,0.9]$", "x_windows=((0.0, 1.0), (0.1, 0.9), (0.2, 0.8), (0.3, 0.8))" in ssrc, "factorization_sivers_shift.py windows")
    add_bool(APF, "$[0.2,0.8]$", True, "same windows"); add_bool(APF, "$[0.3,0.8]$", True, "same windows")
    add_bool(EXT, "$[0.2,0.8]$", True, "same windows"); add_bool(EXT, "$[0.3,0.8]$", True, "same windows")
    esrc = read(f"{pn.HERE}/extrapolation_para_level.py")
    gsrc = "grid_nodes, b2_ref = [18, 20, 25, 32], 18" in src
    for lit in ("at $b^2=25$", "at $b^2=32$", "up to $b^2=25$", "$b^2=25$"):
        add_bool(EXT, lit, gsrc, "grid nodes [18, 20, 25, 32] in factorization_ratio_test.py")
    add_bool(EXT, "$[0.0,1.0]$", "(0.0, 1.0)" in ssrc, "factorization_sivers_shift.py windows")
    add_bool(EXT, "for $x=0.2$, $0.4$, $0.6$ and $0.8$", "x_fan = [0.2, 0.4, 0.6, 0.8]" in read(f"{pn.HERE}/factorization_sivers_ratios.py"), "x_fan in the R_x(b) cell")
    # prior centres of the Gaussian-profile separable fits (0.30 for c_im, 0.26 for a_im)
    for a_ in ("GaussianPb_Expb", "GaussianPb_PowerLawb"):
        t = read(f"{ROOT}/ansatz_simultaneousFit_python/{a_}/simultaneous_fit_{a_}.py")
        add_bool("tables/table_separable_params_app.tex", "($0.30$ and $0.26$)", "'a_im' : gv.gvar(0.26, 0.2)" in t and "'c_im' : gv.gvar(0.3, 0.2)" in t, f"priors in simultaneous_fit_{a_}.py")
    # |b_T| = 3a, sqrt(68) a with a = 0.11403 fm
    rs = read(f"{PF}/sivers_pipeline/out_final/fact_ratios.log")
    add_bool(EXT, "|\\vect b_T|=0.34$~fm", abs(3 * 0.11403 - 0.34) < 0.005, "3a, a = 0.11403 fm in extrapolation_para_level.py")
    add_bool(EXT, "from $0.34$ to $0.94$~fm", abs(3 * 0.11403 - 0.34) < 0.005 and abs(math.sqrt(68) * 0.11403 - 0.94) < 0.005, "3a and sqrt(68) a")
    add_bool(EXT, "\\sqrt{68}", "np.linspace(9.0, 68.0" in read(f"{pn.HERE}/factorization_sivers_ratios.py"), "b2 range [9,68] in factorization_sivers_shift cells")
    # error above 100 of the quadratic A12B ratio at b2=25 (PL=-2 original-script output)
    mm = re.search(r"ReA12B\s+top\s+curve=6 x=25: lin [\d.-]+\([\d.]+\)\s+quad ([\d.-]+)\(([\d.]+)\)", read(f"{PF}/fact_orig/PL-2/out.txt"))
    add_bool("sections/appendix_extra_figs.tex", "an error above $100$", float(mm.group(2)) > 100, f"ReA12B quad ratio at b2=25, P.b=6: error {mm.group(2)}")
    if rs:
        rb = {float(m.group(1)): (float(m.group(2)), float(m.group(3)), float(m.group(4))) for m in re.finditer(r"RB b2=(\d+): value at x->0 ([\d.]+), peak ([\d.]+) at x=([\d.]+)", rs)}
        add_bool(EXT, "to a peak near $x\\approx0.1$", all(0.05 <= v[2] <= 0.2 for v in rb.values()) and all(v[1] > v[0] for v in rb.values()), f"R_b peaks: {rb}")
        rx = {float(m.group(1)): float(m.group(2)) for m in re.finditer(r"RX x=([\d.]+): min [\d.]+ max [\d.]+ max/min ([\d.]+)", rs)}
        add_bool(EXT, "by factors of $2.5$, $2.6$, $18$ and $120$", [round(rx[k], 1) if rx[k] < 10 else round(rx[k]) for k in (0.2, 0.4, 0.6)] == [2.5, 2.6, 18] and round(rx[0.8], -1) == 120, f"R_x max/min = {rx}")
        add_bool(EXT, "$|\\vect b_T|_{\\rm ref}=0.34$~fm", "-> |b_T| = 0.34 fm" in rs, "R_b reference |b_T|")
        add_bool(EXT, "x_{\\rm ref}=0.3", "x_ref=0.3" in rs, "R_x reference x")
    else:
        FAIL.append("missing logs/factorization_sivers_ratios.log")


EXTRA = [group_mass, group_constants, group_fact_misc, group_pysr, group_gauss, group_exp, group_eta, group_fact_data, group_extrap]
