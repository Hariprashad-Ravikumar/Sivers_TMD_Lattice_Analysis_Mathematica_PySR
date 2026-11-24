#!/opt/homebrew/anaconda3/bin/python
"""Provenance + checker for the numbers quoted in the Sivers paper (fitting, extrapolation and appendices).

Every claim is (tex file, literal as typed in the paper, value computed here from saved data / script logs, error, source).
`python paper_numbers.py check`  recomputes all values, compares them with the literals AND checks that each literal occurs in the tex.
`python paper_numbers.py list`   prints the manifest (paper_numbers_manifest.json is also written).
Nothing here reruns a Mathematica fit or the simultaneous fits: those enter through the saved FitParams h5 files.
Sources (all Python): h5 FitParams (simultaneous / separable fits), PySR hall-of-fame csv, make_paper_PL_figs.py, make_exp_straight_PL.py,
paper_fits.py (+ paper_out/PL2), gauss_corr.py, the original factorization_ratio_test.py (scaled copy), and the extrapolation/factorization
notebooks converted to scripts (nb_to_script.py) whose run logs are in python_fits/logs.
"""
import os, re, sys, json, math, csv
import numpy as np

PAPER = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/Lattice_QCD_TMD_Sivers_paper"
ROOT = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project"
H5 = f"{ROOT}/save_h5_A12B_A2B"
PF = f"{ROOT}/python_fits"
LOGS = f"{PF}/logs"
HERE = os.path.dirname(os.path.abspath(__file__))

CLAIMS = []          # dicts
FAIL = []
UNVERIFIED = []      # (file, literal, reason): quoted but not computed by any script


def add(file, literal, m, e=None, src=""):
    CLAIMS.append(dict(file=file, literal=literal, value=None if m is None else float(m), err=None if e is None else float(e), src=src))


# ------------------------------------------------------------------------------------------------------------------
# literal parsing: "3.9833(80)" -> mean 3.9833 (4 decimals), err digits 80 ; "93.9(2.4)" -> err 2.4 ; "1.24" ; "$-0.0017(7)$"
# ------------------------------------------------------------------------------------------------------------------
def parse_lit(lit):
    """last number in the literal: mean, decimals, absolute error (or None), scale (10^exp)"""
    s = lit.replace("$", "").replace("{", "").replace("}", "").replace("\\!", "").replace("\u2212", "-").replace(" ", "")
    ms = list(re.finditer(r"([+-]?\d*\.?\d+)(?:\(([\d.]+)\))?(?:\\times10\^(-?\d+))?", s))
    if not ms:
        raise ValueError(f"cannot parse literal {lit!r}")
    m = ms[-1]
    mean = float(m.group(1)); dec = len(m.group(1).split(".")[1]) if "." in m.group(1) else 0
    sc = 10.0 ** int(m.group(3)) if m.group(3) else 1.0
    err = None; edec = dec
    if m.group(2) is not None:
        e = m.group(2)
        if "." in e:
            err = float(e); edec = len(e.split(".")[1])
        else:
            err = float(e) * 10.0 ** (-dec); edec = dec
    return mean * sc, dec, (None if err is None else err * sc), sc, edec


def check_claim(c, tex):
    lit = c["literal"]
    if lit == "(all cells)":
        return None
    if lit.strip("$") not in tex and lit not in tex:
        return f"literal {lit!r} not found in {c['file']}"
    if c["value"] is None:
        return None
    mean, dec, err, sc, edec = parse_lit(lit)
    v = c["value"]
    tol = 0.5 * 10.0 ** (-dec) * sc * (1 + 1e-9)
    if abs(v - mean) > tol:
        return f"{lit}: value {v:.8g} differs from the script value (rounding tolerance {tol:.2g})"
    if err is not None:
        if c["err"] is None:
            return f"{lit}: no error from the script"
        if abs(c["err"] - err) > 0.5 * 10.0 ** (-edec) * sc * (1 + 1e-9):
            return f"{lit}: error {c['err']:.6g} differs from the script error"
    return None


def jk(samples):
    s = np.asarray(samples, float)[..., 1:]
    n = s.shape[-1]
    m = s.mean(-1)
    return m, np.sqrt((n - 1) / n * ((s - m[..., None]) ** 2).sum(-1))


# ------------------------------------------------------------------------------------------------------------------
# G1: simultaneous-fit and separable-fit tables (saved h5 from the Python lsqfit notebooks)
# ------------------------------------------------------------------------------------------------------------------
def h5samples(path):
    import h5py
    f = h5py.File(path, "r")
    d = {k: f["jackknife_samples/" + k][:] for k in f["jackknife_samples"]}
    d["chi2_dof"] = f["chi2_dof"][:]
    return d


def main_h5(pl):
    return f"{H5}/SimultaniousFit/FitParams_SimulFit_f_A2BRe_cetasq_A2BIm_A12BRe_bmin3_eta610_PL-{pl}.h5"


def sep_h5(a, pl):
    return f"{H5}/h5data/FitParams_SimulFit_{a}_bmin3_eta610_PL-{pl}.h5"


def tex_cells(text):
    """rows of a tabular as lists of stripped cells"""
    rows = []
    for ln in text.splitlines():
        if "&" in ln and ln.rstrip().endswith("\\\\"):
            rows.append([c.strip() for c in ln.rstrip()[:-2].split("&")])
    return rows


def group_h5():
    names = {"a": ["a_re", "a_im", "a_reA12B"], "c": ["c_re", "c_im", "c_reA12B"], "d": ["d_re", "d_im", "d_reA12B"], "j": ["j_re", "j_im", "j_reA12B"]}
    P = {pl: h5samples(main_h5(pl)) for pl in (1, 2, 3, 4)}
    # appendix table (P_L=-1,-3,-4) rows in file order
    f = "sections/appendix_fit_results.tex"
    tex = open(f"{PAPER}/{f}").read()
    rows = [r for r in tex_cells(tex[tex.index("tab:fit_params"):]) if len(r) == 4][1:]   # drop the header row
    order = ["a_re", "c_re", "d_re", "k1_re", "k2_re", "j_re", "a_im", "c_im", "d_im", "j_im", "a_reA12B", "c_reA12B", "d_reA12B", "j_reA12B", "f"]
    assert len(rows) == 16, len(rows)
    for key, r in zip(order, rows[:15]):
        for k, pl in enumerate((1, 3, 4)):
            m, e = jk(P[pl][key])
            add(f, r[k + 1], m, e, f"h5 {os.path.basename(main_h5(pl))}:{key}")
    for k, pl in enumerate((1, 3, 4)):
        m, e = jk(P[pl]["chi2_dof"])
        add(f, rows[15][k + 1], m, e, f"h5 chi2_dof PL-{pl}")
    # main-text table at PL=-2
    f = "sections/analysis_fitting.tex"
    tex = open(f"{PAPER}/{f}").read()
    seg = tex[tex.index("tab:fit_params_P2"):]
    rows = [r for r in tex_cells(seg) if r[0].startswith("$") and len(r) in (4, 2)][:9]
    # rows: a, c, d, k1, k2, j with 3 columns; f as multicolumn
    keymap = [("a_re", "a_im", "a_reA12B"), ("c_re", "c_im", "c_reA12B"), ("d_re", "d_im", "d_reA12B"), ("k1_re", None, None), ("k2_re", None, None), ("j_re", "j_im", "j_reA12B")]
    for r, ks in zip(rows[:6], keymap):
        for cell, k in zip(r[1:4], ks):
            if k is None:
                continue
            m, e = jk(P[2][k]); add(f, cell, m, e, f"h5 PL-2:{k}")
    m, e = jk(P[2]["f"]); add(f, "$0.5357(66)$", m, e, "h5 PL-2:f")
    m, e = jk(P[2]["chi2_dof"]); add(f, "$1.197(85)$", m, e, "h5 chi2_dof PL-2")
    for pl, lit in ((1, "$1.85(10)$"), (3, "$0.712(66)$"), (4, "$0.434(51)$")):
        m, e = jk(P[pl]["chi2_dof"]); add(f, lit, m, e, f"h5 chi2_dof PL-{pl}")
    # separable ansaetze: chi2 block and PL=-2 key parameters
    seps = [("ExpPb_Expb", r"ExpPb\_Expb"), ("ExpPb_PowerLawb", r"ExpPb\_PowerLawb"), ("GaussianPb_Expb", r"GaussianPb\_Expb"),
            ("GaussianPb_PowerLawb", r"GaussianPb\_PowerLawb"), ("COUPLED", "Coupled power law")]
    i0 = tex.index("\\label{tab:separable}"); seg = tex[i0:tex.index("\\end{table}", i0)]
    cells = {r[0]: r for r in tex_cells(seg)}
    top = [r for r in tex_cells(seg) if r[0] in [s[1] for s in seps]]
    assert len(top) == 10, len(top)
    for (a, lab), r in zip(seps, top[:5]):
        for k, pl in enumerate((1, 2, 3, 4)):
            d = h5samples(main_h5(pl) if a == "COUPLED" else sep_h5(a, pl)); m, e = jk(d["chi2_dof"])
            add(f, r[k + 1], m, e, f"h5 chi2_dof {a} PL-{pl}")
    for (a, lab), r in zip(seps, top[5:]):
        d = h5samples(main_h5(2) if a == "COUPLED" else sep_h5(a, 2))
        for cell, k in zip(r[1:4], ("c_im", "c_reA12B", "a_im")):
            m, e = jk(d[k]); add(f, cell, m, e, f"h5 {a} PL-2:{k}")
    # appendix separable table (PL=-1,-3,-4)
    f2 = "tables/table_separable_params_app.tex"
    tex2 = open(f"{PAPER}/{f2}").read()
    blocks = [r for r in tex_cells(tex2) if r[0] in [s[1] for s in seps]]
    assert len(blocks) == 15, len(blocks)
    for bi, pl in enumerate((1, 3, 4)):
        for (a, lab), r in zip(seps, blocks[5 * bi:5 * bi + 5]):
            d = h5samples(main_h5(pl) if a == "COUPLED" else sep_h5(a, pl))
            for cell, k in zip(r[1:4], ("c_im", "c_reA12B", "a_im")):
                m, e = jk(d[k]); add(f2, cell, m, e, f"h5 {a} PL-{pl}:{k}")
    # prose in the separable paragraph: Gaussian-profile fits at PL=-3,-4 sit at the prior centres 0.30/0.26 (within 0.002)
    dev = 0.0
    for a in ("GaussianPb_Expb", "GaussianPb_PowerLawb"):
        for pl in (3, 4):
            d = h5samples(sep_h5(a, pl)); dev = max(dev, abs(jk(d["c_im"])[0] - 0.30), abs(jk(d["a_im"])[0] - 0.26))
    add(f2, "$0.002$", None, None, f"max |value-prior centre| = {dev:.5f} (must be < 0.002)")
    if dev >= 0.002:
        FAIL.append(f"Gaussian-profile fits deviate {dev} from prior centres, caption says 0.002")


# ------------------------------------------------------------------------------------------------------------------
# G2: python_fits/paper_out generated tables must be byte-identical to the paper tables
# ------------------------------------------------------------------------------------------------------------------
def group_generated_tables():
    """the two tables are written by `paper_fits.py tables` from the saved fit outputs (npz/json of the fit/slices/slopes runs);
    regenerate them now and require the cell contents to equal the paper's"""
    import subprocess, shutil, tempfile
    env = dict(os.environ, OMP_NUM_THREADS="1")
    r = subprocess.run(["/opt/homebrew/anaconda3/bin/python", f"{PF}/paper_fits.py", "tables", "--pl", "2", "--fixed", "seq"], capture_output=True, text=True, env=env)
    if r.returncode != 0:
        FAIL.append("paper_fits.py tables failed: " + r.stderr[-300:])
    r2 = subprocess.run(["/opt/homebrew/anaconda3/bin/python", f"{PF}/paper_fits_separable.py", "tables", "--pl", "2"], capture_output=True, text=True, env=env)
    if r2.returncode != 0:
        FAIL.append("paper_fits_separable.py tables failed: " + r2.stderr[-300:])
    for name in ("table_gauss_family_PL2.tex", "table_powerlaw_family_PL2.tex", "table_sep_EE_PL2.tex", "table_sep_PE_PL2.tex", "table_sep_EP_PL2.tex"):
        a = open(f"{PF}/paper_out/PL2/{name}").read()
        b = open(f"{PAPER}/tables/{name}").read()
        ca, cb = [c for r_ in tex_cells(a) for c in r_], [c for r_ in tex_cells(b) for c in r_]
        if ca != cb:
            FAIL.append(f"table {name}: cell content differs from the paper_fits.py output")
        CLAIMS.append(dict(file=f"tables/{name}", literal="(all cells)", value=None, err=None, src=f"paper_fits.py tables == paper table, {len(cb)} cells"))


def run_check(files_cache={}):
    for c in CLAIMS:
        tex = files_cache.setdefault(c["file"], open(f"{PAPER}/{c['file']}").read())
        msg = check_claim(c, tex)
        if msg:
            FAIL.append(f"{c['file']}: {msg}")


GROUPS = [group_h5, group_generated_tables]

SCOPE = ["sections/analysis_fitting.tex", "sections/analysis_extrapolation.tex", "sections/appendixC.tex", "sections/appendix_fit_results.tex",
         "sections/appendix_factorization.tex", "tables/table_separable_params_app.tex"]   # the four paper_fits tables are checked cell by cell


def coverage():
    """numbers in the in-scope tex files that are not inside any claim literal (candidates for 'no script'); labels/refs are skipped"""
    skip = [r"%[^\n]*", r"\\(?:label|ref|eqref|cite|input|includegraphics|begin|end)(?:\[[^\]]*\])?\{[^}]*\}", r"\\(?:tabcolsep|hspace|setlength)\{[^}]*\}",
            r"\\paragraph\{[^}]*\}", r"\\(?:sub)*section\{[^}]*\}", r"\[[-\d.]+(?:ex|pt|em)\]"]
    unc = {}
    for f in SCOPE:
        tex = open(f"{PAPER}/{f}").read()
        cov = np.zeros(len(tex), bool)
        for c in CLAIMS:
            if c["file"] != f:
                continue
            for lit in {c["literal"], c["literal"].strip("$")}:
                for m in re.finditer(re.escape(lit), tex):
                    cov[m.start():m.end()] = True
        for pat in skip:
            for m in re.finditer(pat, tex):
                cov[m.start():m.end()] = True
        for m in re.finditer(r"(?<![\w.])(\d+(?:\.\d+)?)(?![\w])", tex):
            tok = m.group(1)
            if "." not in tok and int(tok) < 20:   # structural integers (exponents, indices, P_L=-N, C=N, eta values) are skipped
                continue
            if not cov[m.start():m.end()].all():
                ln = tex.count("\n", 0, m.start()) + 1
                unc.setdefault(f, []).append((ln, m.group(1), tex[max(0, m.start() - 45):m.end() + 30].replace("\n", " ")))
    n = 0
    for f, lst in unc.items():
        print(f"== {f}: {len(lst)} uncovered numeric tokens")
        for ln, tok, ctx in lst:
            print(f"  {ln:4d} {tok:>8}  ...{ctx}...")
        n += len(lst)
    print(f"{n} uncovered tokens in total")


def main():
    cmd = sys.argv[1] if len(sys.argv) > 1 else "check"
    sys.path.insert(0, HERE)
    import extra_groups                # imported here (not at module level) to avoid a circular import
    for g in GROUPS + extra_groups.EXTRA:
        g()
    run_check()
    json.dump(CLAIMS, open(f"{HERE}/paper_numbers_manifest.json", "w"), indent=1)
    if cmd == "coverage":
        coverage()
        return
    if cmd == "list":
        for c in CLAIMS:
            print(c["file"], c["literal"], c["value"], c["err"], c["src"])
    print(f"{len(CLAIMS)} claims checked, {len(FAIL)} failures")
    if UNVERIFIED:
        print("NOT reproducible by a script (criteria / read-off values), listed for the author:")
        for f_, l_, why in UNVERIFIED:
            print(f"  {f_}: {l_}  -- {why}")
    for f in FAIL:
        print("FAIL:", f)
    sys.exit(1 if FAIL else 0)


if __name__ == "__main__":
    import paper_numbers as _pn      # run through the importable module so that extra_groups and this file share one CLAIMS list
    _pn.main()
