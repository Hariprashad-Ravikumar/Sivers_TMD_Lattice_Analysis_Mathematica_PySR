#!/opt/homebrew/anaconda3/bin/python
"""Runs the pipeline's fact_shift_final.py and fact_ratios_final.py unchanged and appends code that saves the arrays behind the factorization figures
(g(x), h(b_T), reconstruction; R_b(x); R_x(b)) to npz files, so the single panels of the paper can be drawn from them."""
import os, subprocess
HERE = os.path.dirname(os.path.abspath(__file__)); PF = os.path.dirname(HERE)
OUT = f"{HERE}/out/factshift"; os.makedirs(OUT, exist_ok=True)
SH = '''
_o = {}
for _w, _r in factorization_results.items():
    _tag = "%g_%g" % _w
    _o["x_" + _tag] = _r["x_grid"]; _o["b_" + _tag] = _r["bT_grid"]
    _o["g_" + _tag] = np.array(jk_stats(_r["g_jk"], axis=0)); _o["h_" + _tag] = np.array(jk_stats(_r["h_jk"], axis=0))
_r = factorization_results[(0.0, 1.0)]
for _k, _ib in (("lo", 0), ("hi", -1)):
    _bt = _r["bT_grid"][_ib]; _b2 = (_bt / lata) ** 2
    _o["bt_" + _k] = _bt
    _o["act_" + _k] = np.array(jk_stats(eval_obs_jk(extrapolated_jk, _r["x_grid"], _b2, massterm)["siv"], axis=0))
    _o["rec_" + _k] = np.array(jk_stats(_r["g_jk"] * _r["h_jk"][:, [_ib]], axis=0))
np.savez(OUTD + "/fact_gh.npz", **_o)
print("FACT_GH SAVED")
'''
RA = '''
_o = {"x1": x_grid_fig1, "bref": bT_ref_fm, "xref": x_ref, "b2": bT_grid_fig2}
for _b2 in b2_fan:
    _o["Rb_%g" % _b2] = np.array(jk_stats(eval_obs_jk(extrapolated_jk, x_grid_fig1, _b2)["siv"] / obs_ref, axis=0))
for _x in x_fan:
    _o["Rx_%g" % _x] = np.array(jk_stats(eval_siv_over_b2(_x, b2_grid_fig2) / obs_ref_b, axis=0))
np.savez(OUTD + "/fact_ratios.npz", **_o)
print("FACT_RATIOS SAVED")
'''
env = dict(os.environ, OMP_NUM_THREADS="2", MPLBACKEND="Agg", PYTHONUNBUFFERED="1")
for name, add in (("fact_shift", SH), ("fact_ratios", RA)):
    s = open(f"{PF}/sivers_pipeline/scripts/{name}_final.py").read()
    f = f"{OUT}/{name}_dump.py"; open(f, "w").write(f'OUTD = "{OUT}"\n' + s + "\n" + add)
    with open(f"{OUT}/{name}.log", "w") as lg:
        r = subprocess.run(["/opt/homebrew/anaconda3/bin/python", "-u", f], cwd=OUT, stdout=lg, stderr=subprocess.STDOUT, env=env)
    print(name, r.returncode, flush=True)
