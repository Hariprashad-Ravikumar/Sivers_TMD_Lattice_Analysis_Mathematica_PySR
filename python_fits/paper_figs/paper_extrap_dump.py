#!/opt/homebrew/anaconda3/bin/python
"""Runs the pipeline's extrap_final.py (patched mass jackknife, hbar c = 197.32698) with data-dump hooks inserted, so that the paper panels can be drawn
from the saved arrays: parameter extrapolations, extrapolated curves at b^2=9, 3D grids. Nothing in the computation is changed."""
import os, subprocess, re
HERE = os.path.dirname(os.path.abspath(__file__)); PF = os.path.dirname(HERE)
src = open(f"{PF}/sivers_pipeline/scripts/extrap_final.py").read()
OUT = f"{HERE}/out/extrap"; os.makedirs(OUT, exist_ok=True)
def ins_after(s, anchor, code, count=1):
    i = s.index(anchor); j = s.index("\n", i) + 1
    return s[:j] + code + s[j:]
# 1. parameter dump
src = ins_after(src, "plot_x = np.linspace(0, max(inv_zeta_vals)*1.1, 50)", "    _PD = {}\n")
src = ins_after(src, 'print(f"PARAM {p_name} extrapolated', "        _PD[p_name] = dict(x=inv_zeta_vals, y=y_means, e=np.array(y_errs), px=plot_x, fm=fit_m, fe=fit_e, c0=c0_m, c0e=c0_e, chi=np.array(Jackknife(chi2)))\n")
src = ins_after(src, "    plt.tight_layout()\n", "")  # no-op anchor check
src = src.replace('    plt.savefig(f"Param_Extrapolations', '    np.savez(OUTD + "/params.npz", **{f"{k}__{kk}": vv for k, v in _PD.items() for kk, vv in v.items()})\n    plt.savefig(f"Param_Extrapolations', 1)
# 2. extrapolated 2D curves
src = ins_after(src, "    print(f\"SIVERS peak <k_y>", "    np.savez(OUTD + '/curves.npz', x=x_vals, reA2B=np.array([reA2B_m, reA2B_e]), imA2B=np.array([imA2B_m, imA2B_e]), f1=np.array([A2B_m, A2B_e]), f1T=np.array([reA12B_m, reA12B_e]), ky=np.array([siv_m, siv_e]), xky=np.array([xsiv_m, xsiv_e]))\n")
# 3. 3D grids, then stop
src = src.replace("    # 4. Plotting in 3D\n", "    np.savez(OUTD + '/grid3d.npz', x=x_vals, b2=b2_vals, re=np.array([re_mean_2d, re_err_2d]), im=np.array([im_mean_2d, im_err_2d]), f1=np.array([full_mean_2d, full_err_2d]), f1T=np.array([reA12B_mean_2d, reA12B_err_2d]), ky=np.array([SiverseShift_mean_2d, SiverseShift_err_2d]), xky=np.array([xSiverseShift_mean_2d, xSiverseShift_err_2d]))\n    print('GRID3D SAVED'); import sys; sys.exit(0)\n", 1)
src = f'OUTD = "{OUT}"\n' + src
f = f"{OUT}/extrap_dump.py"; open(f, "w").write(src)
env = dict(os.environ, OMP_NUM_THREADS="2", MPLBACKEND="Agg", PYTHONUNBUFFERED="1")
with open(f"{OUT}/dump.log", "w") as lg:
    r = subprocess.run(["/opt/homebrew/anaconda3/bin/python", "-u", f], cwd=OUT, stdout=lg, stderr=subprocess.STDOUT, env=env)
print("rc", r.returncode)
