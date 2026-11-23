#!/opt/homebrew/anaconda3/bin/python
"""Validation of the simultaneous-fit definition: notebook SimultaneousFit_A12bA2B.ipynb cell 4 (c = d + exp(log_delta_c), tight
priors on a,d,j,k1,k2,f) through lsqfit on a slice of the 2903 samples. Usage: validate_simul.py START STOP"""
import sys, re, json, h5py, numpy as np, gvar as gv, lsqfit
START, STOP = int(sys.argv[1]), int(sys.argv[2])
R = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/"
nb = json.load(open(R + "SimultaniousFit/SimultaneousFit_A12bA2B.ipynb")); src = ''.join(nb['cells'][4]['source'])
ns = {'np': np, 'gv': gv, 'h5py': h5py}
for name in ('load_and_filter_data', 'load_and_filter_data_rm_0_bL', 'ReA2B', 'ImA2B', 'ReA12B', 'fcn'):
    exec(re.search(r'^def %s\(.*?(?=^def |^# ---|\Z)' % name, src, re.S | re.M).group(0), ns)
exec(re.search(r'current_prior = \{.*?\n    \}', src, re.S).group(0).replace('current_prior', 'prior'), {'gv': gv}, ns)
kre, jre = ns['load_and_filter_data'](R + 'ReA2B_PL-1_jackknife_data.h5', 3, 6, 10)
kim, jim = ns['load_and_filter_data_rm_0_bL'](R + 'ImA2B_PL-1_jackknife_data.h5', 3, 6, 10)
k12, j12 = ns['load_and_filter_data'](R + 'ReA12B_PL-1_jackknife_data.h5', 3, 6, 10)
Nre, Nim = len(jre), len(jim); J = np.vstack([jre, jim, j12]); Ns = J.shape[1]
D = J - J.mean(1, keepdims=True); cov = (Ns-1)/Ns*D@D.T
x = {'Re': kre, 'Im': kim, 'ReA12B': k12}
out = []; P = []
for i in range(START, min(STOP, Ns)):
    yg = gv.gvar(J[:, i], cov)
    yd = {'Re': yg[:Nre], 'Im': yg[Nre:Nre+Nim], 'ReA12B': yg[Nre+Nim:]}
    fit = lsqfit.nonlinear_fit(data=(x, yd), prior=ns['prior'], fcn=ns['fcn'], debug=False)
    out.append(fit.chi2/fit.dof)
    p = fit.pmean; P.append([float(p['a_re']), float(p['d_re']+np.exp(p['log_delta_c_re'])), float(p['d_re']), float(p['j_re']), float(p['f']), float(p['k2_re'])])
np.save(R.replace('save_h5_A12B_A2B/', 'python_fits/') + f"logs/validate_{START}_{STOP}.npy", np.array(out))
print(START, STOP, 'chi2/dof mean', np.mean(out), 'dof', fit.dof, 'a_re,c_re,d_re,j_re,f,k2', np.round(np.mean(P, 0), 4))
