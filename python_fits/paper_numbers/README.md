# Provenance of the numbers in the Sivers paper (fitting, extrapolation, appendices)

`python paper_numbers.py check` recomputes or reads every quoted number from saved script outputs and compares it, at the quoted
precision, with the paper text/tables (`ERR` on any mismatch). `coverage` lists numbers in the in-scope files that no claim covers.
Claims that no script can produce are printed at the end of `check` (currently only the x = -0.2 physics criterion).

Script runs behind the numbers (logs in `../logs`, outputs in `../paper_out/PL2`, `../fact_orig`):

| numbers | script (run log) |
|---|---|
| simultaneous / separable fit parameters, chi2/dof | saved `FitParams_*.h5` (Python lsqfit notebooks); read by `paper_numbers.py` |
| PySR Pareto table | `PySR/run_pysr_A2B_real.py --pl 2` -> `outputs_A2B_real_PL2/hall_of_fame_summary.csv` |
| benchmark / Gaussian-straight / short-distance numbers | `PySR/make_paper_PL_figs.py --pl 2` (`logs/make_paper_PL_figs_PL2.log`) |
| exponential straight-line test | `PySR/make_exp_straight_PL.py --pl 2` (`logs/exp_straight_PL2.log`) |
| Gaussian family, power-law family, eta slices, slopes (tables) | `python_fits/paper_fits.py fit/slices/slopes/tables --pl 2` -> `paper_out/PL2` |
| eta=8 Gaussian profile (correlated chi2) | `python_fits/gauss_corr.py --pl 2` (`logs/gauss_corr_PL2.log`) |
| independent-row chi2/dof | `paper_numbers/independent_rows.py` (`logs/independent_rows_PL2.log`) |
| factorization of the lattice data | `python_fits/factorization_ratio_test_PLscaled.py --PL -1/-2` (`fact_orig/PL-*/out.txt`); original: `save_h5_A12B_A2B/TMD_fit/jupyter/factorization_ratio_test.py` |
| parameter extrapolation, x-integrals, Sivers peaks | `paper_numbers/extrapolation_para_level.py` (`logs/extrapolation_run.log`; stopped by hand at the final overlay plot, after all numbers were printed) |
| extrapolation ansatz comparison (1/zeta vs 1/zeta^2) | `paper_numbers/zeta_ansatz_compare.py` (`logs/zeta_ansatz_compare.log`) |
| factorization of the extrapolated Sivers shift / amplitudes | `paper_numbers/factorization_sivers_shift.py`, `factorization_amplitudes.py`, `factorization_sivers_ratios.py` (logs) |

`nb_to_script.py` extracts notebook cells verbatim (patches are marked `[paper_numbers patch]`).
