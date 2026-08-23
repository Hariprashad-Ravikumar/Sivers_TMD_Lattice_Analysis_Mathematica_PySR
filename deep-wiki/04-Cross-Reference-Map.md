# Deep Wiki — Cross-Reference Map

> **Last updated**: 2026-08-23

---

## 1. Mapping: Thesis Chapters ⟷ Code Notebooks & Scripts

| Thesis Chapter | Relevant Section | Supporting Code / Notebook / Script | Generated Output / Data File |
|----------------|------------------|------------------------------------|------------------------------|
| **Ch. 2: Lattice QCD Methodology** | Ratio Method ($R(t,\tau)$) | `mathematica_hari/include/LatticeAnalysis.m`, `Resampling2.m` | `sivers_new/stripped_*/UminusD_Plateaus_jn.bidatex` |
| **Ch. 3: Theoretical Framework** | Amplitude Decomposition ($\widetilde{A}_{2B}, \widetilde{A}_{12B}$) | `mathematica_hari/parametrization_ulink.nb`, `parametrization_ulink_v1v3_b1b2.nb` | `mathematica_hari/output/ratiostructures_ulink_full.m` |
| **Ch. 4: Extracting $x$-Dependence** | Kinematics & $\hat{\zeta}$ derivation | `mathematica_hari/Plots_for_Thesis_Kinematics.nb` | `thesis/plots/kinematics_interpolation/*.pdf` |
| **Ch. 4: Extracting $x$-Dependence** | Off-axis Link Interpolation ($\Delta v_1 = 0$) | `mathematica_hari/interpolation_v_TMD_x_plots_all_sideNum_newdata.nb` | `plots_for_Thesis/v1_v2_withPath_forP-*.pdf` |
| **Ch. 4: Extracting $x$-Dependence** | Re/Im Parity Separation ($\pm b_1$) | `mathematica_hari/A12B_TMD_all_P_save_to_h5.nb`, `A2B_TMD_all_P_save_to_h5.nb` | `save_h5_A12B_A2B/eta_bL_bT_Amp_Re_Im_err.h5` |
| **Ch. 5: Fitting & Stability** | Gaussian Failure Analysis | `mathematica_hari/eta_dependancy_A_multi_paraFit_FourierTransform_Gaussian_Lorentzian.nb` | `thesis/plots/Gaussian_fit_all_b/*.pdf` |
| **Ch. 5: Fitting & Stability** | Symbolic Regression (PySR) | `PySR/run_pysr_A2B_real.py`, `plots_for_Thesis/make_thesis_pysr_plots.py` | `thesis/PySR_outputs/*.tex`, `thesis/plots/pysr_plots/*.pdf` |
| **Ch. 5: Fitting & Stability** | Short-distance cut ($|\vec{b}| \ge 3a$) | `PySR/run_pysr_A2B_real.py` (lines 38-40) | `thesis/plots/short_distance/*.pdf` |
| **Ch. 5: Fitting & Stability** | Sequential Fit Scans ($\eta$-range, power-law) | `mathematica_hari/A12B_A2B_c_eta_dependancy_multi_paraFit_FourierTransform_LorentzianPowerLaw.nb` | `thesis/Gaussian_type_fit_Real_A2B/*.eps` |
| **Ch. 5: Fitting & Stability** | Correlated Simultaneous Fit ($f$ shared) | `mathematica_hari/A2B_Re_Im_SimultaniousFit_FourierTransform_LorentzianPowerLawShortListed.nb` | `thesis/SimultaneousFitsCov/Fit_Table_PL*.tex` |
| **Ch. 5: Fitting & Stability** | Fourier Integration $\int d(P \cdot b)$ | `mathematica_hari/Fit_bLbT_PowerlawFromPySR_4paraFit_FourierTransform_Re_A12B_ReIm_A2B_.nb` | `thesis/SimultaneousFitsCov/Integration_Table_PL*.tex` |
| **Ch. 6: Extrapolations** | $\hat{\zeta} \to \infty$ Extrapolation | `mathematica_hari/A12B_A2B_eta_dependancy_multi_paraFit_FourierTransform_LorentzianPowerLaw.nb` | `thesis/SimultaneousFitsCov/extrapolation_para_level/*.pdf` |

---

## 2. Mapping: Thesis Figures ⟷ Source Files

| Thesis Figure Path | Topic / Description | Generating Code File |
|--------------------|---------------------|----------------------|
| `plots/kinematics_interpolation/v1_v2_allzetahat_plot.pdf` | Staple directions $v$ in $v_1-v_3$ plane | `mathematica_hari/Plots_for_Thesis_Kinematics.nb` |
| `plots/kinematics_interpolation/v1_v2_withPath_forP-1_plot.pdf` | Bounding links for $P_1 = -1$ | `mathematica_hari/Plots_for_Thesis_Kinematics.nb` |
| `plots/kinematics_interpolation/Interpolation_Ex_b120_eta7_P-1.pdf` | Quadratic interpolation at $\Delta v_1 = 0$ | `mathematica_hari/Plots_for_Thesis_Kinematics.nb` |
| `plots/kinematics_interpolation/bL_bT_plot.pdf` | Discrete spatial grid in $b_1-b_2$ plane | `mathematica_hari/Plots_for_Thesis_Kinematics.nb` |
| `plots/kinematics_interpolation/Pb_bsq_plot.pdf` | Mapping into invariant space $(P \cdot b, b^2)$ | `mathematica_hari/Plots_for_Thesis_Kinematics.nb` |
| `plots/pysr_plots/01_A2B_PySR_Benchmark_Fits.pdf` | PySR Pareto front model benchmark | `plots_for_Thesis/make_thesis_pysr_plots.py` |
| `plots/pysr_plots/02_Gaussian_StraightLine_Test.pdf` | Log-linear straight-line Gaussian rejection | `plots_for_Thesis/make_thesis_pysr_plots.py` |
| `plots/short_distance/A2B_Re_b_lessthan3_and_ge3.pdf` | Discretization artifact demonstration | `mathematica_hari/Plots_for_Thesis_Kinematics.nb` |
| `plots/Gaussian_fit_all_b/Gaussian_A2B_Re_P1_FailedFit.pdf` | Gaussian model failure for $\widetilde{A}_{2B}^{\text{Re}}$ | `mathematica_hari/eta_dependancy_A_multi_paraFit_*.nb` |
| `plots/Amps_Fit/Combined_eta8_PL-1_WithFit_2D.pdf` | 2D fit surface overlay at $\eta = 8$ | `mathematica_hari/A2B_Re_Im_SimultaniousFit_*.nb` |
| `SimultaneousFitsCov/SimulFitCovMatrix-*.pdf` | 2D & 3D Jackknife covariance matrices | `mathematica_hari/A2B_Re_Im_SimultaniousFit_*.nb` |

---

## 3. Mapping: PySR Outputs ⟷ LaTeX Inclusion Points

| Generated Output File | Included In Thesis File | Description |
|-----------------------|-------------------------|-------------|
| `thesis/PySR_outputs/pysr_model_config.tex` | `Chapters/FITTING_METHODOLOGIES_AND_STABILITY_ANALYSIS.tex` (Line 144) | PySR operators, constraints, and hyperparameters table |
| `thesis/PySR_outputs/pysr_custom_loss_code.tex` | `Chapters/FITTING_METHODOLOGIES_AND_STABILITY_ANALYSIS.tex` (Line 173) | Julia custom loss function code listing |
| `thesis/PySR_outputs/pysr_equations_table.tex` | `Chapters/FITTING_METHODOLOGIES_AND_STABILITY_ANALYSIS.tex` (Line 179) | Discovered Pareto front equation table |
| `thesis/SimultaneousFitsCov/Fit_Table_PL-1_bmin3.tex` | `Chapters/FITTING_METHODOLOGIES_AND_STABILITY_ANALYSIS.tex` (Line 528) | Parameter extraction table for $P_1 = -1$ |
| `thesis/SimultaneousFitsCov/Integration_Table_PL-1_bmin3.tex` | `Chapters/FITTING_METHODOLOGIES_AND_STABILITY_ANALYSIS.tex` (Line 562) | Fourier transform integration table for $P_1 = -1$ |
