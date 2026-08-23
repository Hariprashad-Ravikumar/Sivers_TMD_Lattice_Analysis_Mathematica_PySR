# Deep Wiki — Code Architecture

> **Last updated**: 2026-08-23

---

## 1. Overview of the Code Repository

The code repository (`sivers_TMD_PhD_project`) contains the data processing pipelines, Wolfram Mathematica notebooks, Python symbolic regression scripts, HDF5 data generation tools, and thesis figure generators.

```
sivers_TMD_PhD_project/
├── mathematica_hari/              ← Mathematica notebooks & packages
│   ├── include/                   ← Custom Mathematica modules (.m)
│   ├── output/                    ← Intermediate exported Mathematica expressions & tables
│   └── *.nb                       ← Production & exploration notebooks
├── PySR/                          ← Symbolic Regression pipeline
│   ├── run_pysr_A2B_real.py       ← PySR Regressor execution script
│   ├── pysr_helpers.py            ← Helper functions
│   └── outputs_A2B_real/          ← PySR Hall of Fame CSVs & outputs
├── plots_for_Thesis/              ← Python plot generators for LaTeX inclusion
│   └── make_thesis_pysr_plots.py  ← Script generating PySR benchmark plots
├── save_h5_A12B_A2B/             ← HDF5 data files containing Jackknife samples & means
│   └── SimultaniousFit/           ← Simultaneous fit HDF5 data & outputs
├── sivers_new/                    ← Raw and processed .bidatex database files
├── mcp_wolfram_server.py          ← MCP Server exposing Wolfram Kernel tools to AGY
```

---

## 2. Core Pipelines & Workflows

### 2.1 Raw Data Extraction to Amplitude Databases (`.bidatex`)
1. **Raw inputs**: Three-point and two-point correlators stored in `sivers_new/stripped_1..4/`.
2. **Mathematica packages**: `include/BDatabase2.m`, `include/BIDATEX2.m`, `include/LatticeAnalysis.m`, `include/Resampling2.m`.
3. **Processing**: Evaluates ratios $R(t,\tau)$, fits plateau regions, and constructs linear combinations of ratios to extract $R_{\Gamma(i)}$ for spatial shifts $\pm b_1$.
4. **Output**: `.bidatex` files containing amplitude components across $\eta$, $b_L$, $b_T$, and $P_1$.

### 2.2 Re/Im Amplitude Separation & HDF5 Export
1. **Script/Notebooks**: `mathematica_hari/A12B_TMD_all_P_save_to_h5.nb`, `A2B_TMD_all_P_save_to_h5.nb`.
2. **Operations**:
   - Applies discrete symmetry projections (taking symmetric/antisymmetric combinations over $\pm b_1$).
   - Solves the 8-row system of equations for $\widetilde{A}_{2B}^{\text{Re}}$, $\widetilde{A}_{2B}^{\text{Im}}$, and $\widetilde{A}_{12B}^{\text{Re}}$.
   - Computes Jackknife covariance matrices across $\sim 1000$ gauge configurations.
3. **Outputs**: Stored in `save_h5_A12B_A2B/`:
   - `eta_bL_bT_Amp_Re_Im_err.h5`
   - `ReA2B_PL-1_jackknife_data.h5` ... `ReA2B_PL-4_jackknife_data.h5`
   - `ReA12B_PL-1_jackknife_data.h5` ... `ReA12B_PL-4_jackknife_data.h5`
   - `ImA2B_PL-1_jackknife_data.h5` ... `ImA2B_PL-4_jackknife_data.h5`

### 2.3 Symbolic Regression Pipeline (PySR)
1. **Environment**: Python `/opt/homebrew/anaconda3/bin/python` (includes `pysr`, `julia` backend, `h5py`, `sympy`).
2. **Execution Script**: [`PySR/run_pysr_A2B_real.py`](file:///Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/PySR/run_pysr_A2B_real.py)
   - Loads `eta_bL_bT_Amp_Re_Im_err.h5` for $P_1 = -1$, $\eta \in [6, 10]$.
   - Filters spatial domain: $|\vec{b}| = \sqrt{b_L^2 + b_T^2} \ge 3a$.
   - Runs `PySRRegressor` with a **Julia custom loss function**:
     $$\mathcal{L} = \frac{\chi^2}{\text{dof}} + 0.1 \sum_{b_L^{\text{large}}} |\text{model}(b_L, b_T)|^2$$
3. **Pareto Front Discovery**: Discovers factorized Lorentzian power law:
   $$\widetilde{A}_{2B}^{\text{Re}} \sim \frac{e^{-f\eta}}{(1 + c b_L^2 + d b_T^2)^j}$$
4. **Outputs**: Pareto tables saved to `PySR/outputs_A2B_real/hall_of_fame_summary.csv`.

### 2.4 Correlated Simultaneous Fitting & Fourier Transform
1. **Notebooks**: `mathematica_hari/A2B_Re_Im_SimultaniousFit_FourierTransform_LorentzianPowerLawShortListed.nb` and python scripts in `save_h5_A12B_A2B/SimultaniousFit/`.
2. **Operations**:
   - Couples $\widetilde{A}_{2B}^{\text{Re}}$, $\widetilde{A}_{2B}^{\text{Im}}$, and $\widetilde{A}_{12B}^{\text{Re}}$ into a correlated multi-function fit.
   - Enforces a shared exponential parameter $f$ for $e^{-f\eta}$.
   - Performs non-linear least squares fit with full Jackknife covariance matrix (`lsqfit` / `gvar` in Python or `NonlinearModelFit` with weight matrix in Mathematica).
   - Analytically/numerically integrates over $P \cdot b$:
     $$\int d(P \cdot b) \, e^{i x (P \cdot b)} \widetilde{A}(P \cdot b, b_T)$$
   - Extracts $\langle k_y \rangle_{TU}(x, \hat{\zeta})$.
3. **Outputs**: PDF plots exported to `thesis/plots/Amps_Fit/` and LaTeX tables generated for `SimultaneousFitsCov/`.

### 2.5 Thesis Plot Generation
1. **Script**: [`plots_for_Thesis/make_thesis_pysr_plots.py`](file:///Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/plots_for_Thesis/make_thesis_pysr_plots.py)
2. **Operations**: Reads HDF5 data and PySR model outputs, generating publication-quality figures:
   - `01_A2B_PySR_Benchmark_Fits.pdf`
   - `02_Gaussian_StraightLine_Test.pdf`
   - Saves PDFs to `thesis/plots/pysr_plots/` and snippet tables to `thesis/PySR_outputs/`.

---

## 3. Key Data Formats

| Extension | Format | Description |
|-----------|--------|-------------|
| `.bidatex` | Binary / Text Custom Database | Custom Mathematica dataset format holding Jackknife sample arrays for lattice correlation functions |
| `.h5` | HDF5 | Structured numerical arrays holding processed amplitudes, mean values, errors, and full covariance matrices |
| `.m` | Mathematica Package / Script | Modular Wolfram code (data structures, eliminatepoints definitions) |
| `.nb` | Mathematica Notebook | Interactive evaluation workflows, plots, fitting routines |
| `.csv` | CSV | PySR Hall of Fame tables and raw numerical benchmark outputs |
| `.pdf` | Vector Graphic | Thesis publication figures |

---

## 4. MCP Server (`mcp_wolfram_server.py`)

The workspace includes a custom Model Context Protocol (MCP) server integration allowing AGY to execute Wolfram Language code directly via headless `WolframKernel` execution.

- **File**: [`mcp_wolfram_server.py`](file:///Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/mcp_wolfram_server.py)
- **Interpreter**: `/Applications/Mathematica.app/Contents/MacOS/WolframKernel`
- **Exposed MCP Tools**:
  - `wolfram_eval(code)`: Evaluates WL expressions synchronously.
  - `wolfram_to_latex(expression)`: Converts WL expressions to `\TeXForm`.
  - `wolfram_export_plot(plot_code, output_path)`: Exports graphics directly to thesis folders.
  - `read_notebook_cells(notebook_path)`: Strips notebook graphics cache and extracts input cells.
  - `wolfram_run_script(script_path)`: Headless batch runner for `.wl` scripts.
