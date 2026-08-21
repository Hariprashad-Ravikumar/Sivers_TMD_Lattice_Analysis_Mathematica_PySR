# AGENTS.md — Lattice QCD TMD PhD Project

## 1. Project Overview & Repository Structure
This workspace contains the research and thesis codebase for the PhD dissertation on Lattice QCD calculations of the $x$-dependence of the Sivers TMD.

- **PhD Thesis Repository**: 
  - Path: `/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-Hariprashad-Ravikumar-NMSU-PhD-Thesis`
  - Main Document: `main.tex`
  - Core Fitting Chapter: `Chapters/FITTING_METHODOLOGIES_AND_STABILITY_ANALYSIS.tex`
  - PySR Outputs & LaTeX Snippets: `PySR_outputs/` (`plots/`, `latex_snippets/`)
  - Standalone Plots: `plots/`, `Gaussian_type_fit_Real_A2B/`, `PowerLaw_etaAsymptotic/`, `SimultaneousFitsCov/`
  - Version Control: Independent Git repo (`origin/main`)

- **Code, Analysis & Notebooks Repository**:
  - Path: `/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project`
  - Mathematica Notebooks: `mathematica_hari/` (contains `.nb` files for multi-parameter fits, Fourier transforms, and Sivers TMD $x$-dependence)
  - PySR Symbolic Regression: `PySR/` (contains `run_pysr_A2B_real.py`, hall-of-fame outputs, Julia custom loss definitions)
  - Thesis Plot Generators: `plots_for_Thesis/` (`make_thesis_pysr_plots.py`)
  - MCP Server: `mcp_wolfram_server.py`
  - Version Control: Independent Git repo (`origin/main`)

---

## 2. Computing Environments & Interpreters
- **Python (Recommended)**: `/opt/homebrew/anaconda3/bin/python`
  - Contains: `h5py`, `numpy`, `scipy`, `matplotlib`, `mcp`, `pysr`, `gvar`, `lsqfit`.
  - Always prefer `/opt/homebrew/anaconda3/bin/python` over the system `/opt/homebrew/bin/python3` which lacks `h5py`.
- **Wolfram Mathematica Kernel**: `/Applications/Mathematica.app/Contents/MacOS/WolframKernel`
  - Version: Mathematica 13.0.0 (ARM64)
  - CLI script runner: `wolframscript` or `WolframKernel -noprompt -script <file.wl>`

---

## 3. Wolfram Mathematica MCP Server Tools
The `wolfram-mathematica` MCP server (`~/.gemini/config/mcp_config.json`) exposes the following tools:

1. **`wolfram_eval(code, timeout_seconds=120)`**:
   - Executes arbitrary Wolfram Language code.
   - Use for analytical calculus, Fourier integrals $\int d(P\cdot b) e^{ix(P\cdot b)} \widetilde{A}(b)$, asymptotic limits $\eta \to \infty$, and matrix algebra.
2. **`wolfram_to_latex(expression)`**:
   - Converts mathematical expressions to clean `\TeXForm` strings for inclusion in `.tex` files.
3. **`wolfram_export_plot(plot_code, output_path, image_format="PDF", resolution=300)`**:
   - Renders a Wolfram plot (`Plot`, `Show`, `ListLinePlot`, `ContourPlot3D`) and exports vector PDF or high-res PNG directly to the thesis `plots/` or `PySR_outputs/plots/` directory.
4. **`read_notebook_cells(notebook_path, max_cells=100)`**:
   - Extracts clean, executable Wolfram Language input cells from `.nb` files in `mathematica_hari/` without loading heavy graphics caches.
5. **`wolfram_run_script(script_path, args=None, timeout_seconds=300)`**:
   - Runs external `.wl` / `.wls` batch scripts headless and reports results.

---

## 4. Thesis Mathematical & Formatting Conventions
- **Amplitudes Notation**: Always use `\tAmp` in LaTeX (which expands to `\widetilde{A}` via `\newcommand{\tAmp}{\widetilde{A}}`).
  - Real unpolarized amplitude: `\tAmp_{2B}^{\text{Re}}`
  - Imaginary unpolarized amplitude: `\tAmp_{2B}^{\text{Im}}`
  - Real Sivers amplitude: `\tAmp_{12B}^{\text{Re}}`
- **Spatial Cutoff**: Data is strictly restricted to $|\vect{b}| = \sqrt{b_L^2 + b_T^2} \ge 3a$ to eliminate UV discretization artifacts.
- **Lorentz Invariant Mapping**:
  - $b_L = \frac{P \cdot b}{-P_L}$
  - $b_T^2 = b^2 - b_L^2 = b^2 - \frac{(P\cdot b)^2}{P_L^2}$
- **Fourier Integrability**: Power-law models $\sim (1 + b^2)^{-j}$ with $j > 1/2$ ensure absolute integrability in $P \cdot b$ space (unlike Gaussian with $\alpha < \beta$).
