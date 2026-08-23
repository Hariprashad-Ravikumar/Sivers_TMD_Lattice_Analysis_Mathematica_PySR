# Deep Wiki — Changelog

> **Last updated**: 2026-08-23

This log tracks all major updates, computational milestones, fitting changes, thesis edits, and Deep Wiki additions across both repositories (`Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-Hariprashad-Ravikumar-NMSU-PhD-Thesis` and `sivers_TMD_PhD_project`).

---

## [2026-08-23] — Deep Wiki Initialization & Workspace Synchronization

### Added
- **Created Deep Wiki** (`/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/deep-wiki/`):
  - `00-Overview.md`: High-level summary of the PhD project, layout, ensemble parameters, current status.
  - `01-Thesis-Map.md`: Chapter-by-chapter status, key equations, LaTeX notation cheat sheet.
  - `02-Physics-Concepts.md`: Complete derivation chain from QCD Lagrangian to Sivers shift, Gaussian failure, PySR power-law discovery.
  - `03-Code-Architecture.md`: Overview of notebooks, pipelines, PySR driver, HDF5 formats, MCP integration.
  - `04-Cross-Reference-Map.md`: Explicit mapping between thesis chapters, LaTeX files, Mathematica notebooks, Python scripts, HDF5 datasets, and PDF figures.
  - `05-Open-Questions.md`: Active research questions, missing thesis writing tasks, systematic error backlog, standing AI instructions.
  - `06-Glossary.md`: Physics acronyms, TMD terms, and LaTeX symbol dictionary.
  - `07-Changelog.md`: This file.

### Fixed
- **Mac Binary Header Stripping**: Stripped non-ASCII cache header metadata (first 145 bytes) from `parametrization_ulink.nb` and `parametrization_ulink_v1v3_b1b2.nb` to enable clean headless execution via Wolfram Mathematica `NotebookImport` / MCP tools.
- **Plots & Tables Synchronization**: Executed `Plots_for_Thesis_Kinematics.nb` and regenerated 18 kinematics figures in `plots_for_Thesis/` and `thesis/plots/kinematics_interpolation/`.
- **Git Repositories**: Committed and pushed changes to both `thesis` and `sivers_TMD_PhD_project` repositories.

---

## [Prior Milestones Summary]

### PySR Symbolic Regression Campaign
- Discovered Lorentzian-type power-law spatial decay $(1 + b^2)^{-j}$ for $\widetilde{A}_{2B}^{\text{Re}}$.
- Implemented Julia custom loss function with asymptotic decay penalty $\mathcal{P}_{\text{asymptotic}} = \sum |f(b_L^{\text{large}})|^2$.
- Discovered shared exponential decay $e^{-f\eta}$ across all three surviving effective amplitudes ($\widetilde{A}_{2B}^{\text{Re}}$, $\widetilde{A}_{2B}^{\text{Im}}$, $\widetilde{A}_{12B}^{\text{Re}}$).

### Short-Distance Cut ($|\vec{b}| \ge 3a$)
- Excluded short-distance lattice points ($|\vec{b}| < 3a$) due to hypercubic discretization artifacts and opposite curvature trends.

### Correlated Simultaneous Fitting
- Built dense Jackknife covariance matrices across all spatial points and real/imaginary components.
- Executed correlated $\chi^2$ minimizations using `gvar` and `lsqfit` in Python and Mathematica for all four momenta ($P_1 \in \{-1, -2, -3, -4\}$).
- Numerically evaluated Fourier integrals to extract continuous $x$-dependent Sivers shift $\langle k_y \rangle_{TU}(x, \hat{\zeta})$.
