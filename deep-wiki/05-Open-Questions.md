# Deep Wiki — Open Questions & Research Backlog

> **Last updated**: 2026-08-23

---

## 1. Physics & Analytical Open Questions

### 1.1 Completing the $\hat{\zeta} \to \infty$ Extrapolation
- **Current State**: Chapter 6 ([`EXTRAPOLATIONS-TO-THE-PHYSICAL-LIMIT.tex`](file:///Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-Hariprashad-Ravikumar-NMSU-PhD-Thesis/Chapters/EXTRAPOLATIONS-TO-THE-PHYSICAL-LIMIT.tex)) currently contains figure references but lacks complete explanatory narrative.
- **Task**: Draft detailed analytical explanations for the $1/\hat{\zeta}^2$ linear parameter-level fit vs amplitude-level fit. Discuss why $P_1 = -1$ is excluded from the extrapolation ($P_1 = -1$ corresponds to $\hat{\zeta} \approx 0.091$, which is far from the asymptotic light-cone region).

### 1.2 Systematics of the Short-Distance Cut $|\vec{b}| \ge 3a$
- **Current State**: The spatial cut $|\vec{b}| \ge 3a$ successfully insulates the fits from hypercubic rotational symmetry breaking and $\mathcal{O}(a^2)$ discretization noise.
- **Question**: How sensitive are the extracted fit parameters ($j, c, d, f$) and the resulting Sivers shift $\langle k_y \rangle_{TU}(x)$ to shifting the cut to $|\vec{b}| \ge 2.5a$ or $|\vec{b}| \ge 3.5a$?
- **Action**: Run a systematic variation of $b_{\min} \in \{2, 2.5, 3, 3.5\}a$ and quantify the resulting systematic error band on $\langle k_y \rangle_{TU}(x)$.

### 1.3 Asymptotic $\eta \to \infty$ Behavior
- **Current State**: The simultaneous fit model assumes a single exponential factor $e^{-f\eta}$ describing the staple length dependence.
- **Question**: Does $f$ exhibit any residual dependence on $b_T$ or nucleon momentum $P_1$? Is an area-law function $e^{-f \eta b_T}$ physically more appropriate than a pure $e^{-f \eta}$?
- **Note**: In the Sivers shift ratio, any factorized $\eta$-dependence cancels out analytically, so minor model variations in $\eta$ do not affect the extracted $x$-dependence, provided the factorization holds.

---

## 2. Textual & Thesis Completion Backlog

### 2.1 Writing Chapter 1: INTRODUCTION AND MOTIVATION
- **File**: [`Chapters/INTRODUCTION_AND_MOTIVATION.tex`](file:///Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-Hariprashad-Ravikumar-NMSU-PhD-Thesis/Chapters/INTRODUCTION_AND_MOTIVATION.tex)
- **Status**: Stub.
- **Needed Sections**:
  1. Hadron structure beyond collinear PDFs (3D imaging in momentum space).
  2. The Sivers effect, spin-orbit correlations, and single-spin asymmetries (SSA).
  3. Gauge link topologies, initial/final state interactions, and the non-trivial T-odd sign change ($\text{SIDIS} = -\text{DY}$).
  4. Role of Lattice QCD and Large-Momentum Effective Theory (LaMET) / Quasi-TMD approaches.
  5. Outline of the dissertation structure.

### 2.2 Writing Chapter 7: CONCLUSION AND OUTLOOK
- **File**: [`Chapters/CONCLUSION.tex`](file:///Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-Hariprashad-Ravikumar-NMSU-PhD-Thesis/Chapters/CONCLUSION.tex)
- **Status**: Stub.
- **Needed Sections**:
  1. Summary of key accomplishments (first continuous $x$-dependence of Sivers TMD from lattice QCD).
  2. Main findings: failure of Gaussian spatial models, PySR power-law discovery, $\hat{\zeta} \to \infty$ behavior.
  3. Outlook: physical pion mass ensembles, smaller lattice spacings $a$, continuum/chiral extrapolations, comparison with upcoming Electron-Ion Collider (EIC) experimental data.

---

## 3. Code & Computational Tasks

### 3.1 Mathematica Headless Execution Stability
- **Issue**: Standard `wolframscript` / `NotebookImport` occasionally encounters Mac binary headers (`CacheID` comments at the head of `.nb` files).
- **Workaround**: Programmatic stripping of the first 145 bytes or reading raw ASCII expressions.
- **Permanent Solution**: Retain a clean script version (`.wl` or `.wls`) alongside every `.nb` notebook in `mathematica_hari/`.

### 3.2 Automated Thesis Figure Sync
- **Current State**: Python scripts (`plots_for_Thesis/make_thesis_pysr_plots.py`) generate PDF plots directly into `thesis/plots/pysr_plots/`.
- **Task**: Ensure all Mathematica notebooks that produce figures export directly to `thesis/plots/` rather than saving images inside `.nb` cells. This keeps the `.nb` files lightweight and version-control friendly.

---

## 4. Standing Instruction for Future Sessions

> **Always keep the Deep Wiki updated!**  
> Whenever a major fit is rerun, a chapter section is completed, a new PySR run is performed, or a paper draft/thesis chapter is edited, update the relevant Deep Wiki markdown file (`00` through `07`) in `/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/deep-wiki/` and record the change in `07-Changelog.md`.
