# Deep Wiki — Glossary & Acronyms

> **Last updated**: 2026-08-23

---

## 1. Physics Terms & Acronyms

| Term / Acronym | Full Name / Expression | Definition & Physical Context |
|----------------|------------------------|-------------------------------|
| **QCD** | Quantum Chromodynamics | The gauge field theory of strong interactions (SU(3) color symmetry). |
| **Lattice QCD** | Discretized Euclidean QCD | Non-perturbative formulation of QCD on a 4D spacetime grid with lattice spacing $a$. |
| **PDF** | Parton Distribution Function | 1D momentum fraction $x$ distribution of partons in a hadron. |
| **TMD** | Transverse Momentum Dependent Parton Distribution Function | 3D distribution function $f(x, \vec{k}_T)$ describing partonic longitudinal momentum $x$ and transverse momentum $\vec{k}_T$. |
| **Sivers Function** | $f_{1T}^\perp(x, k_T^2)$ | Naively T-odd TMD describing unpolarized quarks inside a transversely polarized nucleon. |
| **Sivers Shift** | $\langle k_y \rangle_{TU}(x)$ | Average transverse momentum offset of quarks perpendicular to nucleon transverse spin: ratio of 1st $k_T$-moment of Sivers TMD to unpolarized TMD. |
| **SIDIS** | Semi-Inclusive Deep Inelastic Scattering | Process $e + N \to e' + h + X$ probing TMDs via final-state interactions (future-pointing staple link $+\eta$). |
| **DY** | Drell–Yan Process | Process $p + p \to \ell^+ \ell^- + X$ probing TMDs via initial-state interactions (past-pointing staple link $-\eta$). |
| **T-Odd / T-Even** | Naive Time-Reversal Odd / Even | Symmetries of correlation functions under naive time reversal $T$. T-odd observables flip sign between SIDIS and DY. |
| **LaMET** | Large-Momentum Effective Theory | Theoretical framework (Ji et al.) relating Euclidean quasi-distributions at finite momentum $P_z$ to light-cone distributions via matching kernel. |
| **Collins-Soper Parameter** | $\hat{\zeta} = \frac{v \cdot P}{m_N \sqrt{\|v^2\|}}$ | Dimensionless scale quantifying the tilt of the space-like Wilson line $v$ relative to the nucleon momentum $P$. Asymptotic light cone $\leftrightarrow \hat{\zeta} \to \infty$. |
| **Soft Factor** | $\widetilde{S}(b^2; \ldots)$ | Vacuum expectation value of Wilson lines regulating rapidity divergences in TMD correlators; cancels in the Sivers shift ratio. |
| **Wilson Line / Gauge Link** | $\mathcal{U}[\mathcal{C}]$ | Path-ordered exponential $\mathcal{P} \exp(i g \int_{\mathcal{C}} A \cdot dx)$ connecting separated quark fields to preserve color gauge invariance. |
| **Staple Link** | $\mathcal{U}[0 \to \eta v \to \eta v + b \to b]$ | Staple-shaped Wilson line geometry with longitudinal separation $b$, transverse separation $b_T$, and staple length $\eta v$. |
| **Jackknife Resampling** | Statistical error method | Non-parametric resampling technique used to compute full covariance matrices $C_{ij}$ and errors on non-linear function fits over ~1000 configurations. |
| **PySR** | Symbolic Regression in Python / Julia | High-performance genetic programming engine for discovering analytical expressions balancing accuracy ($\chi^2$) and parsimony (complexity). |
| **Pareto Front** | Accuracy vs. Complexity boundary | Set of candidate mathematical expressions discovered by PySR where no equation exists that is both simpler and more accurate. |

---

## 2. Mathematical Symbol & Notation Dictionary

| Symbol | LaTeX Notation | Meaning |
|--------|----------------|---------|
| $\widetilde{A}_{2B}$ | `\tAmp_{2B}` | Combined leading-twist unpolarized position-space invariant amplitude |
| $\widetilde{A}_{12B}$ | `\tAmp_{12B}` | Combined leading-twist Sivers position-space invariant amplitude |
| $\widetilde{A}_{iB}^{\text{Re}}$ | `\tAmp_{iB}^{\text{Re}}` | Real part of invariant amplitude $\widetilde{A}_{iB}$ (even under $b \cdot P$) |
| $\widetilde{A}_{iB}^{\text{Im}}$ | `\tAmp_{iB}^{\text{Im}}` | Imaginary part of invariant amplitude $\widetilde{A}_{iB}$ (odd under $b \cdot P$) |
| $b_L$ | `b_L` | Longitudinal spatial separation component along nucleon momentum ($b_1$) |
| $b_T$ | `b_T` | Transverse spatial separation component perpendicular to momentum ($b_2$) |
| $P \cdot b$ | `P \cdot b` | Lorentz-invariant scalar product conjugate to momentum fraction $x$ |
| $v$ | `v` | Space-like direction vector of the staple gauge link |
| $\eta$ | `\eta` | Dimensionless staple extent parameter |
| $a$ | `a` | Lattice spacing ($a = 0.11403$ fm) |
| $L, T$ | `L, T` | Spatial ($L=32$) and temporal ($T=64$) lattice extents |
| $m_N$ | `m_N` or `\mN` | Nucleon ground-state mass ($a m_N = 0.6228(28)$, $m_N \approx 1078$ MeV) |
| $\hat{\zeta}$ | `\zetahat` | Collins-Soper parameter |
| $\chi^2/\text{dof}$ | `\chi^2/\text{dof}` | Reduced chi-squared goodness-of-fit metric |
