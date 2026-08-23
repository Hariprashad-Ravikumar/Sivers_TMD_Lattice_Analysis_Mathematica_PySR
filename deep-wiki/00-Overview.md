# Deep Wiki — Overview

> **Last updated**: 2026-08-23  
> **Status**: Active development — thesis writing + final extrapolations

---

## 1. What This Project Is

This is the full research workspace for the PhD dissertation:

> **"Lattice QCD Calculations of the $x$-Dependence of the Sivers TMD"**  
> Hariprashad Ravikumar — New Mexico State University

The Sivers function $f_{1T}^{\perp}(x, k_T)$ is a naively time-reversal-odd (T-odd) Transverse Momentum Dependent Parton Distribution Function (TMD) that describes the correlation between the transverse momentum of an unpolarized quark and the transverse spin of the parent nucleon. It is a key observable in Semi-Inclusive Deep Inelastic Scattering (SIDIS) and Drell–Yan processes, and is predicted to reverse sign between the two — a direct manifestation of initial/final-state interactions mediated by the gauge link topology.

This project is the **first lattice QCD determination of the continuous $x$-dependence** of the Sivers TMD, achieved by:
1. Evaluating non-local quark bilinear operators with staple-shaped Wilson lines on Euclidean lattice configurations.
2. Extracting the invariant amplitudes $\widetilde{A}_{2B}$ (unpolarized) and $\widetilde{A}_{12B}$ (Sivers) from the $\gamma^+$-projected correlator.
3. Performing a continuous Fourier transform in $P \cdot b$ to recover the momentum-fraction ($x$) dependence.
4. Extrapolating $\hat{\zeta} \to \infty$ to approach the physical light-cone limit.

---

## 2. Repository Layout

```
Lattice_QCD_TMD_PhD/
├── Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-*.../   ← THESIS repo (git)
│   ├── main.tex                       ← Master document
│   ├── Chapters/
│   │   ├── INTRODUCTION_AND_MOTIVATION.tex         (stub)
│   │   ├── LATTICE_QCD_METHODOLOGY.tex             ✓ complete
│   │   ├── THEORETICAL_FRAMEWORK_OF_TMDs.tex       ✓ complete
│   │   ├── EXTRACTING_THE_x-DEPENDENCE.tex         ✓ complete (~85 kB)
│   │   ├── FITTING_METHODOLOGIES_AND_STABILITY_ANALYSIS.tex  ✓ complete (~71 kB)
│   │   ├── EXTRAPOLATIONS-TO-THE-PHYSICAL-LIMIT.tex  (draft, figures only)
│   │   └── CONCLUSION.tex                          (stub)
│   ├── plots/                         ← Publication-quality PDF figures
│   │   ├── Amps_Fit/                  ← Simultaneous fit overlays
│   │   ├── Amps_Pb_bsq/              ← Amplitude surfaces in invariant space
│   │   ├── Amps_bL_bT/               ← Amplitude surfaces in Cartesian space
│   │   ├── Gaussian_fit_all_b/       ← Gaussian failure diagnostics
│   │   ├── kinematics_interpolation/  ← Off-axis link geometry & interpolation
│   │   ├── pysr_plots/               ← PySR Pareto front visualizations
│   │   └── short_distance/           ← b < 3a vs b ≥ 3a comparisons
│   ├── Gaussian_type_fit_Real_A2B/    ← Gaussian & Lorentzian stability scans
│   ├── PowerLaw_etaAsymptotic/        ← η→∞ extrapolation plots
│   ├── SimultaneousFitsCov/           ← Simultaneous fit tables & covariance matrices
│   ├── PySR_outputs/                  ← PySR config tables, loss code, equations
│   ├── BibTeXList.bib                 ← References
│   └── nmsuth01.cls                   ← NMSU thesis class
│
├── sivers_TMD_PhD_project/            ← CODE repo (git)
│   ├── mathematica_hari/              ← ~68 Mathematica notebooks
│   │   ├── include/                   ← Shared packages (BDatabase2.m, Resampling2.m, etc.)
│   │   ├── output/                    ← Generated .m structures & PDF plots
│   │   ├── Plots_for_Thesis_Kinematics.nb          ← Kinematics figures
│   │   ├── parametrization_ulink.nb                ← U-link parametrization
│   │   ├── A12B_A2B_*_LorentzianPowerLaw*.nb       ← Core fitting notebooks
│   │   └── ... (many iterations of fitting notebooks)
│   ├── PySR/                          ← Symbolic Regression
│   │   ├── run_pysr_A2B_real.py       ← Physics-informed PySR driver
│   │   ├── pysr_helpers.py            ← Utilities
│   │   ├── outputs_A2B_real/          ← Hall-of-fame CSVs
│   │   └── *.ipynb                    ← Exploration notebooks
│   ├── PySR_Machine_learning_TMD_Lattice/ ← Extended ML experiments
│   ├── plots_for_Thesis/              ← Python plot generators
│   │   └── make_thesis_pysr_plots.py  ← PySR benchmark figure generator
│   ├── save_h5_A12B_A2B/             ← HDF5 data stores (Jackknife, means)
│   │   └── SimultaniousFit/          ← PySR hall-of-fame for simultaneous fits
│   ├── sivers_new/                    ← Raw .bidatex lattice databases
│   │   ├── stripped_1..4/             ← Per-momentum plateau data
│   │   └── newDBforA12BA2B/           ← Processed amplitude databases
│   ├── sivers_x/                      ← Older x-dependent datasets
│   ├── mcp_wolfram_server.py          ← MCP server for Mathematica
│   └── pysr_helpers.py
│
├── deep-wiki/                         ← THIS WIKI
├── AGENTS.md                          ← Project rules
└── .agents/                           ← Agent config
```

---

## 3. Lattice Ensemble Parameters

| Parameter | Value |
|-----------|-------|
| **Action** | Wilson gauge + Wilson fermions |
| **Lattice volume** | $32^3 \times 64$ |
| **Lattice spacing** $a$ | $0.11403$ fm |
| **Pion mass** $m_\pi$ | $\sim 518$ MeV (unphysical, u–d isovector) |
| **Nucleon mass** $m_N$ | $0.6228(28) \, a^{-1} = 1077.8(48)$ MeV |
| **Configurations** | ~1000 (Jackknife resampling) |
| **Source-sink separation** | Optimized for ground-state saturation |

**Momenta**: $P_1 \in \{-1, -2, -3, -4\} \times 2\pi/(La)$  
**Collins-Soper**: $\hat{\zeta} \in \{0.091, 0.294, 0.540, 0.786\}$  
**Staple extents**: $\eta \in [0, 10]$ (analysis restricted to $\eta \in [6, 10]$)  
**Spatial cut**: $|\vec{b}| \geq 3a$

---

## 4. Current Status

| Component | Status |
|-----------|--------|
| Data extraction (2pt/3pt) | ✅ Complete |
| Amplitude solving ($\widetilde{A}_{2B}$, $\widetilde{A}_{12B}$) | ✅ Complete |
| Off-axis interpolation | ✅ Complete |
| PySR symbolic regression | ✅ Complete |
| Sequential $\chi^2$ stability scans | ✅ Complete |
| Simultaneous fit w/ covariance | ✅ Complete (all 4 momenta) |
| Fourier transform → $x$-dependent Sivers shift | ✅ Complete |
| $\hat{\zeta} \to \infty$ extrapolation | 🟡 Draft (figures placed, text minimal) |
| Introduction chapter | 🔴 Stub |
| Conclusion chapter | 🔴 Stub |
| Physical-limit extrapolation chapter | 🟡 Figures only |

---

## 5. Key Physics Deliverables

1. **The generalized Sivers shift** $\langle k_y \rangle_{TU}(x, b_T^2, \hat{\zeta})$ as a continuous function of $x$.
2. **The $\hat{\zeta}$-extrapolated Sivers shift** at $\hat{\zeta} \to \infty$ (physical TMD).
3. **The PySR-discovered power-law ansatz**: $(1 + b^2)^{-j}$ spatial profile, replacing the failed Gaussian model.
4. **Demonstration of the SIDIS/DY sign reversal** via the $\eta$-sign flip of $\widetilde{A}_{12B}^{\mathrm{Re}}$.
