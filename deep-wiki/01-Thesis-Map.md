# Deep Wiki — Thesis Map

> **Last updated**: 2026-08-23

---

## Chapter-by-Chapter Summary

### Chapter 1: INTRODUCTION AND MOTIVATION
**File**: [`INTRODUCTION_AND_MOTIVATION.tex`](file:///Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-Hariprashad-Ravikumar-NMSU-PhD-Thesis/Chapters/INTRODUCTION_AND_MOTIVATION.tex)  
**Status**: 🔴 **Stub** — Contains only the section heading.

**Needed content**:
- Motivation for studying nucleon 3D structure beyond collinear PDFs
- Why the Sivers function matters: spin-orbit correlations, process dependence (SIDIS vs DY sign change)
- Why lattice QCD is the uniquely positioned first-principles method
- Brief roadmap of the thesis

---

### Chapter 2: LATTICE QCD METHODOLOGY
**File**: [`LATTICE_QCD_METHODOLOGY.tex`](file:///Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-Hariprashad-Ravikumar-NMSU-PhD-Thesis/Chapters/LATTICE_QCD_METHODOLOGY.tex)  
**Status**: ✅ **Complete** (86 lines, ~11 kB)

**Covers**:
- QCD Lagrangian and asymptotic freedom
- Lattice regularization: Euclidean rotation, hypercubic grid, UV/IR cutoffs
- Wilson gauge action (plaquette construction)
- Wilson fermions and the doubling problem
- Two-point functions → nucleon mass extraction
- Three-point functions → matrix elements
- Non-local operators with gauge links
- TMD three-point functions with staple-shaped Wilson lines
- The ratio method for extracting bare matrix elements

**Key equations**: $C_2(t,\mathbf{p})$, $C_3(t,\tau,\mathbf{p})$, ratio $R(t,\tau)$

---

### Chapter 3: THEORETICAL FRAMEWORK OF TMDs
**File**: [`THEORETICAL_FRAMEWORK_OF_TMDs.tex`](file:///Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-Hariprashad-Ravikumar-NMSU-PhD-Thesis/Chapters/THEORETICAL_FRAMEWORK_OF_TMDs.tex)  
**Status**: ✅ **Complete** (177 lines, ~18 kB)

**Covers**:
- Definition of the unsubtracted quark-quark correlator $\widetilde{\Phi}^{[\Gamma]}_{\mathrm{unsub}}$
- Soft factor $\widetilde{S}$ and its cancellation in ratios
- $x$-$b_T$ Fourier space: Bessel-weighted TMDs, $\tilde{f}^{(n)}$ moments
- Why $b_T = 0$ extrapolation fails (Sivers moment divergence)
- Staple-shaped gauge link: $\mathcal{U}[\mathcal{C}_b^{(\eta v)}]$
- Collins-Soper parameter: $\hat{\zeta} = v \cdot P / (m_N \sqrt{|v^2|})$
- Symmetry constraints: L, P, T, $\dagger$ transformations
- Hermitian conjugation → Re/Im ↔ $b$-even/$b$-odd parity
- Parametrization: 8-amplitude decomposition (Goeke et al.)
- Combined amplitudes: $\widetilde{A}_{2B} = \widetilde{A}_2 + R(\hat{\zeta}^2)\widetilde{B}_1$
- Final Fourier integral operator $\int_\mathcal{F}$ connecting amplitudes → $f_1$, $f_{1T}^\perp$

**Critical constraint**: $R(\hat{\zeta}^2) = 1 - \sqrt{1 + \hat{\zeta}^{-2}}$

---

### Chapter 4: EXTRACTING THE $x$-DEPENDENCE
**File**: [`EXTRACTING_THE_x-DEPENDENCE.tex`](file:///Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-Hariprashad-Ravikumar-NMSU-PhD-Thesis/Chapters/EXTRACTING_THE_x-DEPENDENCE.tex)  
**Status**: ✅ **Complete** (954 lines, ~85 kB) — the **longest and most detailed chapter**

**Covers** (in order):
1. **Sivers shift as a function of $x$**: The Fourier transform ratio $\langle k_y \rangle_{TU}(x)$
2. **Parity filtering**: cos/sin decomposition → only even⊗Re and odd⊗Im survive
3. **Collins-Soper parameter**: Computation of $\hat{\zeta}$ for each momentum
4. **Kinematic constraints**: $v \cdot b / (v \cdot P) = b \cdot P \cdot R / m_N^2$ and the decoupling condition $\vec{v}_T \cdot \vec{b}_T = 0$
5. **Explicit $P_1 = -1$ calculation**: $\hat{\zeta} = \pm 0.090772$, $v_1 = \pm 0.301 v_3$
6. **Off-axis link geometry**: Table of $\hat{\zeta}$ and $v_1/v_3$ ratios for $P_1 \in \{-1,...,-4\}$
7. **Spatial interpolation**: Path averaging + quadratic interpolation at $\Delta v_1 = 0$
8. **$\vec{b}$ separation vectors**: Even/odd $b_L$ → Re/Im amplitude projection
9. **Gauge link construction**: Tables of step sequences for $b_T$-only and off-axis $\pm b_1$
10. **Path averaging for $\vec{b}$**: Degeneracy mitigation
11. **Solving for amplitudes**: Full tensor contraction $\gamma^0, \gamma^1, \gamma^2, \gamma^3$
12. **Euclidean–Minkowski conversion**: $\gamma^i_E \leftrightarrow i\gamma^i_M$ mapping
13. **Finite-link matrix equation**: 8-row system for Re/Im $R_{\Gamma(i)}$ at $\pm b^1$

**Key figures**: v-path plots (Figs. 5–12), interpolation example (Fig. 13), $b$-space coverage, gauge link tables

---

### Chapter 5: FITTING METHODOLOGIES AND STABILITY ANALYSIS
**File**: [`FITTING_METHODOLOGIES_AND_STABILITY_ANALYSIS.tex`](file:///Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-Hariprashad-Ravikumar-NMSU-PhD-Thesis/Chapters/FITTING_METHODOLOGIES_AND_STABILITY_ANALYSIS.tex)  
**Status**: ✅ **Complete** (852 lines, ~71 kB) — the **second core chapter**

**Major sections**:
1. **Cartesian vs Invariant fitting domain**: Why $(b_L, b_T)$ is superior to $(P \cdot b, b^2)$
2. **Gaussian model**: Coordinate transform $b_T^2 = b^2 - b_L^2$, Fourier integrability condition $\alpha > \beta$
3. **Pathology**: $\chi^2/\mathrm{dof} \approx 230$, $\alpha < \beta$ → divergent FT
4. **PySR symbolic regression**: Genetic algorithms, expression trees, crossover/mutation
5. **Custom loss function**: $\mathcal{L}_{\mathrm{custom}} = \chi^2/\mathrm{dof} + \epsilon \sum |f(b_L^{\mathrm{large}})|$
6. **Pareto front**: Discovery of $(1 + b^2)^{-j} \cdot e^{-f\eta}$ (complexity 14, 16)
7. **Gaussian straight-line test**: Definitive rejection of Gaussian profile
8. **Short-distance exclusion**: $|\vec{b}| \geq 3a$ cut to remove UV artifacts
9. **Sequential stability scans**: $\eta$-range, $b_{\min}$ dependence
10. **$\eta$-dependent Gaussian-type fits**: Fixed-$\eta$ Gaussian, Lorentzian, power-law comparisons
11. **Candidate selection**: Simultaneous fit strategy with shared $e^{-f\eta}$
12. **Correlated $\chi^2$ with Jackknife covariance**: `gvar` + `lsqfit` pipeline
13. **Results for all 4 momenta**: Tables, 3D fit overlays, FT integration results
14. **$\hat{\zeta} \to \infty$ extrapolation results** (Sec. 6 in the file)

**Final models**:
- $\widetilde{A}_{2B}^{\mathrm{Re}} = a e^{-f\eta} / [1 + (d + c(1 - k_1/\eta - k_2/\eta^2))b_L^2 + db_T^2]^j$
- $\widetilde{A}_{12B}^{\mathrm{Re}} = -a' e^{-f\eta} / [1 + (c'+d')b_L^2 + d'b_T^2]^{j'}$
- $\widetilde{A}_{2B}^{\mathrm{Im}} = a'' b_L e^{-f\eta} / [1 + (c''+d'')b_L^2 + d''b_T^2]^{j''}$

---

### Chapter 6: EXTRAPOLATIONS TO THE PHYSICAL LIMIT
**File**: [`EXTRAPOLATIONS-TO-THE-PHYSICAL-LIMIT.tex`](file:///Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-Hariprashad-Ravikumar-NMSU-PhD-Thesis/Chapters/EXTRAPOLATIONS-TO-THE-PHYSICAL-LIMIT.tex)  
**Status**: 🟡 **Draft** (34 lines) — Figures placed, no explanatory text

**Figures placed**:
- $1/P_L$ extrapolation plot (all momenta overlaid)
- Parameter-level extrapolation in $1/\hat{\zeta}^2$ (using $P = -2, -3, -4$)
- Extrapolated amplitude-level Sivers shift at $\hat{\zeta} \to \infty$
- Covariance matrix of the extrapolated fit
- Comparison: all finite-$\hat{\zeta}$ vs. extrapolated

**Needs**: Explanatory prose connecting figures; discussion of systematic uncertainties.

---

### Chapter 7: CONCLUSION
**File**: [`CONCLUSION.tex`](file:///Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-Hariprashad-Ravikumar-NMSU-PhD-Thesis/Chapters/CONCLUSION.tex)  
**Status**: 🔴 **Stub** — Section heading only.

---

## Supporting Files

| File | Purpose |
|------|---------|
| [`appendix.tex`](file:///Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-Hariprashad-Ravikumar-NMSU-PhD-Thesis/appendix.tex) | Supplementary material |
| [`BibTeXList.bib`](file:///Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-Hariprashad-Ravikumar-NMSU-PhD-Thesis/BibTeXList.bib) | Bibliography (~40 entries) |
| [`nmsuth01.cls`](file:///Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-Hariprashad-Ravikumar-NMSU-PhD-Thesis/nmsuth01.cls) | NMSU thesis formatting class |
| [`PySR_outputs/`](file:///Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-Hariprashad-Ravikumar-NMSU-PhD-Thesis/PySR_outputs) | LaTeX snippets auto-generated by Python (`\input{...}`) |
| [`SimultaneousFitsCov/`](file:///Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-Hariprashad-Ravikumar-NMSU-PhD-Thesis/SimultaneousFitsCov) | Fit tables + covariance matrix plots per $P_L$ |

---

## Notation Cheat Sheet (Thesis LaTeX Commands)

| Command | Renders as | Meaning |
|---------|-----------|---------|
| `\tAmp` | $\widetilde{A}$ | Position-space invariant amplitude |
| `\tBmp` | $\widetilde{B}$ | $v$-dependent amplitude |
| `\vect{b}` | $\boldsymbol{b}$ | Spatial separation vector |
| `\mN` | $m_N$ | Nucleon mass |
| `\zetahat` | $\hat{\zeta}$ | Collins-Soper parameter |
| `\fourint` | $\int_\mathcal{F}$ | Fourier integration operator |
| `\WlineC{...}` | $\mathcal{U}[\cdots]$ | Wilson line along contour |
| `\softf` | $\mathcal{S}$ | Soft factor |
| `\unsub` | unsubtr. | Unsubtracted label |
| `\Wline{...}` | $\mathcal{U}[\cdots]$ | Wilson line |
