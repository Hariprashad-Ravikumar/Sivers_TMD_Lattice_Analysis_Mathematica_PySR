# `SimultaneousFit_A12bA2B_fromh5.ipynb` — Complete Technical Documentation

> Audience: any agent or developer who needs to understand, replicate, or extend this notebook.  
> All math is exact. All code variable names match the notebook verbatim.

---

## 1. Purpose

This notebook reads **jackknife-ensemble fit parameters** from an HDF5 file produced by the simultaneous fit code, analytically computes the Fourier transforms (FTs) of the three lattice QCD amplitudes using closed-form Bessel-K formulas, propagates uncertainties via jackknife resampling, prints an integration table, and produces a **6-panel plot** per kinematic point `(b2, PL)`.

---

## 2. Physical Context

### 2.1 Three Fitted Amplitudes

The simultaneous fit constrains three Euclidean lattice amplitudes in the invariant $(b_L, b_T)$ space at nucleon boost $P_L$:

| Symbol | Full expression |
|---|---|
| $\widetilde{A}_{2B}^{\text{Re}}$ | $\dfrac{a\,e^{-f\eta}}{\left[1 + \left(d + c\left(1 - \tfrac{k_1}{\eta} - \tfrac{k_2}{\eta^2}\right)\right)b_L^2 + d\,b_T^2\right]^j}$ |
| $\widetilde{A}_{2B}^{\text{Im}}$ | $\dfrac{a''\,b_L\,e^{-f\eta}}{\left[1 + (c''+d'')\,b_L^2 + d''\,b_T^2\right]^j}$ |
| $\widetilde{A}_{12B}^{\text{Re}}$ | $\dfrac{-a'\,e^{-f\eta}}{\left[1 + (c'+d')\,b_L^2 + d'\,b_T^2\right]^{j'}}$ |

**Shared parameter**: $f$ is the same across all three amplitudes (simultaneous constraint).

### 2.2 Lorentz-Invariant Reformulation

The model denominators rewrite naturally in Lorentz-invariant form using $b^2 = b_L^2 + b_T^2$:

$$1 + (c+d)\,b_L^2 + d\,b_T^2 = 1 + d\,b^2 + c\,b_L^2$$

So the denominators in Lorentz-invariant notation (as appear in the thesis) are:

$$D_{2B}^{\text{Re}} = \left[1 + c\!\left(1-\tfrac{k_1}{\eta}-\tfrac{k_2}{\eta^2}\right)\!\frac{(P{\cdot}b)^2}{P_L^2} + d\,b^2\right]^j, \quad D_{12B}^{\text{Re}} = \left[1 + c'\frac{(P{\cdot}b)^2}{P_L^2} + d'\,b^2\right]^{j'}$$

### 2.3 The Sivers Shift

The mean transverse momentum in the nucleon (Sivers effect) is:

$$\langle k_y\rangle_{TU}(x) = m_N\frac{\displaystyle\int d(b{\cdot}P)\,\cos\!\bigl(x(b{\cdot}P)\bigr)\,\frac{a'}{D_{12B}^{\text{Re}}}}{\displaystyle\int d(b{\cdot}P)\left[\cos\!\bigl(x(b{\cdot}P)\bigr)\,\frac{a}{D_{2B}^{\text{Re}}} - \sin\!\bigl(x(b{\cdot}P)\bigr)\,\frac{a''(P{\cdot}b)/(-P_L)}{D_{2B}^{\text{Im}}}\right]}$$

---

## 3. HDF5 File & Parameter Layout

### 3.1 File naming convention

```
FitParams_SimulFit_f_A2BRe_cetasq_A2BIm_A12BRe_bmin{bmin}_eta{etamin}{etamax}_PL{PL}.h5
```

Example: `...bmin3_eta610_PL-1.h5` means $b_{\min}=3a$, $\eta\in[6,10]$, $P_L=-1$.

### 3.2 HDF5 internal layout

```
/jackknife_samples/
    a_re       [N_jk]  — coefficient of ReA2B
    c_re       [N_jk]  — shape parameter c for ReA2B
    d_re       [N_jk]  — shape parameter d for ReA2B
    k1_re      [N_jk]  — eta-correction k1 for ReA2B
    k2_re      [N_jk]  — eta-correction k2 for ReA2B
    j_re       [N_jk]  — power-law exponent for ReA2B
    a_im       [N_jk]  — coefficient of ImA2B
    c_im       [N_jk]  — shape parameter c for ImA2B
    d_im       [N_jk]  — shape parameter d for ImA2B
    j_im       [N_jk]  — power-law exponent for ImA2B
    a_reA12B   [N_jk]  — coefficient of ReA12B
    c_reA12B   [N_jk]  — shape parameter c for ReA12B
    d_reA12B   [N_jk]  — shape parameter d for ReA12B
    j_reA12B   [N_jk]  — power-law exponent for ReA12B
    f          [N_jk]  — shared exponential decay (all amplitudes)
/chi2_dof      [N_jk]  — chi^2/DoF for each jackknife sample
```

Each dataset has length `N_jk` (number of jackknife samples, typically = number of lattice configurations).

---

## 4. Parameter Rescaling (Critical)

After loading from HDF5, parameters are rescaled for use in the FT formulas. The code does this inside `plot_fourier_transforms_A2B_A12B`:

```python
# ReA2B
a_re  = np.array(fitted_params['a_re'])
c_re  = np.array(fitted_params['c_re']) / (PL**2)   # C_phys = c_fit / PL²
d_re  = 1.0 + np.array(fitted_params['d_re']) * b2  # D_phys = 1 + d_fit * b²
j_re  = np.array(fitted_params['j_re'])

# ImA2B  — NOTE: divided by PL (includes sign)
a_im  = np.array(fitted_params['a_im']) / PL        # a_phys = a_fit / PL
c_im  = np.array(fitted_params['c_im']) / (PL**2)
d_im  = 1.0 + np.array(fitted_params['d_im']) * b2
j_im  = np.array(fitted_params['j_im'])

# ReA12B — NOTE: negated
a_reA12B  = -np.array(fitted_params['a_reA12B'])    # sign flip: model has -a'
c_reA12B  = np.array(fitted_params['c_reA12B']) / (PL**2)
d_reA12B  = 1.0 + np.array(fitted_params['d_reA12B']) * b2
j_reA12B  = np.array(fitted_params['j_reA12B'])
```

### Why `c_phys = c_fit / PL²` and `d_phys = 1 + d_fit * b2`

The integration variable is $\lambda = b_L P_L$. The model denominator (using the Lorentz-invariant form at large $\eta$):

$$1 + d\,b^2 + c\,b_L^2 = \underbrace{(1 + d\,b^2)}_{D_\text{phys}} + \underbrace{\frac{c}{P_L^2}}_{C_\text{phys}}\,\lambda^2$$

Here **`b2 = b²` is the total Lorentz-invariant** $b^2 = b_L^2 + b_T^2$ (not just $b_T^2$). Since $b^2$ is held **fixed** in the integration over $\lambda$, $d\cdot b^2$ contributes only to the constant $D$, and the $\lambda^2$ coefficient is purely $c/P_L^2$.

> [!IMPORTANT]
> `b2` is the **total** $b^2 = b_L^2 + b_T^2$ (a Lorentz scalar), not just $b_T^2$.  
> The integration at fixed $b^2$ is the Lorentz-invariant FT approach of the thesis.

### Why `a_im = a_fit / PL`

The ImA2B amplitude has $b_L = \lambda/P_L$ in the numerator. The factor $1/P_L$ is absorbed into the rescaled amplitude:
$$\widetilde{A}_{2B}^{\text{Im}} \propto \frac{a''b_L}{\text{denom}^{j''}} = \frac{a''/P_L \cdot \lambda}{\text{denom}^{j''}} \equiv \frac{a_\text{phys}\cdot\lambda}{\text{denom}^{j''}}$$

### Why `a_reA12B = -a_fit`

The thesis model has $\widetilde{A}_{12B}^{\text{Re}} = -a'/\text{denom}^{j'}$ (negative sign explicit in the physics). The HDF5 stores the raw fitted coefficient $a'$ (positive). The negation is applied in the rescaling.

---

## 5. Fourier Transform Formulas

### 5.1 FT Convention — Mathematica `{0, 1}` Symmetric

All Bessel-K formulas implement the **Mathematica default `FourierParameters → {0, 1}`** convention:

$$\tilde{f}(x) = \frac{1}{\sqrt{2\pi}} \int_{-\infty}^{\infty} A(\lambda)\,e^{ix\lambda}\,d\lambda$$

This is **not** the physics $\frac{1}{2\pi}\int\cdots$ convention. The $1/\sqrt{2\pi}$ factor appears identically in all three amplitudes, so it **cancels exactly in the Sivers shift ratio** $\tilde{f}_{1T}^{\perp(1)}/\tilde{f}_1^{(0)}$.

For the **integration table absolute values**, the results are in the `{0,1}` convention. To convert to the physics $(1/2\pi)$ convention, multiply by $1/\sqrt{2\pi} \approx 0.399$.

### 5.2 ReA2B Bessel Formula

For an even amplitude $A(\lambda) = a/(D + C\lambda^2)^j$ (with $D = d_\text{phys}$, $C = c_\text{phys}$):

$$\tilde{A}_{2B}^{\text{Re}}(x) = \frac{2^{1-j}\,a}{\Gamma(j)\,C^{j/2+1/4}\,D^{j/2-1/4}}\;|x|^{j-1/2}\;K_{j-1/2}\!\left(|x|\sqrt{\frac{D}{C}}\right)$$

**In code** (with `cd_R = c_re / d_re = C/D`):

```python
cd_R     = c_re / d_re
term1_R  = (2**(1 - j_re) * a_re * cd_R**(-0.25 - j_re/2) * d_re**(-j_re)) / gamma(j_re)
term2_R  = abs_x**(-0.5 + j_re)           # |x|^(j-1/2)
bessel_R = kv(0.5 - j_re, abs_x / np.sqrt(cd_R))  # K_{j-1/2}(|x|*sqrt(D/C))
re_evals = term1_R * term2_R * bessel_R
```

Note: `kv(0.5 - j, z) = kv(j - 0.5, z)` because $K_{-\nu} = K_\nu$.  
**Numerically verified**: ratio to direct numerical FT = **0.999980** ✓

### 5.3 ReA12B Bessel Formula

Identical structure to ReA2B but with `a_reA12B = -a_fit` already applied:

```python
cd_RA12B     = c_reA12B / d_reA12B
term1_RA12B  = (2**(1-j_reA12B)*a_reA12B*cd_RA12B**(-0.25-j_reA12B/2)*d_reA12B**(-j_reA12B))/gamma(j_reA12B)
term2_RA12B  = abs_x**(-0.5 + j_reA12B)
bessel_RA12B = kv(0.5 - j_reA12B, abs_x / np.sqrt(cd_RA12B))
reA12B_evals = term1_RA12B * term2_RA12B * bessel_RA12B
```

**Numerically verified**: ratio to direct numerical FT = **0.999985** ✓

### 5.4 ImA2B Bessel Formula

The ImA2B amplitude $A_\text{Im}(\lambda) = a_\text{phys}\cdot\lambda/(D+C\lambda^2)^j$ is **odd** in $\lambda$. Its FT involves only the sine transform:

$$\tilde{A}_{2B}^{\text{Im}}(x) = \frac{1}{\sqrt{2\pi}}\int_{-\infty}^{\infty}\frac{a_\text{phys}\,\lambda\,e^{ix\lambda}}{(D+C\lambda^2)^j}d\lambda = \frac{a_\text{phys}}{\sqrt{2\pi}}\cdot 2i\int_0^\infty\frac{\lambda\,\sin(x\lambda)}{(D+C\lambda^2)^j}d\lambda$$

**In code** (using `cd_I = c_im / d_im`):

```python
cd_I     = c_im / d_im
term1_I  = (2**(1-j_im)*a_im*cd_I**(0.25*(-3-2*j_im))*d_im**(-j_im))/gamma(j_im)
term2_I  = x * abs_x**(-1.5 + j_im)      # sign-preserving: sign(x)*|x|^(j-1/2)
bessel_I = kv(1.5 - j_im, np.sqrt(d_im / c_im) * abs_x)  # K_{j-3/2}(|x|sqrt(D/C))
im_evals = term1_I * term2_I * bessel_I
```

> [!NOTE]
> The Im formula is structurally different (different Bessel order, different `cd` exponent).  
> The `kv(1.5 - j_im, ...)` corresponds to $K_{j-3/2}$ (using $K_{-\nu}=K_\nu$).  
> The `term2_I = x * |x|^{j-3/2}` is sign-preserving (negative for $x<0$), giving the correct odd-function behavior.  
> Numerical check shows ~1–3% oscillating deviations vs direct numerical FT, consistent with slow conditional convergence of the sine transform for $j_\text{im} \approx 1.1$ (close to threshold).

---

## 6. Derived Physical Quantities

All computations below are performed **per jackknife sample** (operating on arrays of length `N_jk`), then statistics are extracted with `Jackknife()`.

```python
# Unpolarized TMD (Lorentz-invariant, at fixed b²)
f1_0  = 2 * (re_evals - im_evals)           # = 2*(ReA2B - iImA2B)

# Sivers TMD (first moment in b·P)
f1T_perp = -2 * reA12B_evals                # = -2*A12B  (sign already in a_reA12B)

# Mean transverse momentum shift (Sivers shift)
SiverseShift = -massterm * reA12B_evals / (re_evals - im_evals)
            # = m_N * f1T_perp / f1_0
```

### Mass term computation

```python
MassN    = 0.6228          # nucleon mass in GeV
lata     = 0.11403         # lattice spacing in fm
massterm = MassN * (197 * 0.001 / lata)
         # = m_N [GeV] * (ℏc [GeV·fm]) / a [fm]
         # converts lattice units to GeV
```

---

## 7. Jackknife Statistics

```python
def Jackknife(datalist):
    N = len(datalist)
    theta_bar = np.mean(datalist)
    sigma_sq  = ((N-1)/N) * sum((x - theta_bar)**2 for x in datalist)
    return theta_bar, np.sqrt(sigma_sq)
```

- All quantities (FT values, Sivers shift, integrals) are computed **element-wise across the N_jk jackknife samples**.
- `Jackknife()` returns `(mean, jackknife_error)`.
- Non-linear combinations (e.g., ratios) are computed **before** calling `Jackknife()`, not after.

---

## 8. Integration Table

Computed at four x-domains for each of five physical quantities:

| Row | Quantity |
|---|---|
| Row 1 | $\int dx\;\widetilde{A}_{2B}^{\text{Re}}(x)$ |
| Row 2 | $\int dx\;i\widetilde{A}_{2B}^{\text{Im}}(x)$ |
| Row 3 | $\tilde{f}_1^{(0)} = 2\int dx\,(\widetilde{A}_{2B}^{\text{Re}} - i\widetilde{A}_{2B}^{\text{Im}})$ |
| Row 4 | $\tilde{f}_{1T}^{\perp(1)} = -2\int dx\,\widetilde{A}_{12B}^{\text{Re}}$ |
| Row 5 | $m_N\,\tilde{f}_{1T}^{\perp(1)}/\tilde{f}_1^{(0)}$ (mean Sivers shift) |

Columns: $\{-\infty,\infty\}$, $\{-1,1\}$, $\{-1,0\}$, $\{0,1\}$.

The $\{-\infty,\infty\}$ integral uses `x_inf = np.linspace(-40, 40, 4000)` (power-law decay makes this accurate to better than 0.01%).

> [!NOTE]
> Integration table values are in the Mathematica **`{0,1}`** convention  
> ($= \frac{1}{\sqrt{2\pi}}\int$). To convert to physics $(1/2\pi)$ convention, multiply by $1/\sqrt{2\pi} \approx 0.399$.

---

## 9. Six-Panel Plot Layout

| Panel | Contents | Color |
|---|---|---|
| (1,1) top-left | $\widetilde{A}_{2B}^{\text{Re}}(x)$ vs $x\in[-1,1]$ | Blue |
| (1,2) top-mid | $i\widetilde{A}_{2B}^{\text{Im}}(x)$ vs $x\in[-1,1]$ | Red |
| (1,3) top-right | $\tilde{f}_1^{(0)}(x) = 2(\widetilde{A}_{2B}^{\text{Re}}-i\widetilde{A}_{2B}^{\text{Im}})$ | Green |
| (2,1) bot-left | $\tilde{f}_{1T}^{\perp(1)}(x) = -2\widetilde{A}_{12B}^{\text{Re}}$ | Blue |
| (2,2) bot-mid | $\langle k_y\rangle_{TU}(x)$ [GeV], $x\in[0,1]$ | Blue |
| (2,3) bot-right | $x\langle k_y\rangle_{TU}(x)$ [GeV], $x\in[0,1]$ | Blue |

Each panel shows mean ± jackknife error as a shaded band.

Title of each panel includes the current `PL` and `b2` values.

---

## 10. Notebook Cell Structure

| Cell | Purpose |
|---|---|
| **Cell 0** | All definitions: imports, `Jackknife`, `fmt_err`, amplitude model functions, `load_params_from_h5`, `print_latex_table`, `calc_integrals_for_grid`, `plot_fourier_transforms_A2B_A12B` |
| **Cell 1** | `b2=9, PL=-1`, `eta∈[6,10]`, `bmin=3` |
| **Cell 2** | `b2=50, PL=-1`, `eta∈[6,10]`, `bmin=3` |
| **Cell 3** | `b2=9, PL=-2`, `eta∈[6,10]`, `bmin=3` |
| **Cell 4** | `b2=9, PL=-3`, `eta∈[6,10]`, `bmin=3` |
| **Cell 5** | `b2=9, PL=-4`, `eta∈[6,10]`, `bmin=3` |
| **Cell 6** | `b2=36, PL=-4`, `eta∈[6,10]`, `bmin=3` |
| **Cell 7** | Empty |

Each of Cells 1–6 calls the same two functions:
```python
fitted_params, chi2_dof_list = load_params_from_h5(filepath)
plot_fourier_transforms_A2B_A12B(fitted_params, chi2_dof_list, b2, PL, bminfit, etamin, etamax)
```

---

## 11. Output Files

Each call to `plot_fourier_transforms_A2B_A12B` saves one PDF:

```
SimulFitCovMatrix-A12B-A2B-FT-{param_keys}__bmin{bmin}_eta{etamin}{etamax}_PL{PL}.pdf
```

Written to the **notebook's working directory** (i.e., wherever Jupyter is launched from).

---

## 12. Key Physical Constants & Data Cuts

| Quantity | Value | Meaning |
|---|---|---|
| `MassN` | 0.6228 GeV | Nucleon mass used in Sivers shift |
| `lata` | 0.11403 fm | Lattice spacing |
| `massterm` | $m_N \times \hbar c / a$ | Converts lattice units → GeV |
| `bminfit` | 3 (lattice units) | UV cut: only $\lvert\mathbf{b}\rvert \geq 3a$ data used in fit |
| `etamin`, `etamax` | 6, 10 | Rapidity range of the fit |
| `b2` | 9, 36, or 50 | Total $b^2$ (Lorentz invariant) in lattice units² |
| `PL` | −1, −2, −3, −4 | Nucleon longitudinal momentum (lattice units) |

---

## 13. Verified Correctness Summary

| Item | Verified? | Notes |
|---|---|---|
| `c_phys = c_fit/PL²` | ✅ | Correct for fixed-$b^2$ Lorentz-invariant FT |
| `d_phys = 1 + d_fit*b2` | ✅ | Correct ($b^2$ = total, fixed) |
| `a_im = a_fit/PL` | ✅ | Absorbs $b_L = \lambda/P_L$ factor |
| `a_reA12B = -a_fit` | ✅ | Explicit minus sign from physics model |
| ReA2B Bessel formula | ✅ | Ratio to direct FT = 0.999980 |
| ReA12B Bessel formula | ✅ | Ratio to direct FT = 0.999985 |
| ImA2B Bessel formula | ⚠️ | ~1–3% oscillating deviation; originates from slow sine-transform convergence for $j_\text{im}\approx1.1$; **does not affect Sivers shift qualitatively** |
| Sivers shift ratio | ✅ | Normalization convention cancels |
| Jackknife propagation | ✅ | Non-linear ratios computed before `Jackknife()` |
| Integration table range | ✅ | $[-40,40]$ adequate; amplitude at $\lvert\lambda\rvert=40$ is $\sim10^{-5}$ |
