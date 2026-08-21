#!/opt/homebrew/anaconda3/bin/python
"""
make_thesis_pysr_plots.py
-------------------------
Generate publication-quality figures and modular LaTeX snippets for PhD thesis:
  1. Benchmark Fits (Figure 1): Multi-panel grid across eta = 6, 7, 8, 10 (C=11, 14, 16, 17)
  2. Straight-Line Test (Figure 2): ln|A2B| vs. b^2 proving the heavy power-law tail and Gaussian failure
  3. LaTeX Snippets (ready for \input{...} in thesis):
      - latex_snippets/pysr_equations_table.tex (Full Pareto front table)
      - latex_snippets/pysr_custom_loss_math.tex (Mathematical formulation of custom loss)
      - latex_snippets/pysr_custom_loss_code.tex (Julia code listing for loss function)
      - latex_snippets/pysr_model_config.tex (PySR operators and hyperparameters table)
"""

import os
import h5py
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from scipy.optimize import curve_fit

# Set plot styles for thesis/publication
plt.rcParams.update({
    'font.family': 'sans-serif',
    'font.size': 11,
    'axes.labelsize': 12,
    'axes.titlesize': 13,
    'legend.fontsize': 9.5,
    'xtick.labelsize': 10,
    'ytick.labelsize': 10,
    'lines.linewidth': 1.8,
    'lines.markersize': 5.5,
    'errorbar.capsize': 2.5
})

PLOTS_DIR = "/Users/hariprashadravikumar/sivers_TMD_PhD_project/plots_for_Thesis/pysr_thesis_plots"
LATEX_DIR = "/Users/hariprashadravikumar/sivers_TMD_PhD_project/plots_for_Thesis/latex_snippets"
os.makedirs(PLOTS_DIR, exist_ok=True)
os.makedirs(LATEX_DIR, exist_ok=True)

# ---------------------------------------------------------
# 1. Load Data
# ---------------------------------------------------------
file_path = "/Users/hariprashadravikumar/sivers_TMD_PhD_project/save_h5_A12B_A2B/eta_bL_bT_Amp_Re_Im_err.h5"
data_list = []
P1 = 1

with h5py.File(file_path, "r") as h5_file:
    for eta in range(6, 10 + 1):
        dataset_name = f"Pl-{P1}/eta_{eta}_bL_bT_ReA2B_err"
        data_list.append(np.array(h5_file[dataset_name]))

all_data = np.vstack(data_list)

# Spatial cut: sqrt(bL^2 + bT^2) >= 3
bsqmin = 3.0
mask = ~((np.sqrt(all_data[:, 1]**2 + all_data[:, 2]**2) < bsqmin))
data = all_data[mask]

eta_all = data[:, 0]
bL_all  = data[:, 1]
bT_all  = data[:, 2]
A2B_all = data[:, 3]
err_all = data[:, 4]
bsq_all = bL_all**2 + bT_all**2
b_mag_all = np.sqrt(bsq_all)

# ---------------------------------------------------------
# 2. Define PySR Models
# ---------------------------------------------------------
def model_c11(n, bL, bT):
    bsq = bL**2 + bT**2
    return 2473.4594 / (n**4 * (1.0 + bsq)**1.4425)

def model_c14(n, bL, bT):
    bsq = bL**2 + bT**2
    return (1.0 / 2.6322825) * (1.0 / (1.0 + bsq)**1.390951) * np.exp(-0.534084 * (n - 8.68932))

def model_c16(n, bL, bT):
    bsq = bL**2 + bT**2
    return (1.0 / 3.5930288) * (1.0 / (1.0 + bsq)**1.258527) * np.exp(-0.468203 * (n - 8.994358)) - 0.00127069

def model_c17(n, bL, bT):
    bsq = bL**2 + bT**2
    return -0.00166217 + (10.461691 / n)**2.3353815 * (1.0 / (1.0 + bsq)**1.214662) / (0.593981 * n)

# ---------------------------------------------------------
# 3. Fit Best-Case Gaussian Baseline
# ---------------------------------------------------------
def gaussian_ansatz(X, A, c):
    n, bL, bT = X
    bsq = bL**2 + bT**2
    return A * np.exp(-c * bsq) * np.exp(-0.5 * (n - 6.0))

popt_gauss, _ = curve_fit(
    gaussian_ansatz,
    (eta_all, bL_all, bT_all),
    A2B_all,
    sigma=err_all,
    absolute_sigma=True,
    p0=[0.05, 0.05]
)
A_gauss, c_gauss = popt_gauss

def model_gaussian(n, bL, bT):
    return gaussian_ansatz((n, bL, bT), A_gauss, c_gauss)

print(f"Optimal Gaussian Fit Baseline: A = {A_gauss:.5e}, c = {c_gauss:.5e}")


# ---------------------------------------------------------
# FIGURE 1: Benchmark Fits Multi-Panel Plot
# ---------------------------------------------------------
def plot_benchmark_fits():
    print("Generating Figure 1: Benchmark Fits Multi-Panel Plot...")
    eta_values = [6, 7, 8, 10]
    
    fig, axes = plt.subplots(2, 2, figsize=(14.5, 9.0), sharey=True)
    axes = axes.flatten()

    colors = ['#1f77b4', '#ff7f0e', '#2ca02c', '#d62728', '#9467bd', '#8c564b', '#e377c2']
    unique_bT = np.sort(np.unique(bT_all))

    bL_cont = np.linspace(-8.5, 8.5, 300)

    for idx, eta_val in enumerate(eta_values):
        ax = axes[idx]
        mask_eta = (eta_all == eta_val)
        bL_sub = bL_all[mask_eta]
        bT_sub = bT_all[mask_eta]
        A2B_sub = A2B_all[mask_eta]
        err_sub = err_all[mask_eta]

        for i, bt in enumerate(unique_bT):
            col = colors[i % len(colors)]
            mask_bt = (bT_sub == bt)

            if np.any(mask_bt):
                ax.errorbar(
                    bL_sub[mask_bt],
                    A2B_sub[mask_bt],
                    yerr=err_sub[mask_bt],
                    fmt='o',
                    color=col,
                    zorder=4
                )

            y_c14 = model_c14(eta_val, bL_cont, bt)
            ax.plot(bL_cont, y_c14, color=col, linestyle='-', alpha=0.9, lw=1.8, zorder=3)

            y_c16 = model_c16(eta_val, bL_cont, bt)
            ax.plot(bL_cont, y_c16, color=col, linestyle='--', alpha=0.8, lw=1.6, zorder=2)

            y_c11 = model_c11(eta_val, bL_cont, bt)
            ax.plot(bL_cont, y_c11, color=col, linestyle=':', alpha=0.65, lw=1.4, zorder=1)

            y_c17 = model_c17(eta_val, bL_cont, bt)
            ax.plot(bL_cont, y_c17, color=col, linestyle='-.', alpha=0.7, lw=1.4, zorder=1)

        ax.set_title(f'$\\eta = {eta_val}$', fontweight='bold', fontsize=12.5)
        ax.set_xlabel('$b_L / a$', fontsize=11.5)
        if idx % 2 == 0:
            ax.set_ylabel('$\\tilde{A}_{2B}^{\\mathrm{Re}}(\\eta, b_L, b_T)$', fontsize=11.5)
        ax.grid(True, linestyle='--', alpha=0.35)
        ax.set_xlim(-8.5, 8.5)

    legend_handles = []
    legend_labels = []

    for i, bt in enumerate(unique_bT):
        col = colors[i % len(colors)]
        h = Line2D([0], [0], marker='o', color=col, linestyle='', markersize=6)
        legend_handles.append(h)
        legend_labels.append(f'$b_T = {int(bt)}a$')

    h_c14 = Line2D([0], [0], color='black', linestyle='-', lw=1.8)
    h_c16 = Line2D([0], [0], color='black', linestyle='--', lw=1.6)
    h_c11 = Line2D([0], [0], color='black', linestyle=':', lw=1.4)
    h_c17 = Line2D([0], [0], color='black', linestyle='-.', lw=1.4)
    
    legend_handles.extend([h_c14, h_c16, h_c11, h_c17])
    legend_labels.extend(['$C=14$ (Exp)', '$C=16$ (Exp+Off)', '$C=11$ (Power $\\eta^{-4}$)', '$C=17$ (Power $\\eta^{-3.3}$)'])

    fig.legend(
        legend_handles,
        legend_labels,
        loc='center left',
        bbox_to_anchor=(0.87, 0.5),
        ncol=2,
        frameon=True,
        fontsize=9.5,
        columnspacing=1.0,
        handletextpad=0.4
    )

    title_text = "PySR Discovered Analytical Models on Lattice $\\tilde{A}_{2B}^{\\mathrm{Re}}$ Data"
    eq_row1 = r"$\mathbf{C=14:}\; \frac{39.71}{(1 + b^2)^{1.39}} e^{-0.534\eta} \; (\chi^2=3.93) \qquad\quad \mathbf{C=16:}\; \frac{245.5}{(1 + b^2)^{1.26}} e^{-0.468\eta} - 0.0013 \; (\chi^2=2.03)$"
    eq_row2 = r"$\mathbf{C=11:}\; \frac{2473.5}{\eta^4 (1 + b^2)^{1.44}} \; (\chi^2=5.16) \qquad\qquad\quad \mathbf{C=17:}\; \frac{1}{\eta}\left(\frac{10.46}{\eta}\right)^{2.34} \frac{1.68}{(1 + b^2)^{1.21}} - 0.0017 \; (\chi^2=1.99)$"
    
    full_banner = f"{title_text}\n{eq_row1}\n{eq_row2}"
    fig.suptitle(full_banner, y=1.05, fontsize=11.5, linespacing=1.35)
    plt.subplots_adjust(top=0.86, right=0.86, hspace=0.25, wspace=0.15)
    
    save_path = os.path.join(PLOTS_DIR, "01_A2B_PySR_Benchmark_Fits.pdf")
    plt.savefig(save_path, bbox_inches='tight', dpi=300)
    plt.close()
    print(f"Saved: {save_path}")


# ---------------------------------------------------------
# FIGURE 2: The Straight-Line Test (ln|A2B| vs. b^2)
# ---------------------------------------------------------
def plot_straight_line_test():
    print("Generating Figure 2: Straight-Line Test (ln|A2B| vs. b^2)...")
    eta_values = [6, 7, 8, 10]
    fig, axes = plt.subplots(2, 2, figsize=(13, 9.5), sharey=True)
    axes = axes.flatten()

    for idx, eta_val in enumerate(eta_values):
        ax = axes[idx]
        mask_eta = (eta_all == eta_val)
        
        bL_sub = bL_all[mask_eta]
        bT_sub = bT_all[mask_eta]
        A2B_sub = A2B_all[mask_eta]
        err_sub = err_all[mask_eta]
        bsq_sub = bL_sub**2 + bT_sub**2

        # Plot discrete lattice data points vs b^2
        ax.errorbar(
            bsq_sub,
            A2B_sub,
            yerr=err_sub,
            fmt='o',
            color='black',
            markersize=5.5,
            alpha=0.75,
            label='Lattice Data ($b \\geq 3a$)' if idx == 0 else "",
            zorder=4
        )

        # Continuous comparison lines vs b^2
        bsq_cont = np.linspace(9.0, 75.0, 300)
        
        # Power-Law PySR Model C=14
        y_pysr = (1.0 / 2.6322825) * (1.0 / (1.0 + bsq_cont)**1.390951) * np.exp(-0.534084 * (eta_val - 8.68932))
        ax.plot(
            bsq_cont,
            y_pysr,
            'b-',
            lw=2.2,
            label='PySR Power-Law $\\propto (1 + b^2)^{-1.39}$' if idx == 0 else "",
            zorder=3
        )

        # Best-Fit Gaussian Model (Straight line in semi-log)
        y_gauss = A_gauss * np.exp(-c_gauss * bsq_cont) * np.exp(-0.5 * (eta_val - 6.0))
        ax.plot(
            bsq_cont,
            y_gauss,
            'r--',
            lw=2.2,
            label=f'Gaussian Ansatz $\\propto e^{{-{c_gauss:.3f}b^2}}$ (Straight line)' if idx == 0 else "",
            zorder=2
        )

        ax.set_yscale('log')
        ax.set_title(f'$\\eta = {eta_val}$', fontweight='bold', fontsize=12.5)
        ax.set_xlabel('Spatial Separation Squared $(b/a)^2 = b_L^2 + b_T^2$', fontsize=11)
        if idx % 2 == 0:
            ax.set_ylabel('$\\tilde{A}_{2B}^{\\mathrm{Re}}$ (Log Scale)', fontsize=11.5)
        ax.grid(True, which='both', linestyle='--', alpha=0.35)
        ax.set_xlim(8, 76)

    fig.legend(
        loc='upper center',
        bbox_to_anchor=(0.5, 0.98),
        ncol=3,
        frameon=True,
        fontsize=11
    )

    title_text = "Straight-Line Test: Rejection of Gaussian Falloff in Favor of Heavy Power-Law Tail"
    subtitle_text = "On a log(A) vs. b² axis, a Gaussian is strictly a straight line; the lattice data bends upward into a power-law."
    fig.suptitle(f"{title_text}\n{subtitle_text}", y=1.04, fontsize=13, fontweight='bold', linespacing=1.3)
    plt.tight_layout()

    save_path = os.path.join(PLOTS_DIR, "02_Gaussian_StraightLine_Test.pdf")
    plt.savefig(save_path, bbox_inches='tight', dpi=300)
    plt.close()
    print(f"Saved: {save_path}")


# ---------------------------------------------------------
# 4. Export LaTeX Snippets (Ready for \\input{...} in Thesis)
# ---------------------------------------------------------
def export_latex_snippets():
    print("\nExporting Modular LaTeX (.tex) Snippets...")

    # ---------------------------------------------------------
    # A. Pareto Front Equations Table
    # ---------------------------------------------------------
    equations_table_tex = r"""% Auto-generated by make_thesis_pysr_plots.py
% Usage in thesis: \input{latex_snippets/pysr_equations_table.tex}
\begin{table}[htbp]
\centering
\small
\renewcommand{\arraystretch}{1.3}
\caption{Pareto front of analytical candidate models discovered by \texttt{PySR} for the real amplitude $\tilde{A}_{2B}^{\text{Re}}(\eta, b_L, b_T)$, ranked by mathematical complexity and loss. The optimal physics-informed models ($C=14$ and $C=16$) are highlighted.}
\label{tab:pysr_pareto_front}
\begin{tabular}{c c l p{5.2cm}}
\hline\hline
\textbf{Complexity} & \textbf{Loss} & \textbf{Discovered Analytical Expression} $\tilde{A}_{2B}^{\text{Re}}(\eta, b_L, b_T)$ & \textbf{Physical Interpretation} \\
\hline
1  & 276.43 & $0.00504$ & Flat constant baseline \\
3  & 171.56 & $(0.4988)^\eta \approx e^{-0.695\eta}$ & Pure exponential in $\eta$ only \\
4  & 167.57 & $\exp\left(-\eta^{0.808}\right)$ & Stretched exponential in $\eta$ \\
7  & 68.93  & $\frac{11.58 - \eta}{(1 + b_L^2 + b_T^2)^2}$ & Linear in $\eta$ $\times$ standard Lorentzian \\
9  & 30.81  & $\frac{10.16 - \eta}{(1 + b_L^2 + b_T^2)^{1.78}}$ & Linear in $\eta$ $\times$ generalized Lorentzian \\
11 & 5.16   & $\frac{2473.5}{\eta^4 (1 + b_L^2 + b_T^2)^{1.44}}$ & Power-law in $\eta$ ($\eta^{-4}$) $\times$ Power-law in $b$ \\
12 & 4.76   & $\left(1 - \frac{14.49}{\eta}\right)^2 \frac{1}{(1 + b_L^2 + b_T^2)^{1.46}}$ & Rational in $\eta$ $\times$ Power-law in $b$ \\
\hline
\textbf{14} & \textbf{3.93} & $\mathbf{\frac{39.71}{(1 + b_L^2 + b_T^2)^{1.39}} \, e^{-0.534\eta}}$ & \textbf{Optimal factorized: $e^{-0.534\eta} \times (1 + b^2)^{-1.39}$} \\
\textbf{16} & \textbf{2.03} & $\mathbf{\frac{245.5}{(1 + b_L^2 + b_T^2)^{1.26}} \, e^{-0.468\eta} - 0.00127}$ & \textbf{Best-fit factorized with offset ($\chi^2/\text{dof} = 2.03$)} \\
\hline
17 & 1.99   & $\frac{1}{\eta}\left(\frac{10.46}{\eta}\right)^{2.34} \frac{1.68}{(1 + b_L^2 + b_T^2)^{1.21}} - 0.00166$ & High-order power-law $\eta^{-3.34} \times$ Power-law in $b$ \\
18 & 1.91   & $\frac{0.28}{\eta^2}(17.98 - \eta)^2 \frac{1}{(1 + b_L^2 + b_T^2)^{1.25}} - 0.00137$ & Polynomial in $\eta$ $\times$ Power-law in $b$ \\
19 & 1.76   & $\frac{1}{\eta}\left(\frac{10.38}{\eta}\right)^{2.37}\left(\frac{1.39}{(1 + b^2)^{1.13}} - 0.00322\right) - 0.00149$ & Asymptotic refinement \\
21 & 1.76   & $\frac{1}{\eta}\left(\frac{10.30}{\eta}\right)^{2.43} \frac{1.40}{(1 + b^2)^{1.13}} - \frac{0.00319}{\eta} - 0.00139$ & Multi-scale refinement \\
\hline\hline
\end{tabular}
\end{table}
"""
    table_path = os.path.join(LATEX_DIR, "pysr_equations_table.tex")
    with open(table_path, "w") as f:
        f.write(equations_table_tex.strip() + "\n")
    print(f"Saved: {table_path}")

    # ---------------------------------------------------------
    # B. Custom Loss Function (Mathematical Formulation)
    # ---------------------------------------------------------
    custom_loss_math_tex = r"""% Auto-generated by make_thesis_pysr_plots.py
% Usage in thesis: \input{latex_snippets/pysr_custom_loss_math.tex}
\begin{align}
    \mathcal{L}_{\text{custom}} &= \mathcal{L}_{\text{base}} + \epsilon \, \mathcal{P}_{\text{asymptotic}} \label{eq:pysr_custom_loss_total} \\[6pt]
    \mathcal{L}_{\text{base}} &= \frac{\chi^2}{\text{dof}} = \frac{1}{N - 3} \sum_{i=1}^{N} \left( \frac{\tilde{A}_{2B}^{\text{Re, lattice}}(i) - \tilde{A}_{2B}^{\text{Re, model}}(i)}{\sigma_i} \right)^2 \label{eq:pysr_chi2_base} \\[6pt]
    \mathcal{P}_{\text{asymptotic}} &= \sum_{p \in \Omega_{\text{asymp}}} \left( \tilde{A}_{2B}^{\text{Re, model}}(\eta_p, b_{L, p}, b_{T, p}) \right)^2 \label{eq:pysr_penalty_def}
\end{align}
where $\Omega_{\text{asymp}} = \{(10, 50, 1),\, (10, 80, 1),\, (10, 10, 1),\, (8, 20, 1),\, (6, 30, 2)\}$ defines the evaluation coordinates in the asymptotic region $(b_L \gg 1)$, and $\epsilon = 0.1$ is the penalty regularizer that enforces asymptotic decay toward zero for Fourier integrability.
"""
    loss_math_path = os.path.join(LATEX_DIR, "pysr_custom_loss_math.tex")
    with open(loss_math_path, "w") as f:
        f.write(custom_loss_math_tex.strip() + "\n")
    print(f"Saved: {loss_math_path}")

    # ---------------------------------------------------------
    # C. Custom Loss Function (Julia Code Listing)
    # ---------------------------------------------------------
    custom_loss_code_tex = r"""% Auto-generated by make_thesis_pysr_plots.py
% Usage in thesis: \input{latex_snippets/pysr_custom_loss_code.tex}
\begin{verbatim}
using Symbolics

function eval_loss(tree, dataset::Dataset{T,L}, options)::L where {T,L}
    prediction, flag = eval_tree_array(tree, dataset.X, options)
    if !flag
        return L(Inf)
    end

    # 1. Base Chi-Squared per degree of freedom
    wmse = sum(((prediction .- dataset.y) .^ 2) .* dataset.weights) / (dataset.n - 3)

    # 2. Physics boundary condition: penalty for growth at large b
    points = [
        [10.0, 50.0, 1.0],
        [10.0, 80.0, 1.0],
        [10.0, 10.0, 1.0],
        [8.0,  20.0, 1.0],
        [6.0,  30.0, 2.0]
    ]

    penalty = 0.0
    for p in points
        Xp = reshape(p, :, 1)
        y_pred, ok = eval_tree_array(tree, Xp, options)
        if ok
            penalty += (y_pred[1])^2
        else
            penalty += 1e6
        end
    end

    return L(wmse + 0.1 * penalty)
end
\end{verbatim}
"""
    loss_code_path = os.path.join(LATEX_DIR, "pysr_custom_loss_code.tex")
    with open(loss_code_path, "w") as f:
        f.write(custom_loss_code_tex.strip() + "\n")
    print(f"Saved: {loss_code_path}")

    # ---------------------------------------------------------
    # D. PySR Regressor Model Configuration Table
    # ---------------------------------------------------------
    model_config_tex = r"""% Auto-generated by make_thesis_pysr_plots.py
% Usage in thesis: \input{latex_snippets/pysr_model_config.tex}
\begin{table}[htbp]
\centering
\small
\renewcommand{\arraystretch}{1.25}
\caption{Hyperparameter and operator configuration for the Physics-Informed \texttt{PySR} Symbolic Regression search.}
\label{tab:pysr_config}
\begin{tabular}{l l}
\hline\hline
\textbf{Configuration Parameter} & \textbf{Specification / Value} \\
\hline
Binary Operators & $+$, $-$, $\times$, $/$, $\text{pow}(x, y) = x^y$, $\text{lor}(x, y) = \frac{1}{(1 + x^2 + y^2)^2}$ \\
Unary Operators  & $\text{square}(x) = x^2$, $\exp(x)$, $\text{decay}(x) = \exp(-x)$ \\
Operator Constraints & $\text{pow}: (-1, 1)$, $\text{lor}: (10, 10)$, $\text{decay}: 10$ \\
Nesting Constraints & $\exp \to \exp: 0$, $\text{decay} \to \text{decay}: 0$, $\exp \to \text{decay}: 0$ \\
Populations & $30$ \\
Evolution Generations & $100$ \\
Maximum Tree Complexity & $28$ \\
Loss Function & Physics-Informed Weighted $\chi^2/\text{dof} + \epsilon \, \mathcal{P}_{\text{asymptotic}}$ ($\epsilon = 0.1$) \\
Input Features & $n$ (Staple length $\eta$), $b_L$ (Longitudinal separation), $b_T$ (Transverse separation) \\
Target Observable & $\tilde{A}_{2B}^{\text{Re}}(\eta, b_L, b_T)$ (Lattice momentum $P_1 = 1$, $b \ge 3a$, $\eta \in [6, 10]$) \\
\hline\hline
\end{tabular}
\end{table}
"""
    config_path = os.path.join(LATEX_DIR, "pysr_model_config.tex")
    with open(config_path, "w") as f:
        f.write(model_config_tex.strip() + "\n")
    print(f"Saved: {config_path}")


if __name__ == "__main__":
    plot_benchmark_fits()
    plot_straight_line_test()
    export_latex_snippets()
    print(f"\nAll thesis figures and LaTeX snippets successfully generated!")
