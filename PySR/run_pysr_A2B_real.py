#!/opt/homebrew/anaconda3/bin/python
"""
run_pysr_A2B_real.py
--------------------
Run Physics-Informed Symbolic Regression (PySR) on the real A2B lattice amplitude data.
Cuts:
  - eta in [6, 10]
  - sqrt(bL^2 + bT^2) >= 3
  - P1 = 1
Custom Loss:
  - Weighted Chi^2 / dof
  - Asymptotic decay penalty at large (bL, bT) coordinates
"""

import os
import h5py
import numpy as np
import pandas as pd
from sympy import exp, symbols, Function
import sympy as sp
from pysr import PySRRegressor

# 1. Load Data
file_path = "/Users/hariprashadravikumar/sivers_TMD_PhD_project/save_h5_A12B_A2B/eta_bL_bT_Amp_Re_Im_err.h5"
data_list = []
P1 = 1

print(f"Loading Real A2B data from {file_path} for Pl-{P1}...")
with h5py.File(file_path, "r") as h5_file:
    for eta in range(6, 10 + 1):
        dataset_name = f"Pl-{P1}/eta_{eta}_bL_bT_ReA2B_err"
        arr = np.array(h5_file[dataset_name])
        data_list.append(arr)

data_for_eta = np.vstack(data_list)

# 2. Apply Cut: sqrt(bL^2 + bT^2) >= 3 (exclude < 3)
bsqmin = 3.0
mask = ~((np.sqrt(data_for_eta[:, 1]**2 + data_for_eta[:, 2]**2) < bsqmin))
filtered_data = data_for_eta[mask]

etabLbT = filtered_data[:, 0:3]   # Columns: eta, bL, bT
A2B = filtered_data[:, 3]          # Target: Re(A2B)
A2Berr = filtered_data[:, 4]       # Error: sigma
epsilon = 1e-12
A2Bweight = np.array([1.0 / max(sigma, epsilon)**2 for sigma in A2Berr])

print(f"Total points after cuts (eta in [6, 10], b >= 3): {len(A2B)}")
print(f"  eta range: [{etabLbT[:, 0].min()}, {etabLbT[:, 0].max()}]")
print(f"  bL range:  [{etabLbT[:, 1].min()}, {etabLbT[:, 1].max()}]")
print(f"  bT range:  [{etabLbT[:, 2].min()}, {etabLbT[:, 2].max()}]")
print(f"  A2B range: [{A2B.min():.6e}, {A2B.max():.6e}]")

# 3. Define Physics-Informed Custom Loss Function (Julia backend)
custom_loss_function_with_penalty = """
using Symbolics

function eval_loss(tree, dataset::Dataset{T,L}, options)::L where {T,L}
    prediction, flag = eval_tree_array(tree, dataset.X, options)
    if !flag
        return L(Inf)
    end

    wmse = sum(((prediction .- dataset.y) .^ 2) .* dataset.weights) / (dataset.n - 3)

    # ---------------------------------------------------
    # Enforce physical asymptotic decay for large bL, bT
    # ---------------------------------------------------
    points = [
        [10.0, 50.0, 1.0],
        [10.0, 80.0, 1.0],
        [10.0, 10.0, 1.0],
        [8.0, 20.0, 1.0],
        [6.0, 30.0, 2.0]
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
"""

# 4. SymPy Mappings
extra_sympy_mappings = {
    "lor": lambda x, y: 1 / (1 + x**2 + y**2)**2,
    "decay": lambda x: exp(-x),
    "gaussian": lambda x: exp(-x**2),
    "pow": lambda x, y: x**y
}

# 5. Output Directory
output_dir = "/Users/hariprashadravikumar/sivers_TMD_PhD_project/PySR/outputs_A2B_real"
os.makedirs(output_dir, exist_ok=True)

# 6. Initialize and Fit PySR Model
model = PySRRegressor(
    niterations=100,
    populations=30,
    maxsize=28,
    binary_operators=[
        "+",
        "-",
        "*",
        "/",
        "pow",
        "lor(x, y) = 1 / (1 + x^2 + y^2)^2"
    ],
    unary_operators=[
        "square",
        "exp",
        "decay(x) = exp(-x)"
    ],
    constraints={
        'pow': (-1, 1),
        'lor': (10, 10),
        'decay': 10
    },
    nested_constraints={
        "exp": {"exp": 0, "decay": 0},
        "decay": {"exp": 0, "decay": 0}
    },
    extra_sympy_mappings=extra_sympy_mappings,
    loss_function=custom_loss_function_with_penalty,
    model_selection="accuracy",
    output_directory=output_dir,
    update=True
)

print("\nStarting PySR Symbolic Regression search...")
model.fit(
    etabLbT,
    A2B,
    weights=A2Bweight,
    variable_names=['n', 'bL', 'bT']
)

print("\n" + "="*80)
print("PYSR SYMBOLIC REGRESSION COMPLETED")
print("="*80)

equations = model.equations_
print("\nDiscovered Pareto Front Equations:")
print(equations[['complexity', 'loss', 'equation', 'sympy_format']])

# Save Hall of Fame table to CSV and Markdown
hof_csv = os.path.join(output_dir, "hall_of_fame_summary.csv")
equations.to_csv(hof_csv, index=True)
print(f"\nSaved equations table to: {hof_csv}")
