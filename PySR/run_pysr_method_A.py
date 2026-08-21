#!/opt/homebrew/anaconda3/bin/python
"""
run_pysr_method_A.py
--------------------
Run PySR without the rigid Lorentzian operator to organically discover:
  A_2B(eta, bL, bT) = a * exp(-f * eta) / (1 + c * bL^2 + d * bT^2)^j
"""

import os
import h5py
import numpy as np
import pandas as pd
from sympy import exp, symbols
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

# 2. Apply Cut: sqrt(bL^2 + bT^2) >= 3
bsqmin = 3.0
mask = ~((np.sqrt(data_for_eta[:, 1]**2 + data_for_eta[:, 2]**2) < bsqmin))
filtered_data = data_for_eta[mask]

etabLbT = filtered_data[:, 0:3]   # Columns: eta, bL, bT
A2B = filtered_data[:, 3]          # Target: Re(A2B)
A2Berr = filtered_data[:, 4]       # Error: sigma
epsilon = 1e-12
A2Bweight = np.array([1.0 / max(sigma, epsilon)**2 for sigma in A2Berr])

print(f"Total points after cuts (eta in [6, 10], b >= 3): {len(A2B)}")

# 3. Physics-Informed Custom Loss Function
custom_loss_function_with_penalty = """
using Symbolics

function eval_loss(tree, dataset::Dataset{T,L}, options)::L where {T,L}
    prediction, flag = eval_tree_array(tree, dataset.X, options)
    if !flag
        return L(Inf)
    end

    wmse = sum(((prediction .- dataset.y) .^ 2) .* dataset.weights) / (dataset.n - 3)

    # Enforce decay at large distances
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
    "decay": lambda x: exp(-x),
    "pow": lambda x, y: x**y
}

output_dir = "/Users/hariprashadravikumar/sivers_TMD_PhD_project/PySR/outputs_method_A"
os.makedirs(output_dir, exist_ok=True)

# 5. Method A PySR Configuration (Pure standard operators)
model = PySRRegressor(
    niterations=150,
    populations=35,
    maxsize=30,
    binary_operators=[
        "+",
        "-",
        "*",
        "/",
        "pow"
    ],
    unary_operators=[
        "square",
        "exp",
        "decay(x) = exp(-x)"
    ],
    constraints={
        'pow': (-1, 1),
        'decay': 10
    },
    nested_constraints={
        "exp": {"exp": 0, "decay": 0},
        "decay": {"exp": 0, "decay": 0}
    },
    optimizer_nrestarts=4,   # Extra restarts for precise constant tuning (a, f, c, d, j)
    extra_sympy_mappings=extra_sympy_mappings,
    loss_function=custom_loss_function_with_penalty,
    model_selection="accuracy",
    output_directory=output_dir,
    update=True
)

print("\nStarting Method A PySR search (building from fundamental operators)...")
model.fit(
    etabLbT,
    A2B,
    weights=A2Bweight,
    variable_names=['n', 'bL', 'bT']
)

print("\n" + "="*80)
print("METHOD A PYSR REGRESSION COMPLETED")
print("="*80)

equations = model.equations_
print("\nDiscovered Equations Table:")
for i, row in equations.iterrows():
    print(f"Complexity {int(row['complexity']):2d} | Loss: {row['loss']:.4e} | Eq: {row['sympy_format']}")

hof_csv = os.path.join(output_dir, "hall_of_fame_summary.csv")
equations.to_csv(hof_csv, index=True)
print(f"\nSaved equations table to: {hof_csv}")
