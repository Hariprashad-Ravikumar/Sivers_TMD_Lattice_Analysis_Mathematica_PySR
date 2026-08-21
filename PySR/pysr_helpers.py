"""
pysr_helpers.py
---------------
Shared PySR setup for Sivers TMD Lattice Analysis.

Usage in any notebook cell:
    from pysr_helpers import extra_sympy_mappings, custom_loss_function, custom_loss_function_with_penalty
"""

from sympy import exp, Function

# ---------------------------------------------------------------------------
# Sympy mappings for custom Julia operators
# These tell PySR/sympy how to interpret the custom operators symbolically
# so that predict(), latex(), and export functions work correctly.
# ---------------------------------------------------------------------------
extra_sympy_mappings = {
    "gaussian": lambda x: exp(-x**2),          # gaussian(x) = exp(-x^2)
    "decay":    lambda x: exp(-x),              # decay(x)    = exp(-x)
    "Lorentzian": lambda x, y: 1 / (y + x**2), # Lorentzian(x, y) = 1/(y + x^2)
}

# ---------------------------------------------------------------------------
# Custom Julia loss function: pure Chi-Squared (weighted MSE)
# PySR applies its own parsimony penalty on top to control complexity.
# ---------------------------------------------------------------------------
custom_loss_function = """
function eval_loss(tree, dataset::Dataset{T,L}, options)::L where {T,L}
    prediction, flag = eval_tree_array(tree, dataset.X, options)
    if !flag
        return L(Inf)
    end
    chi_sq = sum(((prediction .- dataset.y) .^ 2) .* dataset.weights)
    return L(chi_sq)
end
"""

# ---------------------------------------------------------------------------
# Custom Julia loss function WITH complexity penalty
# Penalises overly complex expressions beyond a given complexity threshold.
# ---------------------------------------------------------------------------
custom_loss_function_with_penalty = """
function eval_loss(tree, dataset::Dataset{T,L}, options)::L where {T,L}
    prediction, flag = eval_tree_array(tree, dataset.X, options)
    if !flag
        return L(Inf)
    end
    chi_sq = sum(((prediction .- dataset.y) .^ 2) .* dataset.weights)
    complexity = compute_complexity(tree, options)
    penalty = (complexity > 15) ? L(0.1) * (complexity - 15) : L(0.0)
    return L(chi_sq) + penalty
end
"""
