#!/usr/bin/env python
# coding: utf-8
"""
Factorization test for M(P.b, b^2) at a SINGLE PL and SINGLE eta (no
combining across PL, unlike Factorization_CrossRatioTest.py).

Why not a cross-ratio here: at fixed PL=-1, eta=8.0, the measured (bL,bT)
grid is sparse -- e.g. P.b=1 only has b^2 in {2,5}, P.b=2 only {5,8,20},
P.b=4 only {17,20,32}, etc. No two P.b values share 2+ b^2 values (the
"rectangle" a cross-ratio needs). Viewed as a bipartite graph (P.b nodes,
b^2 nodes, edge = measured point), this data is a forest (no cycles): the
saturated additive model log M = log g(P.b) + log h(b^2) always has zero
residual degrees of freedom on a tree, so it fits ANY data exactly,
factorized or not. A model-independent ratio test is therefore
mathematically impossible from this slice alone.

What IS possible: P.b = 1, 2, 3, 4 each have >= 2 measured b^2 points
individually, so the LOCAL logarithmic slope d(log|M|)/d(b^2) can be
estimated independently at each of those P.b values, using only that
P.b's own points -- no cross-P.b matching required. If M factorizes and
h(b^2) is reasonably smooth (e.g. the exp/power-law-in-b^2 shape already
used in this repo's SimulFit ansatz), that local slope should come out
the same at every P.b. If the slopes disagree well beyond their jackknife
errors, that's direct evidence against factorization -- with the one
caveat that this assumes local smoothness of h, since a fully
assumption-free test isn't available here.

Outputs (visual only, no chi^2/p-value):
  Factorization_SinglePL_Shapes_PL{PL}.pdf       -- log|M| vs b^2, one line per P.b
  Factorization_SinglePL_LocalSlope_PL{PL}.pdf   -- local slope vs P.b, one point per P.b
"""

import h5py
import numpy as np
import matplotlib.pyplot as plt
from collections import defaultdict

PATH_BASE = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/TMD_fit/h5data"
PL = -1
TARGET_ETA = 8.0
AMPLITUDES = ["ReA2B", "ImA2B", "ReA12B", "ImA12B"]

AMP_LABELS = {
    "ReA2B":  r"$\tilde{A}_{2B}^{Re}$",
    "ImA2B":  r"$\tilde{A}_{2B}^{Im}$",
    "ReA12B": r"$\tilde{A}_{12B}^{Re}$",
    "ImA12B": r"$\tilde{A}_{12B}^{Im}$",
}


def jackknife_vectorized(samples):
    """samples: (N_points, N_JK) -> (mean, err), each (N_points,)."""
    N = samples.shape[1]
    theta_bar = np.mean(samples, axis=1)
    squared_diffs = np.square(samples - theta_bar[:, None])
    sigma_sq = ((N - 1) / N) * np.sum(squared_diffs, axis=1)
    error = np.sqrt(sigma_sq)
    return theta_bar, error


def load_single_pl(path_base, amp_name, pl=PL, target_eta=TARGET_ETA):
    """
    Loads jackknife samples for `amp_name` at a single PL, filtered to
    target_eta and to P.b > 0 (canonical half; ReA2B/ReA12B are exactly
    even and ImA2B/ImA12B exactly odd under P.b -> -P.b in this data, so
    the negative half carries no independent information).

    Replica measurements at the same (P.b, b^2) -- here from bT -> -bT --
    are averaged together rather than one being discarded.

    Returns {(P.b, b^2): averaged_jackknife_sample_array}.
    """
    filepath = f"{path_base}/{amp_name}_PL{pl}_jackknife_data.h5"
    with h5py.File(filepath, "r") as f:
        raw_data = f["Dataset1"][:]

    kin = raw_data[:, 0:3]
    samples = raw_data[:, 3:]
    eta, bL, bT = kin[:, 0], kin[:, 1], kin[:, 2]

    mask = np.isclose(eta, target_eta) & (bL > 0)
    bL_f, bT_f, samples_f = bL[mask], bT[mask], samples[mask]

    replicas = defaultdict(list)
    for i in range(len(bL_f)):
        P_dot_b = np.round(-1.0 * float(pl) * bL_f[i], 5)
        b_sq = np.round(bL_f[i] ** 2 + bT_f[i] ** 2, 5)
        replicas[(P_dot_b, b_sq)].append(samples_f[i])

    return {key: np.mean(arrs, axis=0) for key, arrs in replicas.items()}


def local_log_slope(aggregated_data, pb):
    """
    For a single P.b value, fits log|M| = a - c*b^2 across that P.b's own
    b^2 points (per jackknife sample, vectorized), returning (b2_values,
    slope_mean, slope_err). Requires >= 2 b^2 points at this P.b; returns
    None otherwise.
    """
    b2_vals = sorted(b2 for (p, b2) in aggregated_data if p == pb)
    if len(b2_vals) < 2:
        return None

    b2_arr = np.array(b2_vals)
    sample_stack = np.stack([aggregated_data[(pb, b2)] for b2 in b2_vals], axis=0)  # (n_b2, N_JK)
    log_abs = np.log(np.abs(sample_stack))  # (n_b2, N_JK)

    # Per-jackknife-sample linear fit: log|M| = a + slope*b2
    N_JK = log_abs.shape[1]
    design = np.vstack([b2_arr, np.ones_like(b2_arr)]).T  # (n_b2, 2)
    coeffs, *_ = np.linalg.lstsq(design, log_abs, rcond=None)  # (2, N_JK)
    slope_samples = coeffs[0, :]  # (N_JK,)

    slope_mean, slope_err = jackknife_vectorized(slope_samples.reshape(1, -1))
    return b2_arr, slope_mean[0], slope_err[0]


def plot_shapes(all_data):
    """log|M| vs b^2, one line per P.b, 2x2 panel (one per amplitude)."""
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle(fr'$\log|M(P\cdot b, b^2)|$ vs $b^2$ at fixed $P_L={PL}$, $\eta|v|/a={TARGET_ETA:g}$',
                 fontsize=15, fontweight='bold')
    axes_flat = axes.flatten()
    colors = plt.cm.viridis(np.linspace(0.1, 0.9, 8))

    for idx, amp_name in enumerate(AMPLITUDES):
        ax = axes_flat[idx]
        data = all_data[amp_name]
        all_pb = sorted(set(p for (p, b2) in data))

        for c, pb in zip(colors, all_pb):
            b2_vals = sorted(b2 for (p, b2) in data if p == pb)
            means = []
            errs = []
            for b2 in b2_vals:
                m, e = jackknife_vectorized(data[(pb, b2)].reshape(1, -1))
                means.append(np.log(np.abs(m[0])))
                errs.append(e[0] / np.abs(m[0]))  # d(log|x|) ~ err/|x|
            ax.errorbar(b2_vals, means, yerr=errs, fmt='o-', color=c, label=f'P.b={pb:g}', capsize=3)

        ax.set_title(f'{AMP_LABELS[amp_name]}', fontsize=14)
        ax.set_xlabel('$b^2$', fontsize=12)
        ax.set_ylabel(r'$\log|M|$', fontsize=12)
        ax.grid(True, linestyle='--', alpha=0.5)
        ax.legend(fontsize='small', loc='best', ncol=2)

    plt.tight_layout(rect=[0, 0, 1, 0.95])
    return fig


def plot_local_slopes(all_slopes):
    """Local log-slope d(log|M|)/d(b^2) vs P.b, 2x2 panel (one per amplitude)."""
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    fig.suptitle(
        fr'Local slope $\dfrac{{d\log|M|}}{{db^2}}$ per $P\cdot b$ (fixed $P_L={PL}$, $\eta|v|/a={TARGET_ETA:g}$)'
        '\nFlat vs P.b $\\Rightarrow$ consistent with a common $h(b^2)$ shape (factorized)',
        fontsize=14, fontweight='bold'
    )
    axes_flat = axes.flatten()

    for idx, amp_name in enumerate(AMPLITUDES):
        ax = axes_flat[idx]
        entries = all_slopes[amp_name]

        if not entries:
            ax.text(0.5, 0.5, "Not enough points", ha='center', va='center')
            ax.set_title(AMP_LABELS[amp_name], fontsize=14)
            continue

        pbs = [e[0] for e in entries]
        means = [e[1] for e in entries]
        errs = [e[2] for e in entries]

        weights = 1.0 / np.array(errs) ** 2
        weighted_mean = np.sum(np.array(means) * weights) / np.sum(weights)
        ax.axhline(weighted_mean, color='black', linestyle='--', linewidth=1.5,
                   label=f'weighted mean = {weighted_mean:.4f}', zorder=1)
        ax.errorbar(pbs, means, yerr=errs, fmt='o', color='#e6194b', capsize=4, zorder=5)

        ax.set_title(f'{AMP_LABELS[amp_name]}', fontsize=14)
        ax.set_xlabel('$P \\cdot b$', fontsize=12)
        ax.set_ylabel(r'$d\log|M|/db^2$', fontsize=12)
        ax.grid(True, linestyle='--', alpha=0.5)
        ax.legend(fontsize='small', loc='best')

    plt.tight_layout(rect=[0, 0, 1, 0.93])
    return fig


def main():
    print(f"Loading jackknife samples at PL={PL}, eta={TARGET_ETA}...")
    all_data = {}
    all_slopes = {}

    for amp_name in AMPLITUDES:
        data = load_single_pl(PATH_BASE, amp_name, pl=PL, target_eta=TARGET_ETA)
        all_data[amp_name] = data

        all_pb = sorted(set(p for (p, b2) in data))
        print(f"\n{amp_name}: P.b values = {all_pb}")
        for pb in all_pb:
            b2_here = sorted(b2 for (p, b2) in data if p == pb)
            print(f"  P.b={pb:g}: b^2 = {b2_here}")

        entries = []
        for pb in all_pb:
            result = local_log_slope(data, pb)
            if result is None:
                continue
            b2_arr, slope_mean, slope_err = result
            entries.append((pb, slope_mean, slope_err))
            print(f"  local slope at P.b={pb:g} (using b^2={list(b2_arr)}): "
                  f"{slope_mean:.5f} +/- {slope_err:.5f}")
        all_slopes[amp_name] = entries

    print("\nPlotting...")
    fig1 = plot_shapes(all_data)
    fig1.savefig(f"Factorization_SinglePL_Shapes_PL{PL}.pdf", format='pdf', dpi=300, bbox_inches='tight')
    print(f"Saved: Factorization_SinglePL_Shapes_PL{PL}.pdf")

    fig2 = plot_local_slopes(all_slopes)
    fig2.savefig(f"Factorization_SinglePL_LocalSlope_PL{PL}.pdf", format='pdf', dpi=300, bbox_inches='tight')
    print(f"Saved: Factorization_SinglePL_LocalSlope_PL{PL}.pdf")


if __name__ == "__main__":
    main()
