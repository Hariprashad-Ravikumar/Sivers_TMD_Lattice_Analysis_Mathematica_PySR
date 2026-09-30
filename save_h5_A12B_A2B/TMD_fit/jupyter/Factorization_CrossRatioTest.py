#!/usr/bin/env python
# coding: utf-8
"""
Model-independent cross-ratio test for factorization of the raw lattice
amplitude M(P.b, b^2) [ReA2B, ImA2B, ReA12B, ImA12B], combined across
PL in {-1,-2,-3,-4} via the invariant P.b = -PL*bL, at fixed eta=8.0.

If M(P.b, b^2) = g(P.b)*h(b^2), then for ANY two P.b values (Pb1,Pb2) and
ANY two b^2 values (b2_i,b2_j) at which all four points exist:

    R_cross(Pb1,Pb2; b2_i,b2_j) = [M(Pb1,b2_i)*M(Pb2,b2_j)]
                                 / [M(Pb1,b2_j)*M(Pb2,b2_i)]  ==  1

exactly, with no dependence on g or h and no functional-form assumption.
Every valid "rectangle" of 4 existing grid points is found automatically
and plotted as a discrete point with a jackknife error bar against the
R=1 reference line -- no chi^2/p-value is computed, per plan (visual only).

IMPORTANT symmetry found while building this: M(P.b,b^2) is EXACTLY even
under P.b -> -P.b for ReA2B/ReA12B and EXACTLY odd for ImA2B/ImA12B (an
identity of the underlying data, e.g. Re/Im parts of a Fourier-conjugate
pair). Either symmetry makes a mirror rectangle (Pb, -Pb, b2_i, b2_j)
collapse to R=1 by construction, regardless of whether f actually
factorizes, and makes every mixed/negative-sign rectangle an exact
duplicate of its all-positive counterpart. So only 0 < Pb1 < Pb2 carries
independent information -- that's what find_rectangles restricts to. The
P.b range is additionally capped at MAX_PB, since the raw cross-PL grid
extends to |P.b|=24 where only one or two lattice measurements contribute
and errors blow up to 10-100x the signal.
"""

import h5py
import numpy as np
import matplotlib.pyplot as plt
from itertools import combinations

PATH_BASE = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/TMD_fit/h5data"
PL_LIST = [-1, -2, -3, -4]
TARGET_ETA = 8.0
AMPLITUDES = ["ReA2B", "ImA2B", "ReA12B", "ImA12B"]
MAX_PB = 8.0  # cap on P.b: beyond this the cross-PL grid gets sparse/noisy (see module docstring)

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


def load_and_aggregate_data(path_base, amp_name, target_eta=8.0, pl_list=PL_LIST):
    """
    Loads jackknife samples for `amp_name` across all PL in pl_list, filters
    to target_eta, and returns {(P.b, b^2): jackknife_sample_array}.
    """
    aggregated_data = {}

    for PL in pl_list:
        filepath = f"{path_base}/{amp_name}_PL{PL}_jackknife_data.h5"
        try:
            with h5py.File(filepath, "r") as f:
                raw_data = f["Dataset1"][:]
        except FileNotFoundError:
            print(f"File not found: {filepath}")
            continue

        kin = raw_data[:, 0:3]
        samples = raw_data[:, 3:]
        eta, bL, bT = kin[:, 0], kin[:, 1], kin[:, 2]

        mask = np.isclose(eta, target_eta)
        bL_f, bT_f, samples_f = bL[mask], bT[mask], samples[mask]

        for i in range(len(bL_f)):
            P_dot_b = np.round(-1.0 * float(PL) * bL_f[i], 5)
            b_sq = np.round(bL_f[i] ** 2 + bT_f[i] ** 2, 5)
            key = (P_dot_b, b_sq)
            if key not in aggregated_data:
                aggregated_data[key] = samples_f[i]

    return aggregated_data


def find_rectangles(aggregated_data, max_pb=MAX_PB):
    """
    Finds every (Pb1, Pb2, b2_i, b2_j) "rectangle" of 4 existing grid points:
    for each unordered pair of P.b values, take every unordered pair of b^2
    values common to both. Returns a list of (Pb1, Pb2, b2_i, b2_j) with
    b2_i < b2_j (canonical ordering, no duplicates).

    Restricted to 0 < Pb1 < Pb2 <= max_pb: because M(P.b,b^2) is exactly
    even (Re channels) or exactly odd (Im channels) under P.b -> -P.b in
    this data, any rectangle involving Pb=-Pb' or mixed signs is either a
    trivial R=1 (mirror pair) or an exact duplicate of the all-positive
    rectangle -- see module docstring. max_pb=None disables the cap.
    """
    b2_by_pb = {}
    for (pb, b2) in aggregated_data.keys():
        b2_by_pb.setdefault(pb, set()).add(b2)

    all_pb = sorted(pb for pb in b2_by_pb if pb > 0 and (max_pb is None or pb <= max_pb))
    rectangles = []
    for pb1, pb2 in combinations(all_pb, 2):
        shared_b2 = b2_by_pb[pb1] & b2_by_pb[pb2]
        if len(shared_b2) < 2:
            continue
        for b2_i, b2_j in combinations(sorted(shared_b2), 2):
            rectangles.append((pb1, pb2, b2_i, b2_j))
    return rectangles


def compute_cross_ratio(aggregated_data, pb1, pb2, b2_i, b2_j):
    """R_cross = [M(pb1,b2_i)*M(pb2,b2_j)] / [M(pb1,b2_j)*M(pb2,b2_i)], jackknifed."""
    s_1i = aggregated_data[(pb1, b2_i)]
    s_1j = aggregated_data[(pb1, b2_j)]
    s_2i = aggregated_data[(pb2, b2_i)]
    s_2j = aggregated_data[(pb2, b2_j)]

    r_samples = (s_1i * s_2j) / (s_1j * s_2i)
    mean, err = jackknife_vectorized(r_samples.reshape(1, -1))
    return mean[0], err[0]


def plot_cross_ratios(results_per_amp):
    """
    results_per_amp: {amp_name: [(label, mean, err), ...]}
    2x2 grid, one panel per amplitude, R vs rectangle index with a
    dashed reference line at R=1.
    """
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))
    fig.suptitle(
        fr'Cross-Ratio Factorization Test: $R = \dfrac{{M(P_1{{\cdot}}b,b_i^2)\,M(P_2{{\cdot}}b,b_j^2)}}'
        fr'{{M(P_1{{\cdot}}b,b_j^2)\,M(P_2{{\cdot}}b,b_i^2)}}$ ($\eta|v|/a = {TARGET_ETA:g}$)',
        fontsize=15, fontweight='bold'
    )
    axes_flat = axes.flatten()

    for idx, amp_name in enumerate(AMPLITUDES):
        ax = axes_flat[idx]
        entries = results_per_amp.get(amp_name, [])

        if not entries:
            ax.text(0.5, 0.5, "No valid rectangles", ha='center', va='center')
            ax.set_title(AMP_LABELS[amp_name], fontsize=14)
            continue

        labels = [e[0] for e in entries]
        means = np.array([e[1] for e in entries])
        errs = np.array([e[2] for e in entries])
        x = np.arange(len(entries))

        ax.axhline(1.0, color='black', linestyle='--', linewidth=1.5, label='$R=1$ (factorized)', zorder=1)
        ax.errorbar(x, means, yerr=errs, fmt='o', color='#3cb44b', capsize=4, zorder=5)

        # Clip the view around R=1 so a few very noisy points (large errors on
        # low-signal channels) don't wash out the rest of the panel; error bars
        # simply run off the visible range for those points rather than being
        # dropped from the data.
        ax.set_ylim(-2.0, 4.0)

        ax.set_xticks(x)
        ax.set_xticklabels(labels, rotation=90, ha='center', fontsize=7)
        ax.set_title(f'Cross-Ratio of {AMP_LABELS[amp_name]}', fontsize=14)
        ax.set_ylabel('$R_{cross}$', fontsize=12)
        ax.grid(True, linestyle='--', alpha=0.5)
        ax.legend(fontsize='small', loc='best')

    plt.tight_layout(rect=[0, 0, 1, 0.95])
    return fig


def main():
    print("Loading jackknife samples and building (P.b, b^2) grids...")
    results_per_amp = {}

    for amp_name in AMPLITUDES:
        aggregated_data = load_and_aggregate_data(PATH_BASE, amp_name, target_eta=TARGET_ETA)
        rectangles = find_rectangles(aggregated_data)
        print(f"\n{amp_name}: {len(aggregated_data)} grid points, {len(rectangles)} valid rectangles")

        entries = []
        for (pb1, pb2, b2_i, b2_j) in rectangles:
            mean, err = compute_cross_ratio(aggregated_data, pb1, pb2, b2_i, b2_j)
            label = f"P.b=({pb1:g},{pb2:g}) b²=({b2_i:g},{b2_j:g})"
            entries.append((label, mean, err))
            print(f"  P.b=({pb1:g},{pb2:g}), b^2=({b2_i:g},{b2_j:g}) -> R = {mean:.4f} +/- {err:.4f}")

        results_per_amp[amp_name] = entries

    print("\nPlotting...")
    fig = plot_cross_ratios(results_per_amp)

    save_name = "Factorization_CrossRatioTest.pdf"
    plt.savefig(save_name, format='pdf', dpi=300, bbox_inches='tight')
    print(f"Saved: {save_name}")


if __name__ == "__main__":
    main()
