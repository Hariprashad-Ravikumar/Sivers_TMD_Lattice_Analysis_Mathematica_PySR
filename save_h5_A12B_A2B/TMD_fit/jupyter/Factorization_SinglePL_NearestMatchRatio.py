#!/usr/bin/env python
# coding: utf-8
"""
Approximate single-ratio factorization test at a SINGLE PL and SINGLE eta,
using NEAREST-AVAILABLE-VALUE matching instead of requiring an exact shared
grid point (which Factorization_SinglePL_LocalSlope.py's analysis showed
essentially never exists at fixed PL=-1, eta=8.0: the (P.b,b^2) sampling
graph is a forest, so no two P.b values share 2+ b^2, and no two b^2 values
share 2+ P.b).

If f(P.b,b^2) = J(P.b)*K(b^2):

  Direction A (fix a P.b pair, scan b^2):
      R_A(Pb1,Pb2; b^2) = f(Pb1,b^2)/f(Pb2,b^2) = J(Pb1)/J(Pb2)
      -- should be independent of b^2.

  Direction B (fix a b^2 pair, scan P.b):
      R_B(b2_1,b2_2; P.b) = f(P.b,b2_1)/f(P.b,b2_2) = K(b2_1)/K(b2_2)
      -- should be independent of P.b.

Both need an exact match that mostly doesn't exist here, so for each target
value we substitute the CLOSEST available grid point and plot the actual
mismatch alongside the ratio, so the approximation is visible rather than
hidden. No chi^2/p-value -- visual only, consistent with prior scripts.
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

# Direction A: which (Pb1, Pb2) pairs to scan across b^2
PB_PAIRS = [(2.0, 4.0), (1.0, 3.0)]

# Direction B: which (b2_1, b2_2) pairs to scan across P.b
B2_PAIRS = [(20.0, 45.0)]


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
    {(P.b, b^2): averaged_jackknife_sample_array}, P.b > 0 only (canonical
    half; see Factorization_SinglePL_LocalSlope.py for the even/odd
    symmetry justifying this), averaging bT-sign replica measurements at
    the same (P.b, b^2).
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


def nearest_b2(aggregated_data, pb, target_b2):
    """Closest available b^2 at a given P.b to target_b2. Returns (b2, samples)."""
    available = [b2 for (p, b2) in aggregated_data if p == pb]
    best = min(available, key=lambda b2: abs(b2 - target_b2))
    return best, aggregated_data[(pb, best)]


def ratio_stats(samples_num, samples_den):
    r_samples = samples_num / samples_den
    mean, err = jackknife_vectorized(r_samples.reshape(1, -1))
    return mean[0], err[0]


def direction_a(all_data):
    """
    For each amplitude and each (Pb1,Pb2) pair, scan target b^2 = union of
    both P.b's own available b^2 values, using nearest-match at each P.b.
    Returns {amp: {(pb1,pb2): [(target_b2, matched_b2_1, matched_b2_2, R, err), ...]}}
    """
    results = {}
    for amp_name in AMPLITUDES:
        data = all_data[amp_name]
        results[amp_name] = {}
        for pb1, pb2 in PB_PAIRS:
            b2_1_avail = sorted(b2 for (p, b2) in data if p == pb1)
            b2_2_avail = sorted(b2 for (p, b2) in data if p == pb2)
            targets = sorted(set(b2_1_avail) | set(b2_2_avail))

            entries = []
            for target in targets:
                m1, s1 = nearest_b2(data, pb1, target)
                m2, s2 = nearest_b2(data, pb2, target)
                mean, err = ratio_stats(s1, s2)
                entries.append((target, m1, m2, mean, err))
            results[amp_name][(pb1, pb2)] = entries
    return results


def direction_b(all_data):
    """
    For each amplitude and each (b2_1,b2_2) pair, scan all available P.b,
    using nearest-match b^2 at each P.b to each target.
    Returns {amp: {(b2_1,b2_2): [(pb, matched_b2_1, matched_b2_2, R, err), ...]}}

    A P.b is SKIPPED if both targets snap to the same nearest available
    point (m1 == m2): that would divide a value by itself, giving a
    trivial R=1 with zero error that looks like perfect factorization but
    is actually a degenerate non-comparison (happens when a P.b only has
    points far from both targets, e.g. P.b=1 with b^2 in {2,5} matching
    both target=20 and target=45 to the same b^2=5).
    """
    results = {}
    for amp_name in AMPLITUDES:
        data = all_data[amp_name]
        results[amp_name] = {}
        all_pb = sorted(set(p for (p, b2) in data))
        for b2_1, b2_2 in B2_PAIRS:
            entries = []
            skipped = []
            for pb in all_pb:
                m1, s1 = nearest_b2(data, pb, b2_1)
                m2, s2 = nearest_b2(data, pb, b2_2)
                if m1 == m2:
                    skipped.append((pb, m1))
                    continue
                mean, err = ratio_stats(s1, s2)
                entries.append((pb, m1, m2, mean, err))
            results[amp_name][(b2_1, b2_2)] = entries
            if skipped:
                print(f"  [skipped degenerate] {amp_name}, b²=({b2_1:g},{b2_2:g}): "
                      f"P.b={[p for p, _ in skipped]} all matched both targets to the "
                      f"same point (e.g. b²={skipped[0][1]:g}) -- no real comparison possible there")
    return results


def plot_direction_a(results_a):
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))
    fig.suptitle(
        fr'Direction A: $R(P_1{{\cdot}}b,P_2{{\cdot}}b;b^2) = f(P_1{{\cdot}}b,b^2)/f(P_2{{\cdot}}b,b^2)$ '
        fr'vs target $b^2$ (nearest-match, $P_L={PL}$, $\eta|v|/a={TARGET_ETA:g}$)',
        fontsize=13, fontweight='bold'
    )
    axes_flat = axes.flatten()
    colors = ['#e6194b', '#3cb44b', '#4363d8']

    for idx, amp_name in enumerate(AMPLITUDES):
        ax = axes_flat[idx]
        for series_idx, (c, (pb1, pb2)) in enumerate(zip(colors, PB_PAIRS)):
            entries = results_a[amp_name][(pb1, pb2)]
            targets = [e[0] for e in entries]
            means = [e[3] for e in entries]
            errs = [e[4] for e in entries]

            label = fr'$R = f(P{{\cdot}}b{{=}}{pb1:g},\,b^2)\,/\,f(P{{\cdot}}b{{=}}{pb2:g},\,b^2)$'
            ax.errorbar(targets, means, yerr=errs, fmt='o-', color=c, capsize=4, label=label)

            # Explicit formula, with the actual matched (P.b,b^2) values used, at every point.
            # Series 0 labels go above their point, series 1 below, and within a series
            # consecutive points alternate a further step out -- keeps the two curves'
            # labels from colliding where the lines cross.
            base_dir = 1 if series_idx == 0 else -1
            for pt_idx, (t, m1, m2, mean) in enumerate(zip(targets, [e[1] for e in entries],
                                                             [e[2] for e in entries], means)):
                text = f'$f({pb1:g},{m1:g})/f({pb2:g},{m2:g})$'
                y_offset = base_dir * (12 + 14 * (pt_idx % 2))
                va = 'bottom' if base_dir > 0 else 'top'
                ax.annotate(text, (t, mean), fontsize=7, color=c,
                           textcoords="offset points", xytext=(0, y_offset), ha='center', va=va)

        ax.set_title(AMP_LABELS[amp_name], fontsize=14)
        ax.set_xlabel('target $b^2$', fontsize=11)
        ax.set_ylabel('$R_A$', fontsize=12)
        ax.grid(True, linestyle='--', alpha=0.5)
        ax.legend(fontsize='small', loc='best')

    plt.tight_layout(rect=[0, 0, 1, 0.93])
    return fig


def plot_direction_b(results_b):
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))
    fig.suptitle(
        fr'Direction B: $R(b_1^2,b_2^2;P{{\cdot}}b) = f(P{{\cdot}}b,b_1^2)/f(P{{\cdot}}b,b_2^2)$ '
        fr'vs $P{{\cdot}}b$ (nearest-match, $P_L={PL}$, $\eta|v|/a={TARGET_ETA:g}$)',
        fontsize=13, fontweight='bold'
    )
    axes_flat = axes.flatten()
    colors = ['#911eb4', '#f58231']

    for idx, amp_name in enumerate(AMPLITUDES):
        ax = axes_flat[idx]
        for series_idx, (c, (b2_1, b2_2)) in enumerate(zip(colors, B2_PAIRS)):
            entries = results_b[amp_name][(b2_1, b2_2)]
            pbs = [e[0] for e in entries]
            means = [e[3] for e in entries]
            errs = [e[4] for e in entries]

            label = fr'$R = f(P{{\cdot}}b,\,b^2{{=}}{b2_1:g})\,/\,f(P{{\cdot}}b,\,b^2{{=}}{b2_2:g})$'
            ax.errorbar(pbs, means, yerr=errs, fmt='o-', color=c, capsize=4, label=label)

            # Explicit formula, with the actual matched (P.b,b^2) values used, at every point
            for pt_idx, (p, m1, m2, mean) in enumerate(zip(pbs, [e[1] for e in entries],
                                                             [e[2] for e in entries], means)):
                text = f'$f({p:g},{m1:g})/f({p:g},{m2:g})$'
                y_offset = 10 + 14 * ((series_idx + pt_idx) % 3)
                ax.annotate(text, (p, mean), fontsize=7, color=c,
                           textcoords="offset points", xytext=(0, y_offset), ha='center')

        ax.set_title(AMP_LABELS[amp_name], fontsize=14)
        ax.set_xlabel('$P \\cdot b$', fontsize=11)
        ax.set_ylabel('$R_B$', fontsize=12)
        ax.grid(True, linestyle='--', alpha=0.5)
        ax.legend(fontsize='small', loc='best')

    plt.tight_layout(rect=[0, 0, 1, 0.93])
    return fig


def main():
    print(f"Loading jackknife samples at PL={PL}, eta={TARGET_ETA}...")
    all_data = {amp: load_single_pl(PATH_BASE, amp) for amp in AMPLITUDES}

    print("\n=== Direction A: fix P.b pair, scan b^2 (nearest-match) ===")
    results_a = direction_a(all_data)
    for amp_name in AMPLITUDES:
        for (pb1, pb2), entries in results_a[amp_name].items():
            print(f"\n{amp_name}, P.b=({pb1:g},{pb2:g}):")
            for target, m1, m2, mean, err in entries:
                print(f"  target b²={target:g}  ->  matched ({m1:g},{m2:g})  "
                      f"R = {mean:.4f} +/- {err:.4f}")

    print("\n=== Direction B: fix b^2 pair, scan P.b (nearest-match) ===")
    results_b = direction_b(all_data)
    for amp_name in AMPLITUDES:
        for (b2_1, b2_2), entries in results_b[amp_name].items():
            print(f"\n{amp_name}, b²=({b2_1:g},{b2_2:g}):")
            for pb, m1, m2, mean, err in entries:
                print(f"  P.b={pb:g}  ->  matched ({m1:g},{m2:g})  "
                      f"R = {mean:.4f} +/- {err:.4f}")

    print("\nPlotting...")
    fig_a = plot_direction_a(results_a)
    fig_a.savefig(f"Factorization_SinglePL_NearestMatch_DirA_PL{PL}.pdf", format='pdf', dpi=300, bbox_inches='tight')
    print(f"Saved: Factorization_SinglePL_NearestMatch_DirA_PL{PL}.pdf")

    fig_b = plot_direction_b(results_b)
    fig_b.savefig(f"Factorization_SinglePL_NearestMatch_DirB_PL{PL}.pdf", format='pdf', dpi=300, bbox_inches='tight')
    print(f"Saved: Factorization_SinglePL_NearestMatch_DirB_PL{PL}.pdf")


if __name__ == "__main__":
    main()
