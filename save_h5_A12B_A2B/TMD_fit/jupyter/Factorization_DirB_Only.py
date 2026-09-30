#!/usr/bin/env python
# coding: utf-8
"""
Factorization test for EACH amplitude separately.

This script tests factorization by evaluating the ratio:
    R(P.b) = f(P.b, m1) / f(P.b, m2)
where m1 and m2 are the nearest available matches to target b^2 pairs.

Crucially, BOTH numerator and denominator are evaluated at the EXACT SAME P.b value.
Therefore, the P.b dependence (J(P.b)) mathematically cancels out.
If factorization holds, R(P.b) should be independent of P.b, appearing as a 
flat horizontal line (a "straight line in P.b") when plotted against P.b.

No connecting lines are drawn, and legends explicitly state the numerator and denominator.
"""

import h5py
import numpy as np
import matplotlib.pyplot as plt
from collections import defaultdict
import itertools

PATH_BASE = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/TMD_fit/h5data"
PL = -1
TARGET_ETA = 8.0
AMPLITUDES = ["ReA2B", "ImA2B", "ReA12B"]

# We test the original pair (20, 45) and add (5, 45) to ensure we get a plot with >= 3 points
B2_PAIRS = [(20.0, 45.0), (5.0, 45.0)]

def jackknife_ratio(samples_num, samples_den):
    ratio_samples = samples_num / samples_den
    N = len(ratio_samples)
    theta_bar = np.mean(ratio_samples)
    squared_diffs = np.square(ratio_samples - theta_bar)
    sigma_sq = ((N - 1) / N) * np.sum(squared_diffs)
    error = np.sqrt(sigma_sq)
    return theta_bar, error

def load_single_pl(path_base, amp_name, pl=PL, target_eta=TARGET_ETA):
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

def nearest_b2(data, pb, target_b2):
    available = [b2 for (p, b2) in data if p == pb]
    if not available:
        return None, None
    best = min(available, key=lambda b2: abs(b2 - target_b2))
    return best, data[(pb, best)]

def main():
    print(f"Loading data for PL={PL}, eta={TARGET_ETA}...")
    all_data = {amp: load_single_pl(PATH_BASE, amp) for amp in AMPLITUDES}

    for amp_name in AMPLITUDES:
        data = all_data[amp_name]
        fig, axes = plt.subplots(1, len(B2_PAIRS), figsize=(14, 6))
        fig.suptitle(f"{amp_name}: Ratio Test (Divide at SAME P.b value)", fontsize=14, fontweight='bold')
        
        if len(B2_PAIRS) == 1:
            axes = [axes]
            
        all_pb = sorted(set(p for (p, b2) in data))
        
        for ax, (b2_1, b2_2) in zip(axes, B2_PAIRS):
            markers = itertools.cycle(['o', 's', '^', 'D', 'v', 'p', '*'])
            colors = itertools.cycle(plt.cm.tab10.colors)
            
            plotted_points = 0
            for pb in all_pb:
                m1, s1 = nearest_b2(data, pb, b2_1)
                m2, s2 = nearest_b2(data, pb, b2_2)
                if m1 is None or m2 is None:
                    continue
                if m1 == m2:
                    continue # Skip degenerate point
                    
                mean, err = jackknife_ratio(s1, s2)
                
                # Explicit legend for numerator and denominator
                label = f"P.b={pb}\nNum: f(b²={m1})\nDen: f(b²={m2})"
                ax.errorbar(pb, mean, yerr=err, fmt=next(markers), color=next(colors), capsize=4, label=label, markersize=8)
                plotted_points += 1
                
            ax.set_title(f"Target b²=({b2_1}, {b2_2})", fontsize=12)
            ax.set_xlabel('$P \cdot b$', fontsize=12)
            ax.set_ylabel('Ratio', fontsize=12)
            ax.grid(True, linestyle='--', alpha=0.5)
            if plotted_points > 0:
                ax.legend(bbox_to_anchor=(1.05, 1), loc='upper left', fontsize=10)
            
        plt.tight_layout()
        plot_name = f"Factorization_DirB_{amp_name}_PL{PL}.pdf"
        fig.savefig(plot_name, format='pdf', dpi=300, bbox_inches='tight')
        print(f"Saved: {plot_name}")

if __name__ == "__main__":
    main()
