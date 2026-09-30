#!/usr/bin/env python
# coding: utf-8
"""
Factorization test using Amplitude Ratios.

This script tests factorization by forming ratios of different amplitudes 
at the EXACT SAME (P.b, b^2) kinematic points. 

If factorization holds, A(P.b, b^2) = J(P.b) * K(b^2). 
Assuming the K(b^2) dependence is universal for these amplitudes, the ratio:
    Numerator(P.b, b^2) / Denominator(P.b, b^2)
    = [ J_num(P.b) * K(b^2) ] / [ J_den(P.b) * K(b^2) ]
    = J_num(P.b) / J_den(P.b)

This resulting ratio must be completely independent of b^2. We plot this ratio
as a function of b^2 for fixed P.b values. If the points form a flat horizontal
line, it is a robust, fit-free confirmation of factorization.
"""

import h5py
import numpy as np
import matplotlib.pyplot as plt
from collections import defaultdict

PATH_BASE = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/TMD_fit/h5data"
PL = -1
TARGET_ETA = 8.0

def jackknife_ratio(samples_num, samples_den):
    """
    Computes the Jackknife mean and error for the ratio of two datasets.
    samples_num, samples_den: shape (N_JK,)
    """
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
    
    # Filter by target eta and positive canonical bL half
    mask = np.isclose(eta, target_eta) & (bL > 0)
    bL_f, bT_f, samples_f = bL[mask], bT[mask], samples[mask]

    replicas = defaultdict(list)
    for i in range(len(bL_f)):
        P_dot_b = np.round(-1.0 * float(pl) * bL_f[i], 5)
        b_sq = np.round(bL_f[i] ** 2 + bT_f[i] ** 2, 5)
        replicas[(P_dot_b, b_sq)].append(samples_f[i])
        
    # Average over replicas if there are multiple at the exact same (P.b, b^2)
    return {key: np.mean(arrs, axis=0) for key, arrs in replicas.items()}

def main():
    print(f"Loading jackknife samples at PL={PL}, eta={TARGET_ETA}...")
    
    # We load the 3 amplitudes requested
    data = {
        "ReA2B": load_single_pl(PATH_BASE, "ReA2B"),
        "ImA2B": load_single_pl(PATH_BASE, "ImA2B"),
        "ReA12B": load_single_pl(PATH_BASE, "ReA12B")
    }

    # We will test at P.b = 2.0 and P.b = 4.0 because they have 3 data points each
    target_pbs = [2.0, 4.0]
    
    # Define the 3 ratio combinations to plot
    ratio_pairs = [
        ("ReA12B", "ReA2B"),
        ("ImA2B", "ReA2B"),
        ("ReA12B", "ImA2B")
    ]
    
    results = {pair: {} for pair in ratio_pairs}
    
    for pb in target_pbs:
        for (num_name, den_name) in ratio_pairs:
            data_num = data[num_name]
            data_den = data[den_name]
            
            # Find shared b^2 points between the numerator and denominator for this P.b
            b2_shared = sorted([k[1] for k in data_den if k[0] == pb and k in data_num])
            
            res = []
            for b2 in b2_shared:
                mean, err = jackknife_ratio(data_num[(pb, b2)], data_den[(pb, b2)])
                res.append((b2, mean, err))
                
            results[(num_name, den_name)][pb] = res

    # Plotting
    fig, axes = plt.subplots(1, 3, figsize=(20, 6))
    fig.suptitle(fr"Raw Data Amplitude Ratio Test for Factorization ($P_L={PL}, \eta|v|/a={TARGET_ETA:g}$)", fontsize=16, fontweight='bold')
    
    colors = {2.0: '#e6194b', 4.0: '#3cb44b'}
    
    for idx, (num_name, den_name) in enumerate(ratio_pairs):
        ax = axes[idx]
        for pb in target_pbs:
            plot_data = results[(num_name, den_name)][pb]
            if not plot_data:
                continue
                
            b2_vals = [d[0] for d in plot_data]
            means = [d[1] for d in plot_data]
            errs = [d[2] for d in plot_data]
            
            # Explicitly state numerator and denominator in legend
            label = fr'$P \cdot b = {pb}$ (Num: {num_name}, Den: {den_name})'
            ax.errorbar(b2_vals, means, yerr=errs, fmt='o-', color=colors[pb], capsize=4, label=label)
            
        ax.set_title(f"Ratio: {num_name} / {den_name}", fontsize=14)
        ax.set_xlabel('$b^2$', fontsize=12)
        ax.set_ylabel('Ratio', fontsize=12)
        ax.grid(True, linestyle='--', alpha=0.5)
        ax.legend(fontsize=10)

    plt.tight_layout()
    plot_filename = f"Factorization_AmplitudeRatioTest_PL{PL}.pdf"
    fig.savefig(plot_filename, format='pdf', dpi=300, bbox_inches='tight')
    print(f"\nSaved plot to {plot_filename}")
    
    # Print results to console
    for (num_name, den_name) in ratio_pairs:
        print(f"\n=== Ratio: {num_name} / {den_name} ===")
        for pb in target_pbs:
            print(f"P.b = {pb}:")
            for b2, mean, err in results[(num_name, den_name)][pb]:
                print(f"  b^2 = {b2:g}  -> Ratio = {mean:.4f} +/- {err:.4f}")

if __name__ == "__main__":
    main()
