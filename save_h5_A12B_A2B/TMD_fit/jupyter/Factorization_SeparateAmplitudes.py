#!/usr/bin/env python
# coding: utf-8
"""
Factorization test for EACH amplitude separately using nearest-match ratios.
Plots no connecting lines, and explicitly lists numerator and denominator in the legend.
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

PB_PAIRS = [(2.0, 4.0), (1.0, 3.0)]
B2_PAIRS = [(20.0, 45.0)]

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

    # DIRECTION A: Fix P.b pair, scan target b^2
    for amp_name in AMPLITUDES:
        data = all_data[amp_name]
        fig, axes = plt.subplots(1, len(PB_PAIRS), figsize=(16, 6))
        fig.suptitle(f"{amp_name}: Direction A Ratio Test (Fix P.b pair, scan b²)", fontsize=14, fontweight='bold')
        
        if len(PB_PAIRS) == 1:
            axes = [axes]
            
        for ax, (pb1, pb2) in zip(axes, PB_PAIRS):
            b2_1_avail = sorted(b2 for (p, b2) in data if p == pb1)
            b2_2_avail = sorted(b2 for (p, b2) in data if p == pb2)
            targets = sorted(set(b2_1_avail) | set(b2_2_avail))
            
            markers = itertools.cycle(['o', 's', '^', 'D', 'v', 'p', '*'])
            colors = itertools.cycle(plt.cm.tab10.colors)
            
            for target in targets:
                m1, s1 = nearest_b2(data, pb1, target)
                m2, s2 = nearest_b2(data, pb2, target)
                if m1 is None or m2 is None:
                    continue
                
                mean, err = jackknife_ratio(s1, s2)
                
                # Explicit legend for numerator and denominator
                label = f"Target b²={target}\nNum: f(P.b={pb1}, b²={m1})\nDen: f(P.b={pb2}, b²={m2})"
                
                # No connecting lines, just points (fmt using just the marker)
                ax.errorbar(target, mean, yerr=err, fmt=next(markers), color=next(colors), capsize=4, label=label, markersize=8)
                
            ax.set_title(f"Ratio of P.b={pb1} to P.b={pb2}", fontsize=12)
            ax.set_xlabel('Target $b^2$', fontsize=11)
            ax.set_ylabel('Ratio', fontsize=11)
            ax.grid(True, linestyle='--', alpha=0.5)
            # Move legend outside the plot
            ax.legend(bbox_to_anchor=(1.05, 1), loc='upper left', fontsize=9)
            
        plt.tight_layout()
        fig.savefig(f"SeparateAmp_{amp_name}_DirA_PL{PL}.pdf", format='pdf', dpi=300, bbox_inches='tight')
        print(f"Saved: SeparateAmp_{amp_name}_DirA_PL{PL}.pdf")

    # DIRECTION B: Fix b^2 pair, scan P.b
    for amp_name in AMPLITUDES:
        data = all_data[amp_name]
        fig, axes = plt.subplots(1, len(B2_PAIRS), figsize=(12, 6))
        fig.suptitle(f"{amp_name}: Direction B Ratio Test (Fix b² pair, scan P.b)", fontsize=14, fontweight='bold')
        
        if len(B2_PAIRS) == 1:
            axes = [axes]
            
        all_pb = sorted(set(p for (p, b2) in data))
        
        for ax, (b2_1, b2_2) in zip(axes, B2_PAIRS):
            markers = itertools.cycle(['o', 's', '^', 'D', 'v', 'p', '*'])
            colors = itertools.cycle(plt.cm.tab10.colors)
            
            for pb in all_pb:
                m1, s1 = nearest_b2(data, pb, b2_1)
                m2, s2 = nearest_b2(data, pb, b2_2)
                if m1 is None or m2 is None:
                    continue
                if m1 == m2:
                    continue # Skip degenerate
                    
                mean, err = jackknife_ratio(s1, s2)
                
                label = f"P.b={pb}\nNum: f(P.b={pb}, b²={m1})\nDen: f(P.b={pb}, b²={m2})"
                ax.errorbar(pb, mean, yerr=err, fmt=next(markers), color=next(colors), capsize=4, label=label, markersize=8)
                
            ax.set_title(f"Ratio of Target b²={b2_1} to b²={b2_2}", fontsize=12)
            ax.set_xlabel('$P \cdot b$', fontsize=11)
            ax.set_ylabel('Ratio', fontsize=11)
            ax.grid(True, linestyle='--', alpha=0.5)
            ax.legend(bbox_to_anchor=(1.05, 1), loc='upper left', fontsize=9)
            
        plt.tight_layout()
        fig.savefig(f"SeparateAmp_{amp_name}_DirB_PL{PL}.pdf", format='pdf', dpi=300, bbox_inches='tight')
        print(f"Saved: SeparateAmp_{amp_name}_DirB_PL{PL}.pdf")

if __name__ == "__main__":
    main()
