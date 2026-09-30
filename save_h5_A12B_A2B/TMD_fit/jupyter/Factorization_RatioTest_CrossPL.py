#!/usr/bin/env python
# coding: utf-8

import h5py
import numpy as np
import matplotlib.pyplot as plt

# --- 1. Vectorized Jackknife Function ---
def jackknife_vectorized(samples):
    N = samples.shape[1]
    theta_bar = np.mean(samples, axis=1)
    squared_diffs = np.square(samples - theta_bar[:, None])
    sigma_sq = ((N - 1) / N) * np.sum(squared_diffs, axis=1)
    error = np.sqrt(sigma_sq)
    return theta_bar, error

# --- 2. Data Loading Helper ---
def load_and_aggregate_data(path_base, amp_name, target_eta=8.0):
    """
    Loads data for a specific amplitude across all PL values,
    filters by target_eta, and returns a dictionary structured by (P_dot_b, b_sq) -> samples
    """
    aggregated_data = {}
    
    for PL in [-1, -2, -3, -4]:
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
        bL_f = bL[mask]
        bT_f = bT[mask]
        samples_f = samples[mask]
        
        for i in range(len(bL_f)):
            # IMPORTANT: Lorentz invariant mapping P.b = - PL * bL
            P_dot_b = np.round(-1.0 * float(PL) * bL_f[i], 5)
            # b^2 = bL^2 + bT^2
            b_sq = np.round(bL_f[i]**2 + bT_f[i]**2, 5)
            
            # Key is (P.b, b^2)
            key = (P_dot_b, b_sq)
            # Just in case multiple points fall into the same bin, though unlikely in lattice data
            # we will just overwrite or take the first one
            if key not in aggregated_data:
                aggregated_data[key] = samples_f[i]
                
    return aggregated_data

# --- 3. Ratio Computation and Plotting ---
def plot_cross_pl_ratios(all_data_dict, b2_sets, target_eta=8.0):
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))
    fig.suptitle(fr'Cross-$P_L$ Factorization Ratio Test at fixed $b^2$ (Fixed $\eta|v|/a = {target_eta}$)', fontsize=18, fontweight='bold')

    axes_flat = axes.flatten()
    
    # We will iterate over the provided b2_sets to plot
    # Example b2_sets: [(17.0, 20.0, 32.0), (5.0, 8.0, 20.0)]
    
    for idx, (amp_name, aggregated_data) in enumerate(all_data_dict.items()):
        ax = axes_flat[idx]
        
        if amp_name == "ReA2B":
            amp_print = "$\\tilde{{A}}_{{2B}}^{{Re}}$"
        elif amp_name == "ImA2B":
            amp_print = "$\\tilde{{A}}_{{2B}}^{{Im}}$"
        elif amp_name == "ReA12B":
            amp_print = "$\\tilde{{A}}_{{12B}}^{{Re}}$"
        elif amp_name == "ImA12B":
            amp_print = "$\\tilde{{A}}_{{12B}}^{{Im}}$"

        if not aggregated_data: 
            ax.text(0.5, 0.5, "No data", ha='center', va='center')
            continue
            
        # Get all unique P.b values present in the data
        all_Pb = sorted(list(set(k[0] for k in aggregated_data.keys())))
        
        # We will plot multiple sets on the same axis using different colors/markers
        colors = ['blue', 'red', 'green', 'purple']
        markers = ['o', 's', '^', 'D']
        
        for set_idx, b2_tuple in enumerate(b2_sets):
            b2_1, b2_2, b2_3 = b2_tuple
            
            ratio_13_means = []
            ratio_13_errs = []
            ratio_23_means = []
            ratio_23_errs = []
            valid_Pb_13 = []
            valid_Pb_23 = []
            
            for Pb in all_Pb:
                s1 = aggregated_data.get((Pb, b2_1))
                s2 = aggregated_data.get((Pb, b2_2))
                s3 = aggregated_data.get((Pb, b2_3))
                
                if s3 is not None:
                    if s1 is not None:
                        ratio_samples = s1 / s3
                        mean, err = jackknife_vectorized(ratio_samples.reshape(1, -1))
                        ratio_13_means.append(mean[0])
                        ratio_13_errs.append(err[0])
                        valid_Pb_13.append(Pb)
                    
                    if s2 is not None:
                        ratio_samples = s2 / s3
                        mean, err = jackknife_vectorized(ratio_samples.reshape(1, -1))
                        ratio_23_means.append(mean[0])
                        ratio_23_errs.append(err[0])
                        valid_Pb_23.append(Pb)
                        
            # Plotting this set
            c = colors[set_idx % len(colors)]
            m1 = markers[(set_idx*2) % len(markers)]
            m2 = markers[(set_idx*2 + 1) % len(markers)]
            
            if len(valid_Pb_13) > 0:
                ax.errorbar(valid_Pb_13, ratio_13_means, yerr=ratio_13_errs, fmt=f'{m1}-', color=c, 
                            label=fr'$A(b^2={b2_1:g}) / A(b^2={b2_3:g})$', capsize=3, zorder=5)
            if len(valid_Pb_23) > 0:
                ax.errorbar(valid_Pb_23, ratio_23_means, yerr=ratio_23_errs, fmt=f'{m2}--', color=c, 
                            label=fr'$A(b^2={b2_2:g}) / A(b^2={b2_3:g})$', capsize=3, zorder=4)

        ax.set_title(fr'Ratio of {amp_print}', fontsize=14)
        ax.set_xlabel(r'$(P \cdot b)$', fontsize=12)
        ax.set_ylabel('Amplitude Ratio', fontsize=12)
        ax.grid(True, linestyle='--', alpha=0.5)
        ax.legend(fontsize='small', loc='best', ncol=2)

    plt.tight_layout(rect=[0, 0, 1, 0.96])
    return fig

# ==========================================
# Main Execution Block
# ==========================================
if __name__ == "__main__":
    path_base = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/TMD_fit/h5data"
    
    amplitudes = ["ReA2B", "ImA2B", "ReA12B", "ImA12B"]
    all_data_dict = {}

    print("Loading Jackknife samples across all PL...")
    for amp in amplitudes:
        all_data_dict[amp] = load_and_aggregate_data(path_base, amp, target_eta=8.0)
        
    # Define sets of 3 overlapping b^2 values that were found in the scan
    # Set 1: b^2 in {17.0, 20.0, 32.0} -> available at P.b in {-16, -12, -8, -4, 4, 8, 12, 16}
    # Set 2: b^2 in {5.0, 8.0, 20.0} -> available at P.b in {-8, -6, -4, -2, 2, 4, 6, 8}
    b2_sets = [
        (17.0, 20.0, 32.0),
        (5.0, 8.0, 20.0)
    ]

    print("Computing and plotting ratios...")
    if all_data_dict:
        fig_ratios = plot_cross_pl_ratios(all_data_dict, b2_sets, target_eta=8.0)

        # --- SAVE PLOT HERE ---
        save_name = "Factorization_RatioTest_CrossPL.pdf"
        plt.savefig(save_name, format='pdf', dpi=300, bbox_inches='tight')
        print(f"Saved: {save_name}")
