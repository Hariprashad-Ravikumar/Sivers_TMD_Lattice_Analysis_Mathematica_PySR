#!/usr/bin/env python
# coding: utf-8

# In[20]:


import h5py
import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D

# --- 1. Vectorized Jackknife Function ---
def jackknife_vectorized(samples):
    N = samples.shape[1]
    theta_bar = np.mean(samples, axis=1)
    squared_diffs = np.square(samples - theta_bar[:, None])
    sigma_sq = ((N - 1) / N) * np.sum(squared_diffs, axis=1)
    error = np.sqrt(sigma_sq)
    return theta_bar, error

pl_to_zeta = {
        -4: 0.785756,
        -3: 0.539684,
        -2: 0.294367,
        -1: 0.090772
    }
# --- 2. Data Loading Helper ---
def get_processed_amplitude_data(filepath):
    try:
        with h5py.File(filepath, "r") as f:
            raw_data = f["Dataset1"][:]
    except FileNotFoundError:
        print(f"File not found: {filepath}")
        return None

    kin = raw_data[:, 0:3]
    samples = raw_data[:, 3:]

    eta, bL, bT = kin[:, 0], kin[:, 1], kin[:, 2]

    # Filter for base eta value from 1 to 10
    mask_eta = (eta >= 0) & (eta <= 10)
    eta_f, bL_f, bT_f = eta[mask_eta], bL[mask_eta], bT[mask_eta]

    mean_f, err_f = jackknife_vectorized(samples[mask_eta])

    return {
        'eta': eta_f, 'bL': bL_f, 'bT': bT_f,
        'mean': mean_f, 'error': err_f,
        'unique_bL': np.unique(bL_f), 'unique_bT': np.unique(bT_f)
    }

# --- 3. STRICTLY Distinct Color Generator ---
def get_distinct_colors(num_colors):
    """Returns a list of highly distinct, non-gradient colors."""
    distinct_hex = [
        '#e6194b', '#3cb44b', '#ffe119', '#4363d8', '#f58231',
        '#911eb4', '#46f0f0', '#f032e6', '#bcf60c', '#fabebe',
        '#008080', '#e6beff', '#9a6324', '#fffac8', '#800000',
        '#aaffc3', '#808000', '#ffd8b1', '#000075', '#808080',
        '#000000', '#333333'
    ]
    return [distinct_hex[i % len(distinct_hex)] for i in range(num_colors)]



# --- 4. 3D Plotting Function ---
def plot_3d_for_amplitude(data, amp_name, PL):
    fig = plt.figure(figsize=(16, 9))

    # Using 'fr' for formatted raw string
    if amp_name == "ReA2B":
        amp_print = "$\\tilde{{A}}_{{2B}}^{{Re}}$"
    elif amp_name == "ImA2B":
        amp_print = "$\\tilde{{A}}_{{2B}}^{{Im}}$"
    elif amp_name == "ReA12B":
        amp_print = "$\\tilde{{A}}_{{12B}}^{{Re}}$"
    elif amp_name == "ImA12B":  # <--- ADD THIS
        amp_print = "$\\tilde{{A}}_{{12B}}^{{Im}}$"

    # --- Plot 1: Color by distinct bT ---
    ax1 = fig.add_subplot(121, projection='3d')
    unique_bT = data['unique_bT']
    colors_bT = get_distinct_colors(len(unique_bT))

    for i, val_bT in enumerate(unique_bT):
        mask = (data['bT'] == val_bT)

        # 1. Plot the mean scatter points
        ax1.scatter(data['eta'][mask], data['bL'][mask], data['mean'][mask], 
                    color=colors_bT[i], label=fr'$b_T/a={val_bT:.0f}$', 
                    s=40, alpha=0.9, edgecolors='k', linewidth=0.3)

        # 2. Add the Z-axis error bars for Jackknife error
        ax1.errorbar(data['eta'][mask], data['bL'][mask], data['mean'][mask], 
                     zerr=data['error'][mask], fmt='none', ecolor=colors_bT[i], 
                     alpha=0.4, linewidth=1.0, zorder=0)

    # Added labelpad=10 to push labels away from tick numbers
    ax1.set_xlabel(r'$\eta|v|/a$', fontsize=12, labelpad=10)
    ax1.set_ylabel(r'$b_L/a$', fontsize=12, labelpad=10)
    ax1.set_zlabel(f'{amp_print}', fontsize=12, labelpad=10)
    ax1.set_title(fr'{amp_print} ($\eta|v|/a$, $b_L/a$, $b_T/a$, $\hat{{\zeta}}={pl_to_zeta[int(PL)]}$)')

    # Adjusted legend to be centered vertically on the right to save space
    ax1.legend(loc='center left', bbox_to_anchor=(1.1, 0.5), ncol=1)

    # --- Plot 2: Color by distinct bL ---
    ax2 = fig.add_subplot(122, projection='3d')
    unique_bL = data['unique_bL']
    colors_bL = get_distinct_colors(len(unique_bL))[::-1] 

    for i, val_bL in enumerate(unique_bL):
        mask = (data['bL'] == val_bL)

        # 1. Plot the mean scatter points
        ax2.scatter(data['eta'][mask], data['bT'][mask], data['mean'][mask], 
                    color=colors_bL[i], label=fr'$b_L/a={val_bL:.0f}$', 
                    s=40, alpha=0.9, edgecolors='k', linewidth=0.3)

        # 2. Add the Z-axis error bars for Jackknife error
        ax2.errorbar(data['eta'][mask], data['bT'][mask], data['mean'][mask], 
                     zerr=data['error'][mask], fmt='none', ecolor=colors_bL[i], 
                     alpha=0.4, linewidth=1.0, zorder=0)

    # Added labelpad=10
    ax2.set_xlabel(r'$\eta|v|/a$', fontsize=12, labelpad=10)
    ax2.set_ylabel(r'$b_T/a$', fontsize=12, labelpad=10)
    ax2.set_zlabel(f'{amp_print}', fontsize=12, labelpad=10)
    ax2.set_title(fr'{amp_print} ($\eta|v|/a$, $b_L/a$, $b_T/a$, $\hat{{\zeta}}={pl_to_zeta[int(PL)]}$)')

    # Adjusted legend
    ax2.legend(loc='center left', bbox_to_anchor=(1.1, 0.5), ncol=1)

    ax1.view_init(elev=20, azim=-45) 
    ax2.view_init(elev=20, azim=-45)

    # --- THE FIX FOR CUT-OFF LABELS ---
    # Shrinks the 3D axes block slightly to leave room for outer labels
    try:
        ax1.set_box_aspect(None, zoom=0.8)
        ax2.set_box_aspect(None, zoom=0.8)
    except AttributeError:
        # Fallback if using an older version of Matplotlib
        ax1.dist = 11
        ax2.dist = 11

    # --- THE FIX FOR SPACING ---
    # Adjusted 'rect' to give slightly more left/bottom margin
    plt.tight_layout(rect=[0.02, 0.05, 0.88, 0.95])

    return fig
# --- 5. 2D Plot at fixed eta = 8 ---
def plot_2d_slice_eta8(all_data_dict, PL):
    # Increased figsize width to 24 to comfortably fit 4 columns
    fig, axes = plt.subplots(2, 4, figsize=(24, 12))
    fig.suptitle(fr'At Fixed $\eta|v|/a = 8$ ($\hat{{\zeta}}={pl_to_zeta[int(PL)]}$)', fontsize=18, fontweight='bold')

    for idx, (amp_name, data) in enumerate(all_data_dict.items()):
        # Safety catch in case more than 4 items are passed
        if idx >= 4:
            break

        if amp_name == "ReA2B":
            amp_print = "$\\tilde{{A}}_{{2B}}^{{Re}}$"
        elif amp_name == "ImA2B":
            amp_print = "$\\tilde{{A}}_{{2B}}^{{Im}}$"
        elif amp_name == "ReA12B":
            amp_print = "$\\tilde{{A}}_{{12B}}^{{Re}}$"
        elif amp_name == "ImA12B":
            amp_print = "$\\tilde{{A}}_{{12B}}^{{Im}}$"

        ax_top = axes[0, idx]
        ax_bot = axes[1, idx]

        if data is None: 
            ax_top.text(0.5, 0.5, "No data", ha='center', va='center')
            ax_bot.text(0.5, 0.5, "No data", ha='center', va='center')
            continue

        mask_eta8 = np.isclose(data['eta'], 8.0)
        bL_8 = data['bL'][mask_eta8]
        bT_8 = data['bT'][mask_eta8]
        mean_8 = data['mean'][mask_eta8]
        err_8 = data['error'][mask_eta8]

        if len(bL_8) == 0:
            ax_top.text(0.5, 0.5, "No data", ha='center', va='center')
            ax_bot.text(0.5, 0.5, "No data", ha='center', va='center')
            continue

        # ==========================================
        # TOP ROW: Amplitude vs bL, colored by bT
        # ==========================================
        unique_bT = np.unique(bT_8)
        colors_bT = get_distinct_colors(len(unique_bT))

        for i, val_bT in enumerate(unique_bT):
            sub_mask = (bT_8 == val_bT)
            ax_top.scatter(bL_8[sub_mask], mean_8[sub_mask], color=colors_bT[i], 
                           label=fr'$b_T/a={val_bT:.0f}$', zorder=5, s=50, edgecolors='k')
            ax_top.errorbar(bL_8[sub_mask], mean_8[sub_mask], yerr=err_8[sub_mask], 
                            fmt='none', ecolor=colors_bT[i], alpha=0.7, zorder=4, capsize=3)

        ax_top.set_title(fr'{amp_print} vs $b_L/a$', fontsize=14)
        ax_top.set_xlabel(r'$b_L/a$', fontsize=12)
        ax_top.set_ylabel(f'{amp_print}', fontsize=12)
        ax_top.grid(True, linestyle='--', alpha=0.5)
        ax_top.legend(fontsize='small', loc='best', 
                      ncol=(1 if len(unique_bT) <= 6 else 2))

        # ==========================================
        # BOTTOM ROW: Amplitude vs bT, colored by bL
        # ==========================================
        unique_bL = np.unique(bL_8)
        colors_bL = get_distinct_colors(len(unique_bL))[::-1] 

        for i, val_bL in enumerate(unique_bL):
            sub_mask = (bL_8 == val_bL)
            ax_bot.scatter(bT_8[sub_mask], mean_8[sub_mask], color=colors_bL[i], 
                           label=fr'$b_L/a={val_bL:.0f}$', zorder=5, s=50, edgecolors='k')
            ax_bot.errorbar(bT_8[sub_mask], mean_8[sub_mask], yerr=err_8[sub_mask], 
                            fmt='none', ecolor=colors_bL[i], alpha=0.7, zorder=4, capsize=3)

        ax_bot.set_title(fr'{amp_print} vs $b_T/a$', fontsize=14)
        ax_bot.set_xlabel(r'$b_T/a$', fontsize=12)
        ax_bot.set_ylabel(f'{amp_print}', fontsize=12)
        ax_bot.grid(True, linestyle='--', alpha=0.5)
        ax_bot.legend(fontsize='small', loc='best', 
                      ncol=(1 if len(unique_bL) <= 6 else 2))

    # Clean up empty subplots if fewer than 4 amplitudes are passed
    num_items = len(all_data_dict)
    for idx in range(num_items, 4):
        axes[0, idx].axis('off')
        axes[1, idx].axis('off')

    plt.tight_layout(rect=[0, 0, 1, 0.96])
    return fig

# ==========================================
# Main Execution Block
# ==========================================
PL_value = "-4" 
path_base = "/pscratch/sd/h/hari_8/TMD_fit/h5data"

amplitude_files = {
    "ReA2B":  f"{path_base}/ReA2B_PL{PL_value}_jackknife_data.h5",
    "ImA2B":  f"{path_base}/ImA2B_PL{PL_value}_jackknife_data.h5",
    "ReA12B": f"{path_base}/ReA12B_PL{PL_value}_jackknife_data.h5",
    "ImA12B": f"{path_base}/ImA12B_PL{PL_value}_jackknife_data.h5"
}

processed_data_store = {}

# 1. Generate and Save 3D Plots
for amp_name, file_path in amplitude_files.items():
    print(f"Processing 3D plots for {amp_name}...")
    amplitude_data = get_processed_amplitude_data(file_path)
    if amplitude_data is not None:
        processed_data_store[amp_name] = amplitude_data
        fig_3d = plot_3d_for_amplitude(amplitude_data, amp_name, PL_value)

        # --- SAVE 3D PLOT HERE ---
        save_name_3d = f"{amp_name}_PL{PL_value}_3D.pdf"
        plt.savefig(save_name_3d, format='pdf', dpi=300, bbox_inches='tight')
        print(f"Saved: {save_name_3d}")

        plt.show()

# 2. Generate and Save Combined 2D Plots (eta=7)
print("Processing 2D plots at fixed eta=8...")
if processed_data_store:
    fig_2d = plot_2d_slice_eta8(processed_data_store, PL_value)

    # --- SAVE 2D PLOT HERE ---
    save_name_2d = f"Combined_eta8_PL{PL_value}_2D.pdf"
    plt.savefig(save_name_2d, format='pdf', dpi=300, bbox_inches='tight')
    print(f"Saved: {save_name_2d}")

    plt.show()


# In[21]:


import h5py
import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D

# --- 1. Vectorized Jackknife Function ---
def jackknife_vectorized(samples):
    N = samples.shape[1]
    theta_bar = np.mean(samples, axis=1)
    squared_diffs = np.square(samples - theta_bar[:, None])
    sigma_sq = ((N - 1) / N) * np.sum(squared_diffs, axis=1)
    error = np.sqrt(sigma_sq)
    return theta_bar, error

pl_to_zeta = {
        -4: 0.785756,
        -3: 0.539684,
        -2: 0.294367,
        -1: 0.090772
    }

# --- 2. Data Loading Helper ---
def get_processed_amplitude_data(filepath, PL):
    try:
        with h5py.File(filepath, "r") as f:
            raw_data = f["Dataset1"][:]
    except FileNotFoundError:
        print(f"File not found: {filepath}")
        return None

    kin = raw_data[:, 0:3]
    samples = raw_data[:, 3:]

    eta, bL, bT = kin[:, 0], kin[:, 1], kin[:, 2]

    # Filter for base eta value from 1 to 10
    mask_eta = (eta >= 0) & (eta <= 10)
    eta_f, bL_f, bT_f = eta[mask_eta], bL[mask_eta], bT[mask_eta]

    # Calculate new variables
    # Using np.round to avoid floating point grouping issues in np.unique
    P_dot_b = np.round(bL_f * float(PL), 5)
    b_sq = np.round(bL_f**2 + bT_f**2, 5)

    mean_f, err_f = jackknife_vectorized(samples[mask_eta])

    return {
        'eta': eta_f, 
        'P_dot_b': P_dot_b, 
        'b_sq': b_sq,
        'mean': mean_f, 
        'error': err_f,
        'unique_P_dot_b': np.unique(P_dot_b), 
        'unique_b_sq': np.unique(b_sq)
    }

# --- 3. STRICTLY Distinct Color Generator ---
def get_distinct_colors(num_colors):
    """Returns a list of highly distinct, non-gradient colors."""
    distinct_hex = [
        '#e6194b', '#3cb44b', '#ffe119', '#4363d8', '#f58231',
        '#911eb4', '#46f0f0', '#f032e6', '#bcf60c', '#fabebe',
        '#008080', '#e6beff', '#9a6324', '#fffac8', '#800000',
        '#aaffc3', '#808000', '#ffd8b1', '#000075', '#808080',
        '#000000', '#333333'
    ]
    return [distinct_hex[i % len(distinct_hex)] for i in range(num_colors)]

# --- 4. 3D Plotting Function ---
def plot_3d_for_amplitude(data, amp_name, PL):
    fig = plt.figure(figsize=(16, 9))

    if amp_name == "ReA2B":
        amp_print = "$\\tilde{{A}}_{{2B}}^{{Re}}$"
    elif amp_name == "ImA2B":
        amp_print = "$\\tilde{{A}}_{{2B}}^{{Im}}$"
    elif amp_name == "ReA12B":
        amp_print = "$\\tilde{{A}}_{{12B}}^{{Re}}$"
    elif amp_name == "ImA12B":
        amp_print = "$\\tilde{{A}}_{{12B}}^{{Im}}$"

    # --- Plot 1: Y-axis is P.b, Color by distinct b^2 ---
    ax1 = fig.add_subplot(121, projection='3d')
    unique_b_sq = data['unique_b_sq']
    colors_b_sq = get_distinct_colors(len(unique_b_sq))

    for i, val_b_sq in enumerate(unique_b_sq):
        mask = (data['b_sq'] == val_b_sq)

        # 1. Plot the mean scatter points
        ax1.scatter(data['eta'][mask], data['P_dot_b'][mask], data['mean'][mask], 
                    color=colors_b_sq[i], label=fr'$b^2/a^2={val_b_sq:g}$', 
                    s=40, alpha=0.9, edgecolors='k', linewidth=0.3)

        # 2. Add the Z-axis error bars for Jackknife error
        ax1.errorbar(data['eta'][mask], data['P_dot_b'][mask], data['mean'][mask], 
                     zerr=data['error'][mask], fmt='none', ecolor=colors_b_sq[i], 
                     alpha=0.4, linewidth=1.0, zorder=0)

    ax1.set_xlabel(r'$\eta|v|/a$', fontsize=12, labelpad=10)
    ax1.set_ylabel(r'$(P \cdot b) \cdot \hat{L} / (2\pi)$', fontsize=12, labelpad=10)
    ax1.set_zlabel(f'{amp_print}', fontsize=12, labelpad=10)
    ax1.set_title(fr'{amp_print} ($\eta|v|/a$, $(P \cdot b)\cdot \hat{{L}} / (2\pi)$, $b^2/a^2$, $\hat{{\zeta}}={pl_to_zeta[int(PL)]}$)')
    ax1.legend(loc='center left', bbox_to_anchor=(1.1, 0.5), ncol=1)

    # --- Plot 2: Y-axis is b^2, Color by distinct P.b ---
    ax2 = fig.add_subplot(122, projection='3d')
    unique_P_dot_b = data['unique_P_dot_b']
    colors_P_dot_b = get_distinct_colors(len(unique_P_dot_b))[::-1] 

    for i, val_P_dot_b in enumerate(unique_P_dot_b):
        mask = (data['P_dot_b'] == val_P_dot_b)

        # 1. Plot the mean scatter points
        ax2.scatter(data['eta'][mask], data['b_sq'][mask], data['mean'][mask], 
                    color=colors_P_dot_b[i], label=fr'$(P \cdot b)\cdot \hat{{L}} / (2\pi)={val_P_dot_b:g}$', 
                    s=40, alpha=0.9, edgecolors='k', linewidth=0.3)

        # 2. Add the Z-axis error bars for Jackknife error
        ax2.errorbar(data['eta'][mask], data['b_sq'][mask], data['mean'][mask], 
                     zerr=data['error'][mask], fmt='none', ecolor=colors_P_dot_b[i], 
                     alpha=0.4, linewidth=1.0, zorder=0)

    ax2.set_xlabel(r'$\eta|v|/a$', fontsize=12, labelpad=10)
    ax2.set_ylabel(r'$b^2/a^2$', fontsize=12, labelpad=10)
    ax2.set_zlabel(f'{amp_print}', fontsize=12, labelpad=10)
    ax2.set_title(fr'{amp_print} ($\eta|v|/a$, $(P \cdot b)\cdot \hat{{L}} / (2\pi)$, $b^2/a^2$, $\hat{{\zeta}}={pl_to_zeta[int(PL)]}$)')
    ax2.legend(loc='center left', bbox_to_anchor=(1.1, 0.5), ncol=1)

    ax1.view_init(elev=20, azim=-45) 
    ax2.view_init(elev=20, azim=-45)

    try:
        ax1.set_box_aspect(None, zoom=0.8)
        ax2.set_box_aspect(None, zoom=0.8)
    except AttributeError:
        ax1.dist = 11
        ax2.dist = 11

    plt.tight_layout(rect=[0.02, 0.05, 0.88, 0.95])
    return fig

# --- 5. 2D Plot at fixed eta = 7 ---
def plot_2d_slice_eta7(all_data_dict, PL):
    fig, axes = plt.subplots(2, 4, figsize=(20, 12))
    fig.suptitle(fr'At Fixed $\eta|v|/a = 8$ ($\hat{{\zeta}}={pl_to_zeta[int(PL)]}$)', fontsize=18, fontweight='bold')

    for idx, (amp_name, data) in enumerate(all_data_dict.items()):
        if amp_name == "ReA2B":
            amp_print = "$\\tilde{{A}}_{{2B}}^{{Re}}$"
        elif amp_name == "ImA2B":
            amp_print = "$\\tilde{{A}}_{{2B}}^{{Im}}$"
        elif amp_name == "ReA12B":
            amp_print = "$\\tilde{{A}}_{{12B}}^{{Re}}$"
        elif amp_name == "ImA12B":
            amp_print = "$\\tilde{{A}}_{{12B}}^{{Im}}$"

        if data is None: continue

        ax_top = axes[0, idx]
        ax_bot = axes[1, idx]

        mask_eta7 = np.isclose(data['eta'], 8.0)
        P_dot_b_7 = data['P_dot_b'][mask_eta7]
        b_sq_7 = data['b_sq'][mask_eta7]
        mean_7 = data['mean'][mask_eta7]
        err_7 = data['error'][mask_eta7]

        if len(P_dot_b_7) == 0:
            ax_top.text(0.5, 0.5, "No data", ha='center', va='center')
            ax_bot.text(0.5, 0.5, "No data", ha='center', va='center')
            continue

        # ==========================================
        # TOP ROW: Amplitude vs P.b, colored by b^2
        # ==========================================
        unique_b_sq = np.unique(b_sq_7)
        colors_b_sq = get_distinct_colors(len(unique_b_sq))

        for i, val_b_sq in enumerate(unique_b_sq):
            sub_mask = (b_sq_7 == val_b_sq)
            ax_top.scatter(P_dot_b_7[sub_mask], mean_7[sub_mask], color=colors_b_sq[i], 
                           label=fr'$b^2/a^2={val_b_sq:g}$', zorder=5, s=50, edgecolors='k')
            ax_top.errorbar(P_dot_b_7[sub_mask], mean_7[sub_mask], yerr=err_7[sub_mask], 
                            fmt='none', ecolor=colors_b_sq[i], alpha=0.7, zorder=4, capsize=3)

        ax_top.set_title(fr'{amp_print} vs $(P \cdot b)\cdot \hat{{L}} / (2\pi)$', fontsize=14)
        ax_top.set_xlabel(r'$(P \cdot b) \cdot \hat{L} / (2\pi)$', fontsize=12)
        ax_top.set_ylabel(f'{amp_print}', fontsize=12)
        ax_top.grid(True, linestyle='--', alpha=0.5)
        ax_top.legend(fontsize='small', loc='best', 
                      ncol=(1 if len(unique_b_sq) <= 6 else 2))

        # ==========================================
        # BOTTOM ROW: Amplitude vs b^2, colored by P.b
        # ==========================================
        unique_P_dot_b = np.unique(P_dot_b_7)
        colors_P_dot_b = get_distinct_colors(len(unique_P_dot_b))[::-1] 

        for i, val_P_dot_b in enumerate(unique_P_dot_b):
            sub_mask = (P_dot_b_7 == val_P_dot_b)
            ax_bot.scatter(b_sq_7[sub_mask], mean_7[sub_mask], color=colors_P_dot_b[i], 
                           label=fr'$(P \cdot b)\cdot \hat{{L}} / (2\pi)={val_P_dot_b:g}$', zorder=5, s=50, edgecolors='k')
            ax_bot.errorbar(b_sq_7[sub_mask], mean_7[sub_mask], yerr=err_7[sub_mask], 
                            fmt='none', ecolor=colors_P_dot_b[i], alpha=0.7, zorder=4, capsize=3)

        ax_bot.set_title(fr'{amp_print} vs $b^2/a^2$', fontsize=14)
        ax_bot.set_xlabel(r'$b^2/a^2$', fontsize=12)
        ax_bot.set_ylabel(f'{amp_print}', fontsize=12)
        ax_bot.grid(True, linestyle='--', alpha=0.5)
        ax_bot.legend(fontsize='small', loc='best', 
                      ncol=(1 if len(unique_P_dot_b) <= 6 else 2))

    plt.tight_layout(rect=[0, 0, 1, 0.96])
    return fig

# ==========================================
# Main Execution Block
# ==========================================
PL_value = "-4" 
path_base = "/pscratch/sd/h/hari_8/TMD_fit/h5data"

amplitude_files = {
    "ReA2B":  f"{path_base}/ReA2B_PL{PL_value}_jackknife_data.h5",
    "ImA2B":  f"{path_base}/ImA2B_PL{PL_value}_jackknife_data.h5",
    "ReA12B": f"{path_base}/ReA12B_PL{PL_value}_jackknife_data.h5",
    "ImA12B": f"{path_base}/ImA12B_PL{PL_value}_jackknife_data.h5"
}

processed_data_store = {}

# 1. Generate and Save 3D Plots
for amp_name, file_path in amplitude_files.items():
    print(f"Processing 3D plots for {amp_name}...")
    # PASS PL_value so it can calculate P.b correctly
    amplitude_data = get_processed_amplitude_data(file_path, PL_value)
    if amplitude_data is not None:
        processed_data_store[amp_name] = amplitude_data
        fig_3d = plot_3d_for_amplitude(amplitude_data, amp_name, PL_value)

        # --- SAVE 3D PLOT HERE ---
        save_name_3d = f"{amp_name}_Pb_bsq_PL{PL_value}_3D.pdf"
        plt.savefig(save_name_3d, format='pdf', dpi=300, bbox_inches='tight')
        print(f"Saved: {save_name_3d}")

        plt.show()

# 2. Generate and Save Combined 2D Plots (eta=7)
print("Processing 2D plots at fixed eta=8...")
if processed_data_store:
    fig_2d = plot_2d_slice_eta7(processed_data_store, PL_value)

    # --- SAVE 2D PLOT HERE ---
    save_name_2d = f"Combined_Pb_bsq_eta8_PL{PL_value}_2D.pdf"
    plt.savefig(save_name_2d, format='pdf', dpi=300, bbox_inches='tight')
    print(f"Saved: {save_name_2d}")

    plt.show()


# In[ ]:




