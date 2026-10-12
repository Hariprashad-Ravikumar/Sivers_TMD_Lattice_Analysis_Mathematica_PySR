"""
Split version of the fixed-eta 2D amplitude plots from Plot_Amps.ipynb.

Instead of one 2x4 Combined_*_2D.pdf per P_L, write one 1x2 row per amplitude
and per variable space, so the thesis can stack them like the 3D figures:

    {amp}_eta8_PL{PL}_2D.pdf         : [amp vs bL (colored by bT) | amp vs bT (colored by bL)]
    {amp}_Pb_bsq_eta8_PL{PL}_2D.pdf  : [amp vs P.b (colored by b^2) | amp vs b^2 (colored by P.b)]

Helpers and panel styling are copied from cells 0 and 1 of Plot_Amps.ipynb.
"""
import os

import h5py
import numpy as np
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
path_base = os.path.join(HERE, "..", "h5data")
out_dir = os.path.abspath(os.path.join(
    HERE, "..", "..", "..", "..",
    "Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-Hariprashad-Ravikumar-NMSU-PhD-Thesis",
    "plots", "Amps_Fit"))

ETA_SLICE = 8.0
PL_VALUES = ["-1", "-2", "-3", "-4"]
AMPLITUDES = ["ReA2B", "ImA2B", "ReA12B", "ImA12B"]

pl_to_zeta = {
        -4: 0.785756,
        -3: 0.539684,
        -2: 0.294367,
        -1: 0.090772
    }

AMP_PRINT = {
    "ReA2B": "$\\tilde{{A}}_{{2B}}^{{Re}}$",
    "ImA2B": "$\\tilde{{A}}_{{2B}}^{{Im}}$",
    "ReA12B": "$\\tilde{{A}}_{{12B}}^{{Re}}$",
    "ImA12B": "$\\tilde{{A}}_{{12B}}^{{Im}}$",
}


# --- 1. Vectorized Jackknife Function ---
def jackknife_vectorized(samples):
    N = samples.shape[1]
    theta_bar = np.mean(samples, axis=1)
    squared_diffs = np.square(samples - theta_bar[:, None])
    sigma_sq = ((N - 1) / N) * np.sum(squared_diffs, axis=1)
    error = np.sqrt(sigma_sq)
    return theta_bar, error


# --- 2. Data Loading Helper (both variable spaces) ---
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

    # Using np.round to avoid floating point grouping issues in np.unique
    P_dot_b = np.round(bL_f * float(PL), 5)
    b_sq = np.round(bL_f**2 + bT_f**2, 5)

    mean_f, err_f = jackknife_vectorized(samples[mask_eta])

    return {
        'eta': eta_f, 'bL': bL_f, 'bT': bT_f,
        'P_dot_b': P_dot_b, 'b_sq': b_sq,
        'mean': mean_f, 'error': err_f,
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


# --- 4. One panel: amplitude vs x, one color per distinct value of c ---
def plot_panel(ax, x, c, mean, err, colors, c_label_fmt, title, xlabel, amp_print):
    unique_c = np.unique(c)
    for i, val_c in enumerate(unique_c):
        sub_mask = (c == val_c)
        ax.scatter(x[sub_mask], mean[sub_mask], color=colors[i],
                   label=c_label_fmt(val_c), zorder=5, s=50, edgecolors='k')
        ax.errorbar(x[sub_mask], mean[sub_mask], yerr=err[sub_mask],
                    fmt='none', ecolor=colors[i], alpha=0.7, zorder=4, capsize=3)

    ax.set_title(title, fontsize=14)
    ax.set_xlabel(xlabel, fontsize=12)
    ax.set_ylabel(f'{amp_print}', fontsize=12)
    ax.grid(True, linestyle='--', alpha=0.5)
    ax.legend(fontsize='small', loc='best',
              ncol=(1 if len(unique_c) <= 6 else 2))


# --- 5. 1x2 rows at fixed eta = 8 ---
def plot_row_bL_bT(data, amp_name, PL):
    amp_print = AMP_PRINT[amp_name]
    m = np.isclose(data['eta'], ETA_SLICE)
    bL_8, bT_8 = data['bL'][m], data['bT'][m]
    mean_8, err_8 = data['mean'][m], data['error'][m]
    suffix = fr' ($\eta|v|/a = 8$, $\hat{{\zeta}}={pl_to_zeta[int(PL)]}$)'

    fig, (ax_l, ax_r) = plt.subplots(1, 2, figsize=(14, 5))
    plot_panel(ax_l, bL_8, bT_8, mean_8, err_8,
               get_distinct_colors(len(np.unique(bT_8))),
               lambda v: fr'$b_T/a={v:.0f}$',
               fr'{amp_print} vs $b_L/a$' + suffix, r'$b_L/a$', amp_print)
    plot_panel(ax_r, bT_8, bL_8, mean_8, err_8,
               get_distinct_colors(len(np.unique(bL_8)))[::-1],
               lambda v: fr'$b_L/a={v:.0f}$',
               fr'{amp_print} vs $b_T/a$' + suffix, r'$b_T/a$', amp_print)
    plt.tight_layout()
    return fig


def plot_row_Pb_bsq(data, amp_name, PL):
    amp_print = AMP_PRINT[amp_name]
    m = np.isclose(data['eta'], ETA_SLICE)
    Pb_8, bsq_8 = data['P_dot_b'][m], data['b_sq'][m]
    mean_8, err_8 = data['mean'][m], data['error'][m]
    suffix = fr' ($\eta|v|/a = 8$, $\hat{{\zeta}}={pl_to_zeta[int(PL)]}$)'

    fig, (ax_l, ax_r) = plt.subplots(1, 2, figsize=(14, 5))
    plot_panel(ax_l, Pb_8, bsq_8, mean_8, err_8,
               get_distinct_colors(len(np.unique(bsq_8))),
               lambda v: fr'$b^2/a^2={v:g}$',
               fr'{amp_print} vs $(P \cdot b)\cdot \hat{{L}} / (2\pi)$' + suffix,
               r'$(P \cdot b) \cdot \hat{L} / (2\pi)$', amp_print)
    plot_panel(ax_r, bsq_8, Pb_8, mean_8, err_8,
               get_distinct_colors(len(np.unique(Pb_8)))[::-1],
               lambda v: fr'$(P \cdot b)\cdot \hat{{L}} / (2\pi)={v:g}$',
               fr'{amp_print} vs $b^2/a^2$' + suffix, r'$b^2/a^2$', amp_print)
    plt.tight_layout()
    return fig


# ==========================================
# Main Execution Block
# ==========================================
if __name__ == "__main__":
    for PL_value in PL_VALUES:
        for amp_name in AMPLITUDES:
            file_path = f"{path_base}/{amp_name}_PL{PL_value}_jackknife_data.h5"
            data = get_processed_amplitude_data(file_path, PL_value)
            if data is None:
                continue

            for make_fig, tag in [(plot_row_bL_bT, ""), (plot_row_Pb_bsq, "_Pb_bsq")]:
                fig = make_fig(data, amp_name, PL_value)
                save_name = os.path.join(out_dir, f"{amp_name}{tag}_eta8_PL{PL_value}_2D.pdf")
                fig.savefig(save_name, format='pdf', dpi=300, bbox_inches='tight')
                plt.close(fig)
                print(f"Saved: {save_name}")
