"""
Short-distance vs long-distance amplitude data for the thesis fitting chapter
(Figures short-dis1 / short-dis2).

At P_L=-1 and eta|v|/a=8, plot ReA2B and ReA12B against (P.b).L/(2pi), one color
per b^2, split into |b|<3a (b^2<9, left) and |b|>=3a (b^2>=9, right).
The +bT / -bT entries at the same (P.b, b^2) are averaged (see load_eta_slice).

    A2B_Re_b_lessthan3_and_ge3.pdf
    A12B_Re_b_lessthan3_and_ge3.pdf

Loading and jackknife are the same as in Plot_Amps.ipynb / plot_amps_eta8_split.py.
Replaces the earlier Mathematica exports with larger, print-readable fonts.
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
    "plots", "short_distance"))

PL = -1
ETA_SLICE = 8.0
B_SQ_CUT = 9.0   # |b| >= 3a  <=>  b^2 >= 9

AMPS = {
    "ReA2B":  (r"$\tilde{A}_{2B}^{Re}$",  "A2B_Re_b_lessthan3_and_ge3.pdf"),
    "ReA12B": (r"$\tilde{A}_{12B}^{Re}$", "A12B_Re_b_lessthan3_and_ge3.pdf"),
}

plt.rcParams.update({
    "font.size": 17,
    "axes.labelsize": 21,
    "axes.titlesize": 21,
    "xtick.labelsize": 17,
    "ytick.labelsize": 17,
    "legend.fontsize": 16,
})


# --- Vectorized Jackknife Function ---
def jackknife_vectorized(samples):
    N = samples.shape[1]
    theta_bar = np.mean(samples, axis=1)
    squared_diffs = np.square(samples - theta_bar[:, None])
    sigma_sq = ((N - 1) / N) * np.sum(squared_diffs, axis=1)
    error = np.sqrt(sigma_sq)
    return theta_bar, error


# --- STRICTLY Distinct Color Generator ---
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


def load_eta_slice(amp_name):
    """One point per (P.b, b^2): the +bT and -bT entries are averaged per jackknife
    sample before the jackknife error, as in the original Mathematica figures."""
    with h5py.File(f"{path_base}/{amp_name}_PL{PL}_jackknife_data.h5", "r") as f:
        raw_data = f["Dataset1"][:]
    eta, bL, bT = raw_data[:, 0], raw_data[:, 1], raw_data[:, 2]
    m = np.isclose(eta, ETA_SLICE)
    P_dot_b_all = np.round(bL[m] * float(PL), 5) + 0.0   # normalize -0.0 to 0.0
    b_sq_all = np.round(bL[m]**2 + bT[m]**2, 5)
    samples = raw_data[m, 3:]

    keys = sorted(set(zip(P_dot_b_all.tolist(), b_sq_all.tolist())))
    avg_samples = np.array([samples[(P_dot_b_all == pb) & (b_sq_all == bsq)].mean(axis=0)
                            for pb, bsq in keys])
    mean, err = jackknife_vectorized(avg_samples)
    P_dot_b = np.array([k[0] for k in keys])
    b_sq = np.array([k[1] for k in keys])
    return P_dot_b, b_sq, mean, err


def plot_panel(ax, P_dot_b, b_sq, mean, err, title, amp_print, ncol):
    unique_b_sq = np.unique(b_sq)
    colors = get_distinct_colors(len(unique_b_sq))
    for i, val in enumerate(unique_b_sq):
        sel = (b_sq == val)
        ax.errorbar(P_dot_b[sel], mean[sel], yerr=err[sel], fmt='o', color=colors[i],
                    markersize=8.5, markeredgecolor='k', markeredgewidth=0.6,
                    ecolor=colors[i], elinewidth=1.6, capsize=4, zorder=5,
                    label=fr'$b^2/a^2={val:g}$')
    ax.axhline(0, color='k', linewidth=0.8, zorder=1)
    ax.axvline(0, color='k', linewidth=0.8, zorder=1)
    ax.set_title(title)
    ax.set_xlabel(r'$(P \cdot b) \cdot \hat{L} / (2\pi)$')
    ax.set_ylabel(amp_print)
    ax.grid(True, linestyle='--', alpha=0.5)
    ax.legend(loc='center left', bbox_to_anchor=(1.01, 0.5), ncol=ncol,
              frameon=False, handletextpad=0.2, columnspacing=0.8)


if __name__ == "__main__":
    for amp_name, (amp_print, fname) in AMPS.items():
        P_dot_b, b_sq, mean, err = load_eta_slice(amp_name)
        short = b_sq < B_SQ_CUT

        fig, (ax_l, ax_r) = plt.subplots(1, 2, figsize=(18, 5.5),
                                         gridspec_kw={'width_ratios': [1, 1]})
        plot_panel(ax_l, P_dot_b[short], b_sq[short], mean[short], err[short],
                   r'$|b| < 3a$', amp_print, ncol=1)
        plot_panel(ax_r, P_dot_b[~short], b_sq[~short], mean[~short], err[~short],
                   r'$|b| \geq 3a$', amp_print, ncol=2)
        fig.tight_layout(w_pad=1.5)

        save_name = os.path.join(out_dir, fname)
        fig.savefig(save_name, format='pdf', bbox_inches='tight')
        plt.close(fig)
        print(f"Saved: {save_name}")
