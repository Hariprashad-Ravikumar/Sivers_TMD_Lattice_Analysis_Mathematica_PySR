"""
Thesis versions of the amplitude-with-fit figures (Chapter 6, Simultaneous Fit Results).

Same data, fit model and Jackknife bands as Plot_Fit_on_Amps.ipynb (cells 0 and 1),
but with print-size fonts and legends placed under the panels:

  3D (eta, coordinate, amplitude), two panels side by side, legends underneath:
    {amp}_PL{k}_WithFit_3D.pdf             [vs b_L (by b_T) | vs b_T (by b_L)]
    {amp}_Pb_bsq_PL{k}_WithFit_3D.pdf      [vs P.b (by b^2) | vs b^2 (by P.b)]
  2D at eta|v|/a = 8, one 1x2 row per file:
    {amp}_eta8_PL{k}_WithFit_2D.pdf        [vs b_L | vs b_T]
    {amp}_Pb_bsq_eta8_PL{k}_WithFit_2D.pdf [vs P.b | vs b^2]

Data: |b| >= 3a and 6 <= eta <= 10, as in the notebook.
"""
import os
import math

import h5py
import numpy as np
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
path_base = os.path.join(HERE, "..", "h5data")
out_dir = os.path.abspath(os.path.join(
    HERE, "..", "..", "..", "..",
    "Lattice-QCD-calculations-of-x-dependence-of-Sivers-TMD-Hariprashad-Ravikumar-NMSU-PhD-Thesis",
    "plots", "Amps_Fit"))

PL_VALUES = [-1, -2, -3, -4]
AMPLITUDES = ["ReA2B", "ImA2B", "ReA12B"]
bminfit, etamin, etamax = 3, 6, 10

pl_to_zeta = {-4: 0.785756, -3: 0.539684, -2: 0.294367, -1: 0.090772}

AMP_PRINT = {
    "ReA2B": r"$\tilde{A}_{2B}^{Re}$",
    "ImA2B": r"$\tilde{A}_{2B}^{Im}$",
    "ReA12B": r"$\tilde{A}_{12B}^{Re}$",
}
PB_LABEL = r'$(P \cdot b)\cdot \hat{L} / (2\pi)$'

plt.rcParams.update({
    "font.size": 16,
    "axes.labelsize": 19,
    "axes.titlesize": 18,
    "xtick.labelsize": 14,
    "ytick.labelsize": 14,
    "legend.fontsize": 14,
})


# --- Jackknife helpers (as in Plot_Fit_on_Amps.ipynb) ---
def jackknife_vectorized(samples):
    N = samples.shape[1]
    theta_bar = np.mean(samples, axis=1)
    squared_diffs = np.square(samples - theta_bar[:, None])
    sigma_sq = ((N - 1) / N) * np.sum(squared_diffs, axis=1)
    error = np.sqrt(sigma_sq)
    return theta_bar, error


def Jackknife(datalist):
    N = len(datalist)
    theta_bar = np.mean(datalist)
    sigma_sq = ((N - 1) / N) * np.sum(np.square(np.asarray(datalist) - theta_bar))
    return theta_bar, np.sqrt(sigma_sq)


def fmt_err(mean, err):
    if err <= 0:
        return f"{mean}"
    if mean and (abs(mean) < 1e-3 or abs(mean) >= 1e3):
        exp = int(math.floor(math.log10(abs(mean))))
        mean_scaled, err_scaled = mean / 10**exp, err / 10**exp
        place = int(math.floor(math.log10(abs(err_scaled))))
        ndec = max(0, -(place - 1))
        return f"{mean_scaled:.{ndec}f}({int(round(err_scaled * 10**ndec))})e{exp}"
    place = int(math.floor(math.log10(abs(err))))
    ndec = max(0, -(place - 1))
    return f"{mean:.{ndec}f}({int(round(err * 10**ndec))})"


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


# --- Data loading (cell 1 version: also returns P.b and b^2) ---
def get_processed_amplitude_data(filepath, PL):
    with h5py.File(filepath, "r") as f:
        raw_data = f["Dataset1"][:]
    kin, samples = raw_data[:, 0:3], raw_data[:, 3:]
    eta, bL, bT = kin[:, 0], kin[:, 1], kin[:, 2]
    mask_eta = (eta >= 6) & (eta <= 10) & (np.sqrt(bL**2 + bT**2) >= 3)
    eta_f, bL_f, bT_f = eta[mask_eta], bL[mask_eta], bT[mask_eta]
    mean_f, err_f = jackknife_vectorized(samples[mask_eta])
    return {
        'eta': eta_f, 'bL': bL_f, 'bT': bT_f,
        'P_dot_b': np.round(bL_f * float(PL), 5) + 0.0,  # +0.0 turns -0.0 into 0.0
        'b_sq': np.round(bL_f**2 + bT_f**2, 5),
        'mean': mean_f, 'error': err_f,
    }


# --- Fit evaluation (cell 1 version, takes bT^2) ---
def eval_fit_jk(amp_name, eta, bL, bT_sq, params):
    eta, bL, bT_sq = np.atleast_1d(eta), np.atleast_1d(bL), np.atleast_1d(bT_sq)
    if amp_name == "ReA2B":
        a, c, d, f = params['a_re'], params['c_re'], params['d_re'], params['f']
        k1, k2, j = params['k1_re'], params['k2_re'], params['j_re']
        a, c, d, f = a[:, None], c[:, None], d[:, None], f[:, None]
        k1, k2, j = k1[:, None], k2[:, None], j[:, None]
        denom = (1 + (d + c * (1 - k1/eta - k2/eta**2)) * bL**2 + d * bT_sq)**j
        val = a * np.exp(-f * eta) / denom
    elif amp_name == "ImA2B":
        a, c, d, f = params['a_im'], params['c_im'], params['d_im'], params['f']
        j = params['j_im']
        a, c, d, f, j = a[:, None], c[:, None], d[:, None], f[:, None], j[:, None]
        denom = (1 + (c + d) * bL**2 + d * bT_sq)**j
        val = a * bL * np.exp(-f * eta) / denom
    elif amp_name == "ReA12B":
        a, c, d, f = params['a_reA12B'], params['c_reA12B'], params['d_reA12B'], params['f']
        j = params['j_reA12B']
        a, c, d, f, j = a[:, None], c[:, None], d[:, None], f[:, None], j[:, None]
        denom = (1 + (c + d) * bL**2 + d * bT_sq)**j
        val = -a * np.exp(-f * eta) / denom
    N = val.shape[0]
    mean_val = np.mean(val, axis=0)
    err_val = np.sqrt(((N - 1) / N) * np.sum(np.square(val - mean_val), axis=0))
    return mean_val, err_val


def eval_fit_jk_new_coords(amp_name, eta, P_dot_b, b_sq, params, PL):
    bL = P_dot_b / float(PL)
    return eval_fit_jk(amp_name, eta, bL, b_sq - bL**2, params)


def load_params_from_h5(filename):
    fitted_params = {}
    with h5py.File(filename, "r") as f:
        for key in f["jackknife_samples"].keys():
            fitted_params[key] = f["jackknife_samples"][key][:]
        chi2_dof_list = f["chi2_dof"][:]
    return fitted_params, chi2_dof_list


# --- The four coordinate views: (y-variable, color-variable, label text, fit evaluator) ---
def views(data, amp, params, PL):
    """Returns, per view: y values, group values, labels, and fit(eta_grid, y_grid, group) -> mean, err."""
    max_bL, min_bL = data['bL'].max(), data['bL'].min()
    max_bT, min_bT = data['bT'].max(), data['bT'].min()
    max_bsq = data['b_sq'].max()
    max_Pb = np.sqrt(max_bsq) * abs(float(PL))
    return {
        "bL": dict(y=data['bL'], g=data['bT'], ylab=r'$b_L/a$', glab=lambda v: f'{v:.0f}', gtitle=r'$b_T/a$', rev=False,
                   ygrid=lambda g: np.linspace(min_bL, max_bL, 150),
                   fit=lambda e, y, g: eval_fit_jk(amp, e, y, np.full_like(y, g)**2, params)),
        "bT": dict(y=data['bT'], g=data['bL'], ylab=r'$b_T/a$', glab=lambda v: f'{v:.0f}', gtitle=r'$b_L/a$', rev=True,
                   ygrid=lambda g: np.linspace(min_bT, max_bT, 150),
                   fit=lambda e, y, g: eval_fit_jk(amp, e, np.full_like(y, g), y**2, params)),
        "Pb": dict(y=data['P_dot_b'], g=data['b_sq'], ylab=PB_LABEL, glab=lambda v: f'{v:.0f}', gtitle=r'$b^2/a^2$', rev=False,
                   ygrid=lambda g: np.linspace(-max_Pb, max_Pb, 300),
                   fit=lambda e, y, g: eval_fit_jk_new_coords(amp, e, y, np.full_like(y, g), params, PL)),
        "bsq": dict(y=data['b_sq'], g=data['P_dot_b'], ylab=r'$b^2/a^2$', glab=lambda v: f'{v:.0f}', gtitle=PB_LABEL, rev=True,
                    ygrid=lambda g: np.linspace((g / float(PL))**2, max_bsq, 300),
                    fit=lambda e, y, g: eval_fit_jk_new_coords(amp, e, np.full_like(y, g), y, params, PL)),
    }


def legend_cols(n):
    return 1 if n <= 8 else 2


def draw_3d(ax, data, amp, v):
    groups = np.unique(v['g'])
    colors = get_distinct_colors(len(groups))
    if v['rev']:
        colors = colors[::-1]
    eta_grid = np.linspace(6.0, data['eta'].max(), 30)
    for i, gv in enumerate(groups):
        sel = (v['g'] == gv)
        ax.scatter(data['eta'][sel], v['y'][sel], data['mean'][sel], color=colors[i], label=v['glab'](gv),
                   marker='o', s=45, alpha=0.9, edgecolors='k', linewidth=0.3)
        ax.errorbar(data['eta'][sel], v['y'][sel], data['mean'][sel], zerr=data['error'][sel], fmt='none',
                    ecolor=colors[i], alpha=0.4, linewidth=1.0, zorder=0)
        yg = v['ygrid'](gv)
        ETA, Y = np.meshgrid(eta_grid, yg[::max(1, len(yg) // 50)])
        m, e = v['fit'](ETA.flatten(), Y.flatten(), gv)
        m, e = m.reshape(ETA.shape), e.reshape(ETA.shape)
        ax.plot_surface(ETA, Y, m, color=colors[i], alpha=0.2, rstride=5, cstride=5)
        ax.plot_surface(ETA, Y, m + e, color=colors[i], alpha=0.1, rstride=5, cstride=5)
        ax.plot_surface(ETA, Y, m - e, color=colors[i], alpha=0.1, rstride=5, cstride=5)
    ax.set_xlabel(r'$\eta|v|/a$', labelpad=14)
    ax.set_ylabel(v['ylab'], labelpad=16)
    ax.set_zlabel(AMP_PRINT[amp], labelpad=30)
    ax.zaxis.set_major_locator(plt.MaxNLocator(5))
    ax.set_xticks([6, 8, 10])
    ax.tick_params(axis='z', pad=9)
    ax.view_init(elev=10, azim=-45)
    try:
        ax.set_box_aspect(None, zoom=0.88)
    except TypeError:
        pass
    return len(groups)


def plot_3d_row(data, amp, vv, keys, PL, chi2_str):
    """Two 3D panels side by side, each with its legend underneath."""
    with plt.rc_context({"axes.labelsize": 22, "xtick.labelsize": 16, "ytick.labelsize": 16}):
        fig = plt.figure(figsize=(17, 9.2))
        for col, key in enumerate(keys):
            ax = fig.add_axes([0.46 * col - 0.03, 0.26, 0.43, 0.68], projection='3d')   # leave room right of each box for the z-label
            n = draw_3d(ax, data, amp, vv[key])
            h, l = ax.get_legend_handles_labels()
            fig.legend(h, l, loc='upper center', bbox_to_anchor=(0.19 + 0.46 * col, 0.255),
                       ncol=min(n, 8), fontsize=16, title=vv[key]['gtitle'], title_fontsize=17,
                       frameon=False, handletextpad=0.1, columnspacing=0.7)
        fig.suptitle(fr'{AMP_PRINT[amp]},  $\hat{{\zeta}}={pl_to_zeta[PL]}$,  $\chi^2/\mathrm{{DoF}}={chi2_str}$',
                     y=0.985, fontsize=21)
        # bbox_inches='tight' ignores 3D axis labels; this blank anchor keeps the right z-label inside the crop
        fig.text(0.955, 0.6, ' ', fontsize=1)
    return fig


def plot_2d_panel(ax, data, amp, view, title):
    v = view
    m8 = np.isclose(data['eta'], 8.0)
    groups = np.unique(v['g'][m8])
    colors = get_distinct_colors(len(groups))
    if v['rev']:
        colors = colors[::-1]
    for i, gv in enumerate(groups):
        sel = m8 & (v['g'] == gv)
        ax.errorbar(v['y'][sel], data['mean'][sel], yerr=data['error'][sel], fmt='o', color=colors[i],
                    markersize=7, markeredgecolor='k', markeredgewidth=0.6, ecolor=colors[i],
                    elinewidth=1.4, capsize=3, zorder=5, label=v['glab'](gv))
        yg = v['ygrid'](gv)
        mf, ef = v['fit'](np.full_like(yg, 8.0), yg, gv)
        ax.plot(yg, mf, color=colors[i], zorder=3)
        ax.fill_between(yg, mf - ef, mf + ef, color=colors[i], alpha=0.2, zorder=2)
    ax.set_xlabel(v['ylab'])
    ax.set_ylabel(AMP_PRINT[amp])
    ax.set_title(title)
    ax.grid(True, linestyle='--', alpha=0.5)
    ax.legend(loc='upper center', bbox_to_anchor=(0.5, -0.27), ncol=min(len(groups), 9), fontsize=13,
              title=v['gtitle'], title_fontsize=14, frameon=False, handletextpad=0.1, columnspacing=0.6)
    return len(groups)


def plot_2d_row(data, amp, vv, keys, PL, chi2_str):
    fig, axes = plt.subplots(1, 2, figsize=(13, 7.6))
    head = fr'{AMP_PRINT[amp]},  $\eta|v|/a=8$,  $\hat{{\zeta}}={pl_to_zeta[PL]}$,  $\chi^2/\mathrm{{DoF}}={chi2_str}$'
    plot_2d_panel(axes[0], data, amp, vv[keys[0]], '')
    plot_2d_panel(axes[1], data, amp, vv[keys[1]], '')
    if keys[1] == "bsq":
        axes[1].set_xlim(left=9)
    fig.suptitle(head, y=0.99)
    fig.tight_layout(rect=[0, 0, 1, 0.96], w_pad=2.0)
    return fig


if __name__ == "__main__":
    for PL in PL_VALUES:
        fit_file = f"{path_base}/FitParams_SimulFit_f_A2BRe_cetasq_A2BIm_A12BRe_bmin{bminfit}_eta{etamin}{etamax}_PL{PL}.h5"
        params, chi2_list = load_params_from_h5(fit_file)
        chi2_str = fmt_err(*Jackknife(chi2_list))
        for amp in AMPLITUDES:
            data = get_processed_amplitude_data(f"{path_base}/{amp}_PL{PL}_jackknife_data.h5", PL)
            vv = views(data, amp, params, PL)
            for keys, fname in [(("bL", "bT"), f"{amp}_PL{PL}_WithFit_3D.pdf"),
                                (("Pb", "bsq"), f"{amp}_Pb_bsq_PL{PL}_WithFit_3D.pdf")]:
                fig = plot_3d_row(data, amp, vv, keys, PL, chi2_str)
                fig.savefig(os.path.join(out_dir, fname), bbox_inches='tight')
                plt.close(fig)
            for keys, fname in [(("bL", "bT"), f"{amp}_eta8_PL{PL}_WithFit_2D.pdf"),
                                (("Pb", "bsq"), f"{amp}_Pb_bsq_eta8_PL{PL}_WithFit_2D.pdf")]:
                fig = plot_2d_row(data, amp, vv, keys, PL, chi2_str)
                fig.savefig(os.path.join(out_dir, fname), bbox_inches='tight')
                plt.close(fig)
            print(f"PL={PL} {amp}: done (chi2/DoF={chi2_str})")
