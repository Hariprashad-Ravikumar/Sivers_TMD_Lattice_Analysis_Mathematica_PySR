"""
Factorization ratio test for the Sivers shift, at each finite P_L individually
(no zeta_hat -> infinity extrapolation).

Same two ratio constructions as Factorization_Test_SiversShift.ipynb's Figures 1-2,
but evaluated directly on each P_L's raw fitted parameters:

    R_b(x) = <k_y>_TU(x,b_i) / <k_y>_TU(x,b_ref)   -- flat in x <=> factorized
    R_x(b) = <k_y>_TU(x_i,b) / <k_y>_TU(x_ref,b)   -- flat in b <=> factorized

Standalone: run directly with `python Factorization_Test_FinitePL.py`.
"""
import h5py
import numpy as np
import matplotlib.pyplot as plt
from scipy.special import kv, gamma

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------
DATA_DIR = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/TMD_fit/h5data"

lata = 0.11403  # lattice spacing in fm

bminfit = 3
etamin, etamax = 6, 10
PL_LIST = [-1, -2, -3, -4]

param_names = ['a_re', 'c_re', 'j_re', 'd_re',
               'a_im', 'c_im', 'j_im', 'd_im',
               'a_reA12B', 'c_reA12B', 'j_reA12B', 'd_reA12B']


# ---------------------------------------------------------------------------
# Helpers (copied verbatim from Factorization_Test_SiversShift.ipynb)
# ---------------------------------------------------------------------------
def Jackknife(datalist):
    N = len(datalist)
    theta_bar = np.mean(datalist)
    theta_nminus_theta_bar = []
    for i in range(N):
        theta_n = datalist[i]
        theta_nminus_theta_bar.append(np.square(theta_n - theta_bar))
    sigma_sq = ((N - 1) / N) * np.sum(theta_nminus_theta_bar)
    return theta_bar, np.sqrt(sigma_sq)


def load_params_from_h5(filename):
    fitted_params = {}
    with h5py.File(filename, "r") as f:
        param_group = f["jackknife_samples"]
        for key in param_group.keys():
            fitted_params[key] = param_group[key][:]
    return fitted_params


def jk_stats(arr, axis=0):
    """Vectorized jackknife mean/error over `axis` (the jackknife-sample axis)."""
    N = arr.shape[axis]
    m = np.mean(arr, axis=axis)
    e = np.sqrt(((N - 1) / N) * np.sum((arr - np.expand_dims(m, axis))**2, axis=axis))
    return m, e


# ---------------------------------------------------------------------------
# Load a single P_L's raw (unextrapolated) parameters, with the same
# per-P_L scaling rules used in Extrapolation_para_level.ipynb /
# Factorization_Test_SiversShift.ipynb's build_extrapolated_params().
# ---------------------------------------------------------------------------
def load_raw_params_for_pl(pl, data_dir=DATA_DIR):
    filename = f"{data_dir}/FitParams_SimulFit_f_A2BRe_cetasq_A2BIm_A12BRe_bmin{bminfit}_eta{etamin}{etamax}_PL{pl}.h5"
    params = load_params_from_h5(filename)

    p = {}
    p['a_re'] = params['a_re']
    p['c_re'] = params['c_re'] / (pl**2)
    p['j_re'] = params['j_re']
    p['d_re'] = params['d_re']

    p['a_im'] = params['a_im'] / pl
    p['c_im'] = params['c_im'] / (pl**2)
    p['j_im'] = params['j_im']
    p['d_im'] = params['d_im']

    p['a_reA12B'] = params['a_reA12B']
    p['c_reA12B'] = params['c_reA12B'] / (pl**2)
    p['j_reA12B'] = params['j_reA12B']
    p['d_reA12B'] = params['d_reA12B']

    return p


def load_massterm(data_dir=DATA_DIR):
    mass_filepath = f"{data_dir}/MassN_Jackknife.h5"
    with h5py.File(mass_filepath, "r") as f:
        MassN_jk = f["PL_-1"][:]
    return MassN_jk * (197.32698 * 0.001 / lata)


# ---------------------------------------------------------------------------
# Evaluate the Sivers shift on a grid of x at one fixed b^2, returning RAW
# per-jackknife-sample values (N_JK, N_x) -- ratios are formed from these
# before any jackknife reduction. Verbatim formulas from the notebook.
# ---------------------------------------------------------------------------
def eval_obs_jk(p_dict, x_grid, b2, massterm):
    x_grid = np.asarray(x_grid, dtype=float)
    abs_x = np.abs(x_grid).copy()
    abs_x[abs_x == 0] = 1e-12
    safe_x = np.where(x_grid == 0, 1e-12, x_grid)

    a_R, c_R = p_dict['a_re'][:, None], p_dict['c_re'][:, None]
    d_R, j_R = (1.0 + p_dict['d_re'] * b2)[:, None], p_dict['j_re'][:, None]

    a_I, c_I = p_dict['a_im'][:, None], p_dict['c_im'][:, None]
    d_I, j_I = (1.0 + p_dict['d_im'] * b2)[:, None], p_dict['j_im'][:, None]

    a_A, c_A = -p_dict['a_reA12B'][:, None], p_dict['c_reA12B'][:, None]
    d_A, j_A = (1.0 + p_dict['d_reA12B'] * b2)[:, None], p_dict['j_reA12B'][:, None]

    mt = massterm[:, None]

    cd_R = c_R / d_R
    t1_R = (2**(1 - j_R) * a_R * cd_R**(-0.25 - j_R / 2) * d_R**(-j_R)) / gamma(j_R)
    re = t1_R * (abs_x[None, :]**(-0.5 + j_R)) * kv(0.5 - j_R, abs_x[None, :] / np.sqrt(cd_R))

    cd_I = c_I / d_I
    t1_I = (2**(1 - j_I) * a_I * cd_I**(0.25 * (-3 - 2 * j_I)) * d_I**(-j_I)) / gamma(j_I)
    im = t1_I * (safe_x[None, :] * abs_x[None, :]**(-1.5 + j_I)) * kv(1.5 - j_I, np.sqrt(d_I / c_I) * abs_x[None, :])

    cd_A = c_A / d_A
    t1_A = (2**(1 - j_A) * a_A * cd_A**(-0.25 - j_A / 2) * d_A**(-j_A)) / gamma(j_A)
    reA12B = -2 * t1_A * (abs_x[None, :]**(-0.5 + j_A)) * kv(0.5 - j_A, abs_x[None, :] / np.sqrt(cd_A))

    denom = re - im                  # raw (re - im), matches reference convention
    f1Tperp = reA12B
    siv = mt * f1Tperp / denom       # <k_y>_TU

    return {'siv': siv}


def eval_siv_over_b2(p_dict, x_val, b2_grid, massterm):
    """Evaluate the Sivers shift at a single x for a grid of b^2, stacking into (N_JK, N_b)."""
    x_arr = np.array([x_val])
    out = []
    for b2 in b2_grid:
        res = eval_obs_jk(p_dict, x_arr, b2, massterm)
        out.append(res['siv'][:, 0])
    return np.stack(out, axis=1)  # (N_JK, N_b)


# ---------------------------------------------------------------------------
# Figure A: ratio vs x at fixed |b_T|, one 2x2 subplot per P_L
# ---------------------------------------------------------------------------
def make_figure_ratio_vs_x(pl_params, massterm):
    x_grid = np.linspace(0.001, 1.0, 400)
    b2_ref = 9.0                          # |b_T| ~ 0.34 fm
    b2_fan = [16.0, 25.0, 36.0, 49.0]     # |b_T| ~ 0.46, 0.57, 0.68, 0.80 fm
    bT_ref_fm = np.round(np.sqrt(b2_ref) * lata, 2)

    fig, axes = plt.subplots(2, 2, figsize=(14, 10), sharex=True)
    colors_fan = plt.cm.viridis(np.linspace(0.15, 0.9, len(b2_fan)))

    for ax, pl in zip(axes.flatten(), PL_LIST):
        p_dict = pl_params[pl]
        obs_ref = eval_obs_jk(p_dict, x_grid, b2_ref, massterm)['siv']

        for c, b2_i in zip(colors_fan, b2_fan):
            bT_i_fm = np.round(np.sqrt(b2_i) * lata, 2)
            obs_i = eval_obs_jk(p_dict, x_grid, b2_i, massterm)['siv']

            ratio_jk = obs_i / obs_ref
            m, e = jk_stats(ratio_jk, axis=0)

            label = (
                fr"$\langle k_y \rangle_{{TU}}(x,{bT_i_fm}\,{{\rm fm}})\,/\,"
                fr"\langle k_y \rangle_{{TU}}(x,{bT_ref_fm}\,{{\rm fm}})$"
            )
            ax.plot(x_grid, m, color=c, linewidth=2, label=label)
            ax.fill_between(x_grid, m - e, m + e, color=c, alpha=0.25)

        ax.set_title(f"$P_L = {pl}$")
        ax.set_xlabel('$x$')
        ax.set_ylabel(r'$R_b(x)$')
        ax.set_xlim(0, 1)
        ax.grid(True, linestyle='--', alpha=0.5)
        ax.legend(fontsize=7)

    fig.suptitle(
        r'$R_b(x) = \langle k_y \rangle_{TU}(x,|b_T|) \,/\, '
        fr'\langle k_y \rangle_{{TU}}(x,{bT_ref_fm}\,{{\rm fm}})$ at finite $P_L$'
        + '\n(flat $\\Rightarrow$ factorized)',
        fontsize=14, fontweight='bold'
    )
    plt.tight_layout()
    plt.savefig("Factorization_Ratio_vs_x_AllPL_bmin3_eta610.pdf", format='pdf', bbox_inches='tight')
    return fig


# ---------------------------------------------------------------------------
# Figure B: ratio vs |b_T| at fixed x, one 2x2 subplot per P_L
# ---------------------------------------------------------------------------
def make_figure_ratio_vs_bT(pl_params, massterm):
    b2_grid = np.linspace(9.0, 68.0, 120)     # |b_T| in [0.34, 0.94] fm
    bT_grid = np.sqrt(b2_grid) * lata
    x_ref = 0.1
    x_fan = [0.2, 0.4, 0.6, 0.8]

    fig, axes = plt.subplots(2, 2, figsize=(14, 10), sharex=True)
    colors_fan_x = plt.cm.plasma(np.linspace(0.15, 0.85, len(x_fan)))

    for ax, pl in zip(axes.flatten(), PL_LIST):
        p_dict = pl_params[pl]
        obs_ref_b = eval_siv_over_b2(p_dict, x_ref, b2_grid, massterm)

        for c, x_i in zip(colors_fan_x, x_fan):
            obs_i_b = eval_siv_over_b2(p_dict, x_i, b2_grid, massterm)

            ratio_jk_b = obs_i_b / obs_ref_b
            m_b, e_b = jk_stats(ratio_jk_b, axis=0)

            label = (
                fr"$\langle k_y \rangle_{{TU}}({x_i},|b_T|)\,/\,"
                fr"\langle k_y \rangle_{{TU}}({x_ref},|b_T|)$"
            )
            ax.plot(bT_grid, m_b, color=c, linewidth=2, label=label)
            ax.fill_between(bT_grid, m_b - e_b, m_b + e_b, color=c, alpha=0.25)

        ax.set_title(f"$P_L = {pl}$")
        ax.set_xlabel('$|b_T|$ (fm)')
        ax.set_ylabel(r'$R_x(b)$')
        ax.grid(True, linestyle='--', alpha=0.5)
        ax.legend(fontsize=7)

    fig.suptitle(
        r'$R_x(b) = \langle k_y \rangle_{TU}(x,|b_T|) \,/\, '
        fr'\langle k_y \rangle_{{TU}}({x_ref},|b_T|)$ at finite $P_L$'
        + '\n(flat $\\Rightarrow$ factorized)',
        fontsize=14, fontweight='bold'
    )
    plt.tight_layout()
    plt.savefig("Factorization_Ratio_vs_bT_AllPL_bmin3_eta610.pdf", format='pdf', bbox_inches='tight')
    return fig


if __name__ == "__main__":
    massterm = load_massterm()
    pl_params = {pl: load_raw_params_for_pl(pl) for pl in PL_LIST}

    make_figure_ratio_vs_x(pl_params, massterm)
    make_figure_ratio_vs_bT(pl_params, massterm)

    plt.show()
