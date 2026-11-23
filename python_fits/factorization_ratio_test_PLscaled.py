"""
Factorization ratio test: F(P.b, b^2) = G(P.b) * H(b^2)  at fixed eta, PL.

P.b = -PL * bL,  b^2 = bL^2 + bT^2.  Cuts: P.b != 0, |b| >= 3a.
Ratios are formed per jackknife sample, then reduced with jackknife_vectorized.

  R(b^2)  = F(x1, b^2) / F(x2, b^2)   -> flat in b^2 if factorized (= G(x1)/G(x2))
  S(P.b)  = F(P.b, y1) / F(P.b, y2)   -> flat in P.b if factorized (= H(y1)/H(y2))

Missing nodes are filled by linear interpolation in b^2 along fixed-P.b lines
(no extrapolation).
"""
import os
import argparse
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


pl_to_zeta = {
    -4: 0.785756,
    -3: 0.539684,
    -2: 0.294367,
    -1: 0.090772
}

amp_labels = {
    "ReA2B":  r"$\tilde{A}_{2B}^{Re}$",
    "ImA2B":  r"$\tilde{A}_{2B}^{Im}$",
    "ReA12B": r"$\tilde{A}_{12B}^{Re}$",
    "ImA12B": r"$\tilde{A}_{12B}^{Im}$",
}


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


# --- 2. Load (P.b, b^2) -> jackknife samples ---
def load_lines(filepath, eta_val, PL, b2_min=9.0, include_zero=False):
    """Returns {P.b: {b^2: samples}} for P.b > 0 (>= 0 if include_zero), b^2 >= b2_min.
    +-bL rows are (anti)symmetrized copies -> keep P.b > 0 only.
    +-bT rows are independent -> averaged per jackknife sample."""
    with h5py.File(filepath, "r") as f:
        raw = f["Dataset1"][:]
    eta, bL, bT = raw[:, 0], raw[:, 1], raw[:, 2]
    samples = raw[:, 3:]

    P_dot_b = -1.0 * PL * bL
    b_sq = bL**2 + bT**2
    pb_mask = (P_dot_b >= 0) if include_zero else (P_dot_b > 0)
    mask = np.isclose(eta, eta_val) & pb_mask & (b_sq >= b2_min)

    groups = {}
    for pb, b2, s in zip(P_dot_b[mask], b_sq[mask], samples[mask]):
        groups.setdefault((int(round(pb)), int(round(b2))), []).append(s)

    lines = {}
    for (pb, b2), rows in groups.items():
        lines.setdefault(pb, {})[b2] = np.mean(rows, axis=0)
    return lines


def value_at(lines, pb, b2):
    """Samples of F(pb, b2): data if present, else linear interp in b^2 along
    the fixed-P.b line. Returns (samples, is_interpolated)."""
    line = lines[pb]
    if b2 in line:
        return line[b2], False
    nodes = np.array(sorted(line))
    if len(nodes) < 2 or b2 < nodes[0] or b2 > nodes[-1]:
        raise ValueError(f"b^2={b2} outside P.b={pb} line {list(nodes)}: no extrapolation")
    hi = np.searchsorted(nodes, b2)
    y0, y1 = nodes[hi - 1], nodes[hi]
    w = (b2 - y0) / (y1 - y0)
    return (1 - w) * line[y0] + w * line[y1], True


def ratio(num, den):
    mean, err = jackknife_vectorized(np.vstack([num / den]))
    _, den_err = jackknife_vectorized(np.vstack([den]))
    den_snr = abs(np.mean(den)) / den_err[0]
    return mean[0], err[0], den_snr


# --- 3. Build ratios ---
def build_ratios(lines, R_pair, R_nodes, S_pair, S_nodes):
    x1, x2 = R_pair
    R = []
    for b2 in R_nodes:
        n, in1 = value_at(lines, x1, b2)
        d, in2 = value_at(lines, x2, b2)
        m, e, snr = ratio(n, d)
        R.append(dict(x=b2, mean=m, err=e, interp=in1 or in2, den_snr=snr))

    y1, y2 = S_pair
    S = []
    for pb in S_nodes:
        n, in1 = value_at(lines, pb, y1)
        d, in2 = value_at(lines, pb, y2)
        m, e, snr = ratio(n, d)
        S.append(dict(x=pb, mean=m, err=e, interp=in1 or in2, den_snr=snr))
    return R, S


# --- 4. Plot ---
def draw(ax, pts, color, xlabel, ylabel, title):
    for p in pts:
        ax.errorbar(p['x'], p['mean'], yerr=p['err'], fmt='o', ms=8, capsize=4,
                    color=color, mfc=color, mec=color)
        if p['den_snr'] < 2:
            ax.annotate('low S/N denom.', (p['x'], p['mean']), textcoords='offset points',
                        xytext=(5, 8), fontsize=8, color='gray')
    ax.set_xticks([p['x'] for p in pts])
    ax.set_xlabel(xlabel, fontsize=12)
    ax.set_ylabel(ylabel, fontsize=12)
    ax.set_title(title, fontsize=12)
    ax.grid(True, linestyle='--', alpha=0.5)


def plot_ratios(results, PL, eta_val, R_pair, S_pair):
    fig, axes = plt.subplots(2, len(results), figsize=(6 * len(results), 10), squeeze=False,
                             layout='constrained')
    fig.suptitle(fr'Factorization ratios: $P_L={PL}$, $\eta|v|/a={eta_val:g}$, '
                 fr'$\hat{{\zeta}}={pl_to_zeta[int(PL)]}$'
                 '\n(uses linear interpolation in $b^2$)',
                 fontsize=15, fontweight='bold')
    x1, x2 = R_pair
    y1, y2 = S_pair
    for col, (amp, (R, S)) in enumerate(results.items()):
        lab = amp_labels[amp]
        draw(axes[0, col], R, '#4363d8', r'$b^2/a^2$',
             fr'{lab}$(P\cdot b={x1})$ / {lab}$(P\cdot b={x2})$',
             fr'{lab}: ratio vs $b^2$')
        draw(axes[1, col], S, '#e6194b', r'$P\cdot b$',
             fr'{lab}$(b^2={y1})$ / {lab}$(b^2={y2})$',
             fr'{lab}: ratio vs $P\cdot b$')
        axes[1, col].set_xlim(min(p['x'] for p in S) - 1, max(p['x'] for p in S) + 1)
    return fig


# --- 5. Common-b^2-grid test over several P.b lines ---
def quad_stencil(nodes, b2):
    """The three data b^2 nearest to b2 (ties go to the smaller b^2), sorted."""
    nodes = sorted(nodes)
    return sorted(sorted(nodes, key=lambda y: (abs(y - b2), y))[:3])


def value_at_quadratic(lines, pb, b2):
    """Samples of F(pb, b2) from the parabola in b^2 through the three nearest
    data points on the fixed-P.b line (per jackknife sample, no extrapolation)."""
    line = lines[pb]
    if b2 in line:
        return line[b2]
    nodes = sorted(line)
    if len(nodes) < 3 or b2 < nodes[0] or b2 > nodes[-1]:
        raise ValueError(f"b^2={b2}: P.b={pb} line {nodes} needs >= 3 points and no extrapolation")
    st = quad_stencil(nodes, b2)
    out = 0.0
    for i, yi in enumerate(st):
        w = np.prod([(b2 - yj) / (yi - yj) for j, yj in enumerate(st) if j != i])
        out = out + w * line[yi]
    return out


def grid_value(lines, pb, b2, method='lin'):
    return value_at_quadratic(lines, pb, b2) if method == 'quad' else value_at(lines, pb, b2)[0]


def grid_ratios(lines, pbs, b2_nodes, pb_ref, b2_ref, methods=None):
    """Top:    F(x, b^2) / F(pb_ref, b^2) vs b^2, one curve per x in pbs (x != pb_ref).
    Bottom: F(P.b, y) / F(P.b, b2_ref) vs P.b, one curve per y in b2_nodes (y != b2_ref).
    methods: {P.b: 'lin' | 'quad'} interpolation per line (default linear)."""
    methods = methods or {}
    grid = {(pb, b2): grid_value(lines, pb, b2, methods.get(pb, 'lin'))
            for pb in pbs for b2 in b2_nodes}
    top, bottom = {}, {}
    for x in pbs:
        if x == pb_ref:
            continue
        pts = []
        for b2 in b2_nodes:
            m, e, snr = ratio(grid[(x, b2)], grid[(pb_ref, b2)])
            pts.append(dict(x=b2, mean=m, err=e, den_snr=snr))
        top[x] = pts
    for y in b2_nodes:
        if y == b2_ref:
            continue
        pts = []
        for pb in pbs:
            m, e, snr = ratio(grid[(pb, y)], grid[(pb, b2_ref)])
            pts.append(dict(x=pb, mean=m, err=e, den_snr=snr))
        bottom[y] = pts
    return top, bottom


def draw_curves(ax, curves, colors, label_fmt, xlabel, ylabel, title, dx, annotate=True):
    offsets = (np.arange(len(curves)) - (len(curves) - 1) / 2) * dx
    for (key, pts), col, off in zip(curves.items(), colors, offsets):
        xs = np.array([p['x'] for p in pts]) + off
        ax.errorbar(xs, [p['mean'] for p in pts], yerr=[p['err'] for p in pts],
                    fmt='o', ms=7, capsize=4, color=col, label=label_fmt.format(key))
        for xv, p in zip(xs, pts):
            if annotate and p['den_snr'] < 2:
                ax.annotate('low S/N denom.', (xv, p['mean']), textcoords='offset points',
                            xytext=(5, 8), fontsize=8, color='gray')
    ax.set_xticks([p['x'] for p in next(iter(curves.values()))])
    ax.set_xlabel(xlabel, fontsize=12)
    ax.set_ylabel(ylabel, fontsize=12)
    ax.set_title(title, fontsize=12)
    ax.grid(True, linestyle='--', alpha=0.5)
    ax.legend(fontsize=10)


def plot_grid_ratios(results, PL, eta_val, interp_note='(uses linear interpolation in $b^2$)',
                     annotate=True):
    """results[amp] = (top, bottom, pb_ref, b2_ref)."""
    fig, axes = plt.subplots(2, len(results), figsize=(6 * len(results), 10), squeeze=False,
                             layout='constrained')
    fig.suptitle(fr'Factorization ratios: $P_L={PL}$, $\eta|v|/a={eta_val:g}$, '
                 fr'$\hat{{\zeta}}={pl_to_zeta[int(PL)]}$'
                 '\n' + interp_note,
                 fontsize=15, fontweight='bold')
    curve_colors = ['#4363d8', '#3cb44b', '#e6194b', '#911eb4']
    for col, (amp, (top, bottom, pb_ref, b2_ref)) in enumerate(results.items()):
        lab = amp_labels[amp]
        draw_curves(axes[0, col], top, curve_colors[:len(top)],
                    r'$P\cdot b={}$', r'$b^2/a^2$',
                    fr'{lab}$(P\cdot b,\,b^2)$ / {lab}$(P\cdot b={pb_ref},\,b^2)$',
                    fr'{lab}: ratio vs $b^2$', dx=0.0, annotate=annotate)
        draw_curves(axes[1, col], bottom, curve_colors[:len(bottom)],
                    r'$b^2={}$', r'$P\cdot b$',
                    fr'{lab}$(P\cdot b,\,b^2)$ / {lab}$(P\cdot b,\,b^2={b2_ref})$',
                    fr'{lab}: ratio vs $P\cdot b$', dx=0.0, annotate=annotate)
    return fig


# --- 6. Matched test: interpolate only the dense P.b=0 line, at the sparse line's data b^2 ---
# Linear interpolation commutes with a P.b-only factor: interp[G(x) H] = G(x) interp[H].
# Evaluating the sparse line only at its own data b^2 and interpolating the dense line
# over short gaps keeps the interpolation bias small; the log|F|-vs-log b^2 variant
# gives the systematic.
def value_at_loglog(lines, pb, b2):
    """Samples of F(pb, b2) with log|F| linear in log b^2 (same brackets as value_at)."""
    line = lines[pb]
    if b2 in line:
        return line[b2]
    nodes = np.array(sorted(line))
    if len(nodes) < 2 or b2 < nodes[0] or b2 > nodes[-1]:
        raise ValueError(f"b^2={b2} outside P.b={pb} line {list(nodes)}: no extrapolation")
    hi = np.searchsorted(nodes, b2)
    y0, y1 = nodes[hi - 1], nodes[hi]
    f0, f1 = line[y0], line[y1]
    if np.any(np.sign(f0) != np.sign(f0[0])) or np.any(np.sign(f1) != np.sign(f0[0])):
        raise ValueError(f"sign change in P.b={pb} samples between b^2={y0},{y1}: log interp undefined")
    w = np.log(b2 / y0) / np.log(y1 / y0)
    return np.sign(f0[0]) * np.exp((1 - w) * np.log(np.abs(f0)) + w * np.log(np.abs(f1)))


def matched_point(num_lin, num_log, den_lin, den_log):
    """Ratio with stat (jackknife) error and sys = |lin - loglog| of the means."""
    m, e, snr = ratio(num_lin, den_lin)
    m_log, _, _ = ratio(num_log, den_log)
    sys = abs(m - m_log)
    return dict(mean=m, err=e, sys=sys, tot=np.hypot(e, sys), den_snr=snr)


def matched_ratios(lines, probes, dense=0):
    """Top:    F(dense, y) / F(x, y) at the data b^2 of each probe line x.
    Bottom: F(P.b, y1) / F(P.b, y2) for P.b in {dense, x}, (y1, y2) consecutive data b^2 of x."""
    def dense_at(y):
        return value_at(lines, dense, y)[0], value_at_loglog(lines, dense, y)

    top, bottom = {}, {}
    for x in probes:
        ys = sorted(lines[x])
        pts = []
        for y in ys:
            d_lin, d_log = dense_at(y)
            pts.append(dict(x=y, **matched_point(d_lin, d_log, lines[x][y], lines[x][y])))
        top[x] = pts
        for y1, y2 in zip(ys[:-1], ys[1:]):
            (a_lin, a_log), (b_lin, b_log) = dense_at(y1), dense_at(y2)
            bottom[(y1, y2)] = [
                dict(x=dense, **matched_point(a_lin, a_log, b_lin, b_log)),
                dict(x=x, **matched_point(lines[x][y1], lines[x][y1], lines[x][y2], lines[x][y2])),
            ]
    return top, bottom


def draw_matched(ax, curves, colors, label_fmt, xlabel, ylabel, title, dx):
    offsets = (np.arange(len(curves)) - (len(curves) - 1) / 2) * dx
    xticks = set()
    for (key, pts), col, off in zip(curves.items(), colors, offsets):
        xs = np.array([p['x'] for p in pts]) + off
        xticks.update(p['x'] for p in pts)
        means = [p['mean'] for p in pts]
        ax.errorbar(xs, means, yerr=[p['tot'] for p in pts], fmt='none', capsize=0,
                    elinewidth=6, ecolor=col, alpha=0.25)
        ax.errorbar(xs, means, yerr=[p['err'] for p in pts], fmt='o', ms=7, capsize=4,
                    color=col, label=label_fmt(key))
    ax.set_xticks(sorted(xticks))
    ax.tick_params(axis='x', labelsize=8)
    ax.set_xlabel(xlabel, fontsize=12)
    ax.set_ylabel(ylabel, fontsize=12)
    ax.set_title(title, fontsize=12)
    ax.grid(True, linestyle='--', alpha=0.5)
    ax.legend(fontsize=10)


def plot_matched(results, PL, eta_val, dense=0):
    fig, axes = plt.subplots(2, len(results), figsize=(6 * len(results), 10), squeeze=False,
                             layout='constrained')
    fig.suptitle(fr'Factorization ratios: $P_L={PL}$, $\eta|v|/a={eta_val:g}$, '
                 fr'$\hat{{\zeta}}={pl_to_zeta[int(PL)]}$'
                 f'\n(uses linear interpolation in $b^2$ of the $P\\cdot b={dense}$ line only; '
                 r'outer error bar: stat $\oplus$ sys from $\log|F|$ vs $\log b^2$)',
                 fontsize=14, fontweight='bold')
    colors = ['#4363d8', '#3cb44b', '#e6194b', '#911eb4']
    for col, (amp, (top, bottom)) in enumerate(results.items()):
        lab = amp_labels[amp]
        draw_matched(axes[0, col], top, colors, lambda x: fr'$P\cdot b={x}$', r'$b^2/a^2$',
                     fr'{lab}$(P\cdot b={dense},\,b^2)$ / {lab}$(P\cdot b,\,b^2)$',
                     fr'{lab}: ratio vs $b^2$', dx=0.4)
        draw_matched(axes[1, col], bottom, colors,
                     lambda k: fr'$b^2={k[0]}\,/\,{k[1]}$', r'$P\cdot b$',
                     fr'{lab}$(P\cdot b,\,b_1^2)$ / {lab}$(P\cdot b,\,b_2^2)$',
                     fr'{lab}: ratio vs $P\cdot b$', dx=0.12)
    return fig


# --- 7. Linear vs quadratic on one figure: circles = linear, open triangles = quadratic ---
def same_point(p, q):
    return np.isclose(p['mean'], q['mean'], rtol=1e-12) and np.isclose(p['err'], q['err'], rtol=1e-12)


def draw_lin_quad(ax, lin_curves, quad_curves, colors, label_fmt, xlabel, ylabel, title):
    for (key, lin_pts), col in zip(lin_curves.items(), colors):
        quad_pts = quad_curves[key]
        ax.errorbar([p['x'] for p in lin_pts], [p['mean'] for p in lin_pts],
                    yerr=[p['err'] for p in lin_pts], fmt='o', ms=7, capsize=4,
                    color=col, label=label_fmt(key))
        diff = [q for p, q in zip(lin_pts, quad_pts) if not same_point(p, q)]
        if diff:
            ax.errorbar([q['x'] for q in diff], [q['mean'] for q in diff],
                        yerr=[q['err'] for q in diff], fmt='^', ms=9, capsize=4,
                        color=col, mfc='white', mec=col, mew=1.5)
    ax.set_xticks([p['x'] for p in next(iter(lin_curves.values()))])
    ax.set_xlabel(xlabel, fontsize=12)
    ax.set_ylabel(ylabel, fontsize=12)
    ax.set_title(title, fontsize=12)
    ax.grid(True, linestyle='--', alpha=0.5)
    handles, labels = ax.get_legend_handles_labels()
    handles += [plt.Line2D([], [], ls='none', marker='o', color='k', ms=7),
                plt.Line2D([], [], ls='none', marker='^', color='k', mfc='white', ms=9, mew=1.5)]
    labels += ['linear', 'quadratic']
    ax.legend(handles, labels, fontsize=9)


def plot_lin_vs_quad(lin_results, quad_results, PL, eta_val):
    fig, axes = plt.subplots(2, len(lin_results), figsize=(6 * len(lin_results), 10), squeeze=False,
                             layout='constrained')
    fig.suptitle(fr'Factorization ratios: $P_L={PL}$, $\eta|v|/a={eta_val:g}$, '
                 fr'$\hat{{\zeta}}={pl_to_zeta[int(PL)]}$'
                 '\n' r'(circles: linear interpolation in $b^2$; '
                 r'open triangles: quadratic for $P\cdot b=0, '+str(4*abs(PL))+r'$)',
                 fontsize=15, fontweight='bold')
    colors = ['#4363d8', '#3cb44b', '#e6194b', '#911eb4']
    for col, amp in enumerate(lin_results):
        lt, lb, pb_ref, b2_ref = lin_results[amp]
        qt, qb, _, _ = quad_results[amp]
        lab = amp_labels[amp]
        draw_lin_quad(axes[0, col], lt, qt, colors, lambda x: fr'$P\cdot b={x}$', r'$b^2/a^2$',
                      fr'{lab}$(P\cdot b,\,b^2)$ / {lab}$(P\cdot b={pb_ref},\,b^2)$',
                      fr'{lab}: ratio vs $b^2$')
        draw_lin_quad(axes[1, col], lb, qb, colors, lambda y: fr'$b^2={y}$', r'$P\cdot b$',
                      fr'{lab}$(P\cdot b,\,b^2)$ / {lab}$(P\cdot b,\,b^2={b2_ref})$',
                      fr'{lab}: ratio vs $P\cdot b$')
    return fig


# ==========================================
# Main Execution Block
# ==========================================
if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--path", default=os.path.normpath(
        os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")))
    ap.add_argument("--PL", type=int, default=-1)
    ap.add_argument("--eta", type=float, default=8.0)
    args = ap.parse_args()

    PL, eta_val = args.PL, args.eta
    SC = -PL   # P.b = -PL*bL: all P.b nodes of the PL=-1 script are multiplied by |PL|
    R_pair, R_nodes = (4*SC, 3*SC), [18, 20, 32]   # overlap of P.b=3 {18,45} and P.b=4 {17,20,32}
    S_pairs, S_nodes = [(18, 20), (20, 32)], [3*SC, 4*SC]   # only P.b=3,4 lines span these b^2

    lines_by_amp = {}
    for amp in ["ReA2B", "ImA2B", "ReA12B"]:
        fp = os.path.join(args.path, f"{amp}_PL{PL}_jackknife_data.h5")
        if not os.path.exists(fp):
            print(f"File not found: {fp}")
            continue
        lines_by_amp[amp] = load_lines(fp, eta_val, PL)

    for S_pair in S_pairs:
        results = {}
        print(f"\n===== second row: b^2 = {S_pair[0]} / {S_pair[1]} =====")
        for amp, lines in lines_by_amp.items():
            results[amp] = build_ratios(lines, R_pair, R_nodes, S_pair, S_nodes)
            print(f"\n{amp}  (PL={PL}, eta={eta_val:g})")
            print("  available (P.b: b^2):", {pb: sorted(v) for pb, v in sorted(lines.items())})
            for name, pts in zip(("R vs b^2 ", "S vs P.b "), results[amp]):
                for p in pts:
                    print(f"  {name} x={p['x']:>3}  {p['mean']:+.4f} +- {p['err']:.4f}"
                          f"  {'interp' if p['interp'] else 'data  '}  denom S/N={p['den_snr']:.1f}")

        if results:
            fig = plot_ratios(results, PL, eta_val, R_pair, S_pair)
            save_name = f"Factorization_ratios_b2_{S_pair[0]}_{S_pair[1]}_eta{eta_val:g}_PL{PL}.pdf"
            fig.savefig(save_name, format='pdf', dpi=300, bbox_inches='tight')
            print(f"\nSaved: {save_name}")

    # ---- P.b = 0, 3, 4 on a common b^2 grid (interpolation only) ----
    # ImA2B is odd in P.b (identically 0 at P.b=0) -> P.b = 3, 4 only
    grid_nodes, b2_ref = [18, 20, 25, 32], 18
    grid_pbs = {"ReA2B": [0, 3*SC, 4*SC], "ImA2B": [3*SC, 4*SC], "ReA12B": [0, 3*SC, 4*SC]}

    print("\n===== common b^2 grid", grid_nodes, "=====")
    grid_results = {}
    for amp, pbs in grid_pbs.items():
        fp = os.path.join(args.path, f"{amp}_PL{PL}_jackknife_data.h5")
        if not os.path.exists(fp):
            continue
        lines = load_lines(fp, eta_val, PL, include_zero=(0 in pbs))
        pb_ref = 4*SC   # reference line: most data points, least interpolation
        top, bottom = grid_ratios(lines, pbs, grid_nodes, pb_ref, b2_ref)
        grid_results[amp] = (top, bottom, pb_ref, b2_ref)

        print(f"\n{amp}  (PL={PL}, eta={eta_val:g})")
        for x, pts in top.items():
            print(f"  F(P.b={x}, b^2)/F(P.b={pb_ref}, b^2): " +
                  "  ".join(f"b2={p['x']}: {p['mean']:+.4f}({p['err']:.4f})" for p in pts))
        for y, pts in bottom.items():
            print(f"  F(P.b, b^2={y})/F(P.b, b^2={b2_ref}): " +
                  "  ".join(f"P.b={p['x']}: {p['mean']:+.4f}({p['err']:.4f})" for p in pts))

    if grid_results:
        fig = plot_grid_ratios(grid_results, PL, eta_val)
        save_name = f"Factorization_ratios_Pb034_eta{eta_val:g}_PL{PL}.pdf"
        fig.savefig(save_name, format='pdf', dpi=300, bbox_inches='tight')
        print(f"\nSaved: {save_name}")

    # ---- Matched test: P.b=0 line interpolated at the data b^2 of P.b=3, 4 ----
    # ImA2B excluded: identically 0 at P.b=0, and P.b=3,4 share no data b^2
    print("\n===== matched test (P.b=0 interpolated at P.b=3,4 data b^2) =====")
    matched_results = {}
    for amp in ["ReA2B", "ReA12B"]:
        fp = os.path.join(args.path, f"{amp}_PL{PL}_jackknife_data.h5")
        if not os.path.exists(fp):
            continue
        lines = load_lines(fp, eta_val, PL, include_zero=True)
        top, bottom = matched_ratios(lines, probes=[3*SC, 4*SC])
        matched_results[amp] = (top, bottom)

        print(f"\n{amp}  (PL={PL}, eta={eta_val:g})   mean(stat)(sys)")
        for x, pts in top.items():
            print(f"  F(P.b=0, b^2)/F(P.b={x}, b^2): " +
                  "  ".join(f"b2={p['x']}: {p['mean']:+.4f}({p['err']:.4f})({p['sys']:.4f})" for p in pts))
        for (y1, y2), pts in bottom.items():
            print(f"  F(P.b, {y1})/F(P.b, {y2}): " +
                  "  ".join(f"P.b={p['x']}: {p['mean']:+.4f}({p['err']:.4f})({p['sys']:.4f})" for p in pts))

    if matched_results:
        fig = plot_matched(matched_results, PL, eta_val)
        save_name = f"Factorization_ratios_matched_eta{eta_val:g}_PL{PL}.pdf"
        fig.savefig(save_name, format='pdf', dpi=300, bbox_inches='tight')
        print(f"\nSaved: {save_name}")

    # ---- Same grid, quadratic interpolation on P.b=0, 4; linear on P.b=3 (2 points only) ----
    quad_methods = {0: 'quad', 3*SC: 'lin', 4*SC: 'quad'}
    print("\n===== common b^2 grid, quadratic for P.b=0,4 / linear for P.b=3 =====")
    quad_results = {}
    for amp, pbs in grid_pbs.items():
        fp = os.path.join(args.path, f"{amp}_PL{PL}_jackknife_data.h5")
        if not os.path.exists(fp):
            continue
        lines = load_lines(fp, eta_val, PL, include_zero=(0 in pbs))
        pb_ref = 4*SC
        top, bottom = grid_ratios(lines, pbs, grid_nodes, pb_ref, b2_ref, methods=quad_methods)
        quad_results[amp] = (top, bottom, pb_ref, b2_ref)

        print(f"\n{amp}  (PL={PL}, eta={eta_val:g})")
        for pb in pbs:
            src = []
            for y in grid_nodes:
                if y in lines[pb]:
                    src.append(f"{y}:data")
                elif quad_methods[pb] == 'quad':
                    src.append(f"{y}:quad{tuple(quad_stencil(lines[pb], y))}")
                else:
                    src.append(f"{y}:lin")
            print(f"  P.b={pb} nodes {sorted(lines[pb])}: " + "  ".join(src))
        for x, pts in top.items():
            print(f"  F(P.b={x}, b^2)/F(P.b={pb_ref}, b^2): " +
                  "  ".join(f"b2={p['x']}: {p['mean']:+.4f}({p['err']:.4f})" for p in pts))
        for y, pts in bottom.items():
            print(f"  F(P.b, b^2={y})/F(P.b, b^2={b2_ref}): " +
                  "  ".join(f"P.b={p['x']}: {p['mean']:+.4f}({p['err']:.4f})" for p in pts))

    if quad_results:
        fig = plot_grid_ratios(quad_results, PL, eta_val,
                               interp_note=r'(quadratic interpolation in $b^2$ for $P\cdot b=0, '+str(4*SC)+r'$; '
                                           r'linear for $P\cdot b='+str(3*SC)+r'$)', annotate=False)
        save_name = f"Factorization_ratios_Pb034_quadratic_eta{eta_val:g}_PL{PL}.pdf"
        fig.savefig(save_name, format='pdf', dpi=300, bbox_inches='tight')
        print(f"\nSaved: {save_name}")

    # ---- Linear (circles) and quadratic (open triangles) on one figure ----
    if grid_results and quad_results:
        print("\n===== lin vs quad: points where quadratic differs =====")
        for amp in grid_results:
            for row, idx in (("top", 0), ("bottom", 1)):
                for key, lin_pts in grid_results[amp][idx].items():
                    for p, q in zip(lin_pts, quad_results[amp][idx][key]):
                        tag = "same" if same_point(p, q) else "DIFF"
                        print(f"  {amp:6s} {row:6s} curve={key} x={p['x']}: lin {p['mean']:.4f}({p['err']:.4f})"
                              f"  quad {q['mean']:.4f}({q['err']:.4f})  {tag}")
        fig = plot_lin_vs_quad(grid_results, quad_results, PL, eta_val)
        save_name = f"Factorization_ratios_Pb034_lin_vs_quad_eta{eta_val:g}_PL{PL}.pdf"
        fig.savefig(save_name, format='pdf', dpi=300, bbox_inches='tight')
        print(f"\nSaved: {save_name}")
