"""One plotting style for every figure of the Sivers paper (PRD, two-column revtex4-2).
Every panel is exactly 3.4 x 2.55 in with the same axes rectangle; text is 8-9 pt (Computer-Modern-like STIX), colours are the Okabe-Ito set.
Use  fig, ax = new_panel()  ... save(fig, name)."""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

W, H = 3.4, 2.55                    # inches, one column
AX_RECT = [0.185, 0.175, 0.785, 0.70]   # fixed axes rectangle (fractions of the figure): identical in every panel
OKABE = dict(blue="#0072B2", vermillion="#D55E00", green="#009E73", pink="#CC79A7", orange="#E69F00", sky="#56B4E9", yellow="#F0E442", black="#000000")
CYCLE = [OKABE[k] for k in ("blue", "vermillion", "green", "pink", "orange", "sky", "black")]
# one colour per physical quantity, used in every figure
QCOL = dict(ReA2B=OKABE["blue"], ImA2B=OKABE["vermillion"], f1=OKABE["green"], f1T=OKABE["pink"], ky=OKABE["orange"], xky=OKABE["sky"], ReA12B=OKABE["pink"])
# one colour per momentum, used wherever curves for P_L=-1..-4 are compared
PLCOL = {1: OKABE["blue"], 2: OKABE["vermillion"], 3: OKABE["green"], 4: OKABE["orange"]}


def apply():
    plt.rcParams.update({
        "font.family": "serif", "font.serif": ["STIXGeneral", "DejaVu Serif"], "mathtext.fontset": "stix",
        "font.size": 8, "axes.labelsize": 9, "axes.titlesize": 9, "xtick.labelsize": 8, "ytick.labelsize": 8, "legend.fontsize": 8,
        "axes.linewidth": 0.8, "lines.linewidth": 1.5, "lines.markersize": 4, "errorbar.capsize": 2,
        "xtick.direction": "in", "ytick.direction": "in", "xtick.top": True, "ytick.right": True,
        "xtick.major.size": 3.5, "ytick.major.size": 3.5, "xtick.minor.size": 2, "ytick.minor.size": 2,
        "axes.grid": False, "legend.frameon": False, "axes.prop_cycle": plt.cycler(color=CYCLE),
        "pdf.fonttype": 42, "ps.fonttype": 42, "savefig.dpi": 300,
    })


def new_panel(label=None):
    apply()
    fig = plt.figure(figsize=(W, H))
    ax = fig.add_axes(AX_RECT)
    if label:
        tag(fig, label)
    return fig, ax


def tag(fig, label):
    """panel tag: bold 9 pt, top-left corner of the figure, above the axes (identical in every panel, 2D and 3D)"""
    fig.text(0.015, 0.975, label, va="top", ha="left", fontsize=9, fontweight="bold")


def save(fig, path):
    fig.savefig(path)          # no bbox_inches='tight': every panel keeps the identical page size
    plt.close(fig)
