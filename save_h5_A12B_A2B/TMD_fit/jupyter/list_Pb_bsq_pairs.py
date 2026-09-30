import h5py
import numpy as np
import pathlib

SCRIPT_DIR = pathlib.Path(__file__).parent.resolve()
FILEPATH = SCRIPT_DIR.parent / "h5data" / "ReA2B_PL-1_jackknife_data.h5"
PL = -1
ETA = 8


def main():
    with h5py.File(FILEPATH, "r") as f:
        kin = f["Dataset1"][:, 0:3]

    eta, bL, bT = kin[:, 0], kin[:, 1], kin[:, 2]
    mask = np.isclose(eta, ETA)
    bL_f, bT_f = bL[mask], bT[mask]

    P_dot_b = np.round(bL_f * PL, 5) + 0.0  # normalize -0.0 to 0.0
    b_sq = np.round(bL_f**2 + bT_f**2, 5)

    pairs = sorted(set(zip(P_dot_b.tolist(), b_sq.tolist())), key=lambda p: (p[0], p[1]))

    grouped = {}
    for pb, bsq in pairs:
        grouped.setdefault(pb, []).append(bsq)

    print(f"eta={ETA}, PL={PL}: {len(pairs)} unique (P.b, b^2) pairs\n")
    for pb in sorted(grouped):
        bsq_list = ", ".join(f"{v:g}" for v in grouped[pb])
        print(f"P.b = {pb:g}, b^2 = {bsq_list}")


if __name__ == "__main__":
    main()
