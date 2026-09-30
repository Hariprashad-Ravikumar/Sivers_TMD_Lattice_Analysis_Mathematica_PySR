import h5py
import numpy as np
import matplotlib.pyplot as plt
from collections import defaultdict

PATH_BASE = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/TMD_fit/h5data"
PL = -1
TARGET_ETA = 8.0

def load_data(amp):
    filepath = f"{PATH_BASE}/{amp}_PL{PL}_jackknife_data.h5"
    with h5py.File(filepath, "r") as f:
        raw_data = f["Dataset1"][:]
    kin = raw_data[:, 0:3]
    samples = raw_data[:, 3:]
    eta, bL, bT = kin[:, 0], kin[:, 1], kin[:, 2]
    mask = np.isclose(eta, TARGET_ETA) & (bL > 0)
    bL_f, bT_f, samples_f = bL[mask], bT[mask], samples[mask]
    
    data = defaultdict(list)
    for i in range(len(bL_f)):
        pb = np.round(-1.0 * float(PL) * bL_f[i], 5)
        b2 = np.round(bL_f[i] ** 2 + bT_f[i] ** 2, 5)
        data[(pb, b2)].append(samples_f[i])
    return {k: np.mean(v, axis=0) for k, v in data.items()}

re_a12b = load_data("ReA12B")
re_a2b = load_data("ReA2B")

print("--- ReA12B ---")
for k, v in sorted(re_a12b.items(), key=lambda x: (x[0][1], x[0][0])):
    pb, b2 = k
    val = np.mean(v)
    err = np.std(v)*np.sqrt(len(v)-1)
    print(f"P.b={pb} b^2={b2}: val={val:.4f}, val/P.b={val/pb:.4f}")

print("--- ReA2B ---")
for k, v in sorted(re_a2b.items(), key=lambda x: (x[0][1], x[0][0])):
    pb, b2 = k
    val = np.mean(v)
    print(f"P.b={pb} b^2={b2}: val={val:.4f}, val/P.b={val/pb:.4f}")
