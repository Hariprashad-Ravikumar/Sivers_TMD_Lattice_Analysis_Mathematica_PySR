import h5py
import numpy as np

def jackknife_vectorized(samples):
    N = samples.shape[1]
    theta_bar = np.mean(samples, axis=1)
    return theta_bar

path_base = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/TMD_fit/h5data"
PL = -1

for amp in ["ReA2B", "ReA12B"]:
    print(f"\nAmplitude: {amp}")
    with h5py.File(f"{path_base}/{amp}_PL{PL}_jackknife_data.h5", "r") as f:
        raw = f["Dataset1"][:]
    kin = raw[:, 0:3]
    samples = raw[:, 3:]
    eta, bL, bT = kin[:, 0], kin[:, 1], kin[:, 2]
    mask = np.isclose(eta, 8.0)
    bL_f = bL[mask]
    bT_f = bT[mask]
    samples_f = samples[mask]
    
    data_by_pb = {}
    for i in range(len(bL_f)):
        Pb = np.round(-1.0 * PL * bL_f[i], 5)
        if Pb == 0: continue
        bt_val = np.round(bT_f[i], 5)
        if Pb not in data_by_pb: data_by_pb[Pb] = {}
        data_by_pb[Pb][bt_val] = samples_f[i]
        
    for Pb in sorted(data_by_pb.keys()):
        s1 = data_by_pb[Pb].get(1.0)
        s3 = data_by_pb[Pb].get(4.0)
        if s1 is not None and s3 is not None:
            r1 = s1 / s3
            m = np.mean(r1)
            print(f"P.b = {Pb:>4} | A(bT=1)/A(bT=4) = {m:.3f}")
