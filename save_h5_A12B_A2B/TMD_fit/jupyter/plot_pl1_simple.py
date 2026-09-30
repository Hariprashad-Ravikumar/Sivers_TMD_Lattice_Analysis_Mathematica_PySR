import h5py
import numpy as np
import matplotlib.pyplot as plt

def jackknife_vectorized(samples):
    N = samples.shape[1]
    theta_bar = np.mean(samples, axis=1)
    squared_diffs = np.square(samples - theta_bar[:, None])
    sigma_sq = ((N - 1) / N) * np.sum(squared_diffs, axis=1)
    return theta_bar, np.sqrt(sigma_sq)

def plot_simple_ratio_PL_minus_1():
    path_base = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/TMD_fit/h5data"
    PL = -1
    
    # We will pick 3 values of b_T that are actually available at multiple P.b for PL=-1
    # For PL=-1, b_T in {1, 2, 4} are available at P.b in {-4, -2, 2, 4}
    bT_1, bT_2, bT_3 = 1.0, 2.0, 4.0
    
    amplitudes = ["ReA2B", "ImA2B", "ReA12B", "ImA12B"]
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))
    fig.suptitle(f"Factorization Ratio Test at PL = {PL}", fontsize=16, fontweight='bold')
    
    for idx, amp in enumerate(amplitudes):
        ax = axes.flatten()[idx]
        file_path = f"{path_base}/{amp}_PL{PL}_jackknife_data.h5"
        try:
            with h5py.File(file_path, "r") as f:
                raw_data = f["Dataset1"][:]
        except Exception:
            continue
            
        kin = raw_data[:, 0:3]
        samples = raw_data[:, 3:]
        eta, bL, bT = kin[:, 0], kin[:, 1], kin[:, 2]
        
        mask = np.isclose(eta, 8.0)
        bL_f = bL[mask]
        bT_f = bT[mask]
        samples_f = samples[mask]
        
        # Organize by P.b
        data_by_pb = {}
        for i in range(len(bL_f)):
            Pb = np.round(-1.0 * PL * bL_f[i], 5)
            # EXCLUDE P.b = 0 since Sivers is trivially zero and it ruins the ratio plot
            if np.isclose(Pb, 0.0):
                continue
                
            bt_val = np.round(bT_f[i], 5)
            if Pb not in data_by_pb:
                data_by_pb[Pb] = {}
            data_by_pb[Pb][bt_val] = samples_f[i]
            
        all_Pb = sorted(list(data_by_pb.keys()))
        
        ratio_13_mean, ratio_13_err, valid_pb_13 = [], [], []
        ratio_23_mean, ratio_23_err, valid_pb_23 = [], [], []
        
        for Pb in all_Pb:
            s1 = data_by_pb[Pb].get(bT_1)
            s2 = data_by_pb[Pb].get(bT_2)
            s3 = data_by_pb[Pb].get(bT_3)
            
            if s3 is not None:
                if s1 is not None:
                    r1 = s1 / s3
                    m, e = jackknife_vectorized(r1.reshape(1, -1))
                    ratio_13_mean.append(m[0])
                    ratio_13_err.append(e[0])
                    valid_pb_13.append(Pb)
                if s2 is not None:
                    r2 = s2 / s3
                    m, e = jackknife_vectorized(r2.reshape(1, -1))
                    ratio_23_mean.append(m[0])
                    ratio_23_err.append(e[0])
                    valid_pb_23.append(Pb)
                    
        ax.errorbar(valid_pb_13, ratio_13_mean, yerr=ratio_13_err, fmt='o-', label=f'bT={bT_1} / bT={bT_3}')
        ax.errorbar(valid_pb_23, ratio_23_mean, yerr=ratio_23_err, fmt='s--', label=f'bT={bT_2} / bT={bT_3}')
        ax.set_title(amp)
        ax.set_xlabel('P.b')
        ax.set_ylabel('Ratio')
        ax.grid(True)
        ax.legend()
        
    plt.tight_layout()
    plt.savefig("Factorization_RatioTest_PL_minus_1.pdf")
    print("Saved Factorization_RatioTest_PL_minus_1.pdf")

if __name__ == "__main__":
    plot_simple_ratio_PL_minus_1()
