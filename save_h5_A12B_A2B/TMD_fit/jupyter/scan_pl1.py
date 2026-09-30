import h5py
import numpy as np
import pandas as pd

def scan_data():
    path_base = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/TMD_fit/h5data"
    
    all_pairs = []
    PL = -1
    file_path = f"{path_base}/ReA2B_PL{PL}_jackknife_data.h5"
    try:
        with h5py.File(file_path, "r") as f:
            raw_data = f["Dataset1"][:]
        kin = raw_data[:, 0:3]
        eta, bL, bT = kin[:, 0], kin[:, 1], kin[:, 2]
        mask = np.isclose(eta, 8.0)
        bL_f = bL[mask]
        bT_f = bT[mask]
        
        for i in range(len(bL_f)):
            p = np.round(bL_f[i] * PL, 5)  # Let's just use what they literally said: "P.b = PL*bL/-PL"
            # wait, PL*bL / -PL = -bL
            # Let's print out the exact values so we can see.
            p = np.round(-1.0 * bL_f[i], 5)
            b2 = np.round(bL_f[i]**2 + bT_f[i]**2, 5)
            all_pairs.append({'P.b': p, 'b^2': b2, 'bL': bL_f[i], 'bT': bT_f[i]})
    except Exception as e:
        pass

    df = pd.DataFrame(all_pairs)
    df = df.drop_duplicates(subset=['P.b', 'b^2'])
    
    grouped = df.groupby('P.b')['b^2'].apply(set).reset_index()
    
    print(f"Available b^2 values for each P.b at PL={PL}:")
    for index, row in grouped.iterrows():
        print(f"P.b = {row['P.b']:>5} : {sorted(list(row['b^2']))}")

    from collections import defaultdict
    b2_to_pbs = defaultdict(list)
    for index, row in df.iterrows():
        b2_to_pbs[row['b^2']].append(row['P.b'])
        
    print(f"\nP.b values available for each b^2 at PL={PL}:")
    for b2, pbs in sorted(b2_to_pbs.items()):
        if len(set(pbs)) > 1:
            print(f"b^2 = {b2:>5} : P.b = {sorted(list(set(pbs)))}")

if __name__ == "__main__":
    scan_data()
