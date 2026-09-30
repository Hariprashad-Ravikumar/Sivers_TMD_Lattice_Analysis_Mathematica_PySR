import h5py
import numpy as np
import pandas as pd

def scan_data():
    path_base = "/Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/save_h5_A12B_A2B/TMD_fit/h5data"
    
    # Store all (Pb, bsq) pairs
    all_pairs = []
    
    for PL in [-1, -2, -3, -4]:
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
                p = np.round(bL_f[i] * PL, 5)
                b2 = np.round(bL_f[i]**2 + bT_f[i]**2, 5)
                all_pairs.append({'PL': PL, 'P.b': p, 'b^2': b2, 'bL': bL_f[i], 'bT': bT_f[i]})
        except Exception as e:
            pass

    df = pd.DataFrame(all_pairs)
    df = df.drop_duplicates(subset=['PL', 'P.b', 'b^2'])
    
    # We want to find if there are multiple P.b values that share the exact same set of 3 b^2 values.
    # Group by P.b and list the b^2 values available
    grouped = df.groupby('P.b')['b^2'].apply(set).reset_index()
    
    print("Available b^2 values for each P.b (across all PL):")
    for index, row in grouped.iterrows():
        print(f"P.b = {row['P.b']:>5} : {sorted(list(row['b^2']))}")
        
    print("\nIntersection of b^2 for different P.b:")
    
    # Let's find combinations of P.b that have at least 3 common b^2
    common_b2 = {}
    pb_values = grouped['P.b'].values
    for i in range(len(pb_values)):
        for j in range(i+1, len(pb_values)):
            pb1 = pb_values[i]
            pb2 = pb_values[j]
            set1 = grouped[grouped['P.b'] == pb1]['b^2'].iloc[0]
            set2 = grouped[grouped['P.b'] == pb2]['b^2'].iloc[0]
            intersect = set1.intersection(set2)
            if len(intersect) >= 3:
                print(f"P.b = {pb1} and {pb2} share b^2: {sorted(list(intersect))}")

    # Can we find a single set of 3 b^2 that spans >2 P.b values?
    from collections import defaultdict
    b2_to_pbs = defaultdict(list)
    for index, row in df.iterrows():
        b2_to_pbs[row['b^2']].append(row['P.b'])
        
    print("\nP.b values available for each b^2:")
    for b2, pbs in sorted(b2_to_pbs.items()):
        if len(set(pbs)) > 1:
            print(f"b^2 = {b2:>5} : P.b = {sorted(list(set(pbs)))}")

if __name__ == "__main__":
    scan_data()
