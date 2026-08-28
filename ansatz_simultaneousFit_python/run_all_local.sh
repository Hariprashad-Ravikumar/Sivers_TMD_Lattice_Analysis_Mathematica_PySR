#!/bin/bash
echo "Starting production runs for all 4 Ansatzes (PL = -1, -2, -3, -4) on local Mac..."

cd /Users/hariprashadravikumar/Lattice_QCD_TMD_PhD/sivers_TMD_PhD_project/ansatz_simultaneousFit_python/

echo "1/4: Running ExpPb_Expb..."
cd ExpPb_Expb
/opt/homebrew/anaconda3/bin/python simultaneous_fit_ExpPb_Expb.py > run_ExpPb_Expb.log 2>&1
cd ..

echo "2/4: Running ExpPb_PowerLawb..."
cd ExpPb_PowerLawb
/opt/homebrew/anaconda3/bin/python simultaneous_fit_ExpPb_PowerLawb.py > run_ExpPb_PowerLawb.log 2>&1
cd ..

echo "3/4: Running GaussianPb_Expb..."
cd GaussianPb_Expb
/opt/homebrew/anaconda3/bin/python simultaneous_fit_GaussianPb_Expb.py > run_GaussianPb_Expb.log 2>&1
cd ..

echo "4/4: Running GaussianPb_PowerLawb..."
cd GaussianPb_PowerLawb
/opt/homebrew/anaconda3/bin/python simultaneous_fit_GaussianPb_PowerLawb.py > run_GaussianPb_PowerLawb.log 2>&1
cd ..

echo "All 4 production runs completed successfully!"
