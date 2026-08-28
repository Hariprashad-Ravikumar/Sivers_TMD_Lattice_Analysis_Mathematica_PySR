Print["Integrate from -Infinity to Infinity:"];
Print[Integrate[Exp[-c Abs[\[Lambda]]] * Exp[I * x * \[Lambda]], {\[Lambda], -Infinity, Infinity}, Assumptions -> c > 0]];

Print["FourierTransform with {1,1} (which means no 1/Sqrt[2Pi] prefactor):"];
Print[FourierTransform[Exp[-c Abs[\[Lambda]]], \[Lambda], x, FourierParameters -> {1, 1}, Assumptions -> c > 0]];

Print["FourierTransform with {0,1} (what was used before):"];
Print[FourierTransform[Exp[-c Abs[\[Lambda]]], \[Lambda], x, FourierParameters -> {0, 1}, Assumptions -> c > 0]];
