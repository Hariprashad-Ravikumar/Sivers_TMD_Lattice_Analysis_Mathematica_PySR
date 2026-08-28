Print["Gaussian FT Re:"];
Print[FourierTransform[Exp[-c * \[Lambda]^2], \[Lambda], x, FourierParameters -> {0,1}, Assumptions -> c > 0]];
Print["Gaussian FT Im:"];
Print[FourierTransform[\[Lambda] * Exp[-c * \[Lambda]^2], \[Lambda], x, FourierParameters -> {0,1}, Assumptions -> c > 0]];
