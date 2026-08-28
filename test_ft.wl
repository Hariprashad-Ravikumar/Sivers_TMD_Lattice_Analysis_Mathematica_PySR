Print["FT of Exp[-c |\[Lambda]|] :"];
Print[FourierTransform[Exp[-c Abs[\[Lambda]]], \[Lambda], x, FourierParameters -> {0, 1}, Assumptions -> c > 0]];

Print["FT of \[Lambda] Exp[-c |\[Lambda]|] :"];
Print[FourierTransform[\[Lambda] Exp[-c Abs[\[Lambda]]], \[Lambda], x, FourierParameters -> {0, 1}, Assumptions -> c > 0]];
