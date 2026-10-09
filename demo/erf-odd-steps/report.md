# Special Function Proof Agent

erf((-x)) = (-erf(x))

条件：x is real

完全Lean証明：proved
数値診断：no_mismatch_found

構造化ステップ（各等式を元の全条件で検査）：
1. erf((-x)) = (-erf(x))
   Gaussianの偶関数性と積分方向の反転から誤差関数の奇関数性を適用する。
