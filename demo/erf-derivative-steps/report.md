# Special Function Proof Agent

D_x(erf(x)) = ((2/sqrt(pi))*exp((-(x^2))))

条件：x is real

完全Lean証明：proved
数値診断：no_mismatch_found

構造化ステップ（各等式を元の全条件で検査）：
1. D_x(erf(x)) = ((2/sqrt(pi))*exp((-(x^2))))
   誤差関数のGaussian積分による定義に微積分の基本定理を適用する。
