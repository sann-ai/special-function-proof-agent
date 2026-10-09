# Special Function Proof Agent

int(a,b,exp((-(t^2))),t) = ((sqrt(pi)/2)*(erf(b)-erf(a)))

条件：a is real、b is real

完全Lean証明：proved
数値診断：no_mismatch_found

構造化ステップ（各等式を元の全条件で検査）：
1. int(a,b,exp((-(t^2))),t) = ((sqrt(pi)/2)*(erf(b)-erf(a)))
   誤差関数の微分公式と微積分の基本定理から、指定された実端点のGaussian積分を評価する。
