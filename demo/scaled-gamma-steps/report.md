# Special Function Proof Agent

int(0,infinity,((t^((a-1)))*exp(((-r)*t))),t) = ((r^((-a)))*Gamma(a))

条件：a is real、r is real、a > 0、r > 0

完全Lean証明：proved
数値診断：no_mismatch_found

構造化ステップ（各等式を元の全条件で検査）：
1. int(0,infinity,((t^((a-1)))*exp(((-r)*t))),t) = ((r^((-a)))*Gamma(a))
   正の形状・尺度パラメータに対するGamma積分を適用する。
