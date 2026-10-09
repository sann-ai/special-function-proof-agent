# Special Function Proof Agent

int(0,1,((t^((a-1)))*((1-t)^((b-1)))),t) = ((Gamma(a)*Gamma(b))/Gamma((a+b)))

条件：a is real、b is real、a > 0、b > 0

完全Lean証明：proved
数値診断：no_mismatch_found

構造化ステップ（各等式を元の全条件で検査）：
1. int(0,1,((t^((a-1)))*((1-t)^((b-1)))),t) = ((Gamma(a)*Gamma(b))/Gamma((a+b)))
   a > 0、b > 0 より、オイラーのベータ積分公式を適用する。
