# Special Function Proof Agent

D_x(Laguerre(n,a,x)) = (-Laguerre((n-1),(a+1),x))

条件：a is real、n is nat、x is real、n >= 1

完全Lean証明：proved
数値診断：no_mismatch_found

構造化ステップ（各等式を元の全条件で検査）：
1. D_x(Laguerre(n,a,x)) = (-Laguerre((n-1),(a+1),x))
   一般化Laguerreの有限和を微分し、次数を1下げてパラメータを1上げる公式を適用する。
