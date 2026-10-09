# Special Function Proof Agent

D_x(Jacobi(n,a,b,x)) = (((((n+a)+b)+1)/2)*Jacobi((n-1),(a+1),(b+1),x))

条件：a is real、b is real、n is nat、x is real、n >= 1

完全Lean証明：proved
数値診断：no_mismatch_found

構造化ステップ（各等式を元の全条件で検査）：
1. D_x(Jacobi(n,a,b,x)) = (((((n+a)+b)+1)/2)*Jacobi((n-1),(a+1),(b+1),x))
   Jacobiの有限和の微分公式により、次数を1下げて両パラメータを1上げる。
