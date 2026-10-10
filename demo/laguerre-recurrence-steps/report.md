# Special Function Proof Agent

((n+1)*Laguerre((n+1),a,x)) = ((((((2*n)+a)+1)-x)*Laguerre(n,a,x))-((n+a)*Laguerre((n-1),a,x)))

条件：a is real、n is nat、x is real、n >= 1

完全Lean証明：proved
数値診断：no_mismatch_found

構造化ステップ（各等式を元の全条件で検査）：
1. ((n+1)*Laguerre((n+1),a,x)) = ((((((2*n)+a)+1)-x)*Laguerre(n,a,x))-((n+a)*Laguerre((n-1),a,x)))
   一般化Laguerreの有限和の係数比較から証明した三項漸化式を、自然数次数と実パラメータを保持して適用する。
