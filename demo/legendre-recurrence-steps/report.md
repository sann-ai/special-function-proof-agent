# Special Function Proof Agent

((n+1)*P_{(n+1)}(x)) = (((((2*n)+1)*x)*P_{n}(x))-(n*P_{(n-1)}(x)))

条件：n is nat、x is real、n >= 1

完全Lean証明：proved
数値診断：no_mismatch_found

構造化ステップ（各等式を元の全条件で検査）：
1. ((n+1)*P_{(n+1)}(x)) = (((((2*n)+1)*x)*P_{n}(x))-(n*P_{(n-1)}(x)))
   標準Legendreの有限和の係数比較から証明した三項漸化式を、元の自然数次数条件で適用する。
