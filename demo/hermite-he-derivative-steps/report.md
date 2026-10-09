# Special Function Proof Agent

D_x(He_{n}(x)) = (n*He_{(n-1)}(x))

条件：n is nat、x is real、n >= 1

完全Lean証明：proved
数値診断：no_mismatch_found

Hermite規約：Hは物理学規約、Heは確率論規約。次数は自然数です。

構造化ステップ（各等式を元の全条件で検査）：
1. D_x(He_{n}(x)) = (n*He_{(n-1)}(x))
   確率論規約Heの多項式の微分公式を、明示した自然数次数の条件で適用する。
