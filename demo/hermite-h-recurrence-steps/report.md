# Special Function Proof Agent

H_{(n+1)}(x) = (((2*x)*H_{n}(x))-((2*n)*H_{(n-1)}(x)))

条件：n is nat、x is real、n >= 1

完全Lean証明：proved
数値診断：no_mismatch_found

Hermite規約：Hは物理学規約、Heは確率論規約。次数は自然数です。

構造化ステップ（各等式を元の全条件で検査）：
1. H_{(n+1)}(x) = (((2*x)*H_{n}(x))-((2*n)*H_{(n-1)}(x)))
   物理学規約Hと確率論規約Heを結ぶ変換から導いた漸化式を適用する。
