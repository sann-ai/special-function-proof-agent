# Special Function Proof Agent

Jacobi(n,0,0,x) = P_{n}(x)

条件：n is nat、x is real

完全Lean証明：proved
数値診断：no_mismatch_found

構造化ステップ（各等式を元の全条件で検査）：
1. Jacobi(n,0,0,x) = P_{n}(x)
   Jacobiの両パラメータが0の有限和を標準Legendreの定義へ接続する。
