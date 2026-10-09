# Special Function Proof Agent

Jacobi(1,a,b,x) = (((a-b)+(((a+b)+2)*x))/2)

条件：a is real、b is real、x is real

完全Lean証明：proved
数値診断：no_mismatch_found

構造化ステップ（各等式を元の全条件で検査）：
1. Jacobi(1,a,b,x) = (((a-b)+(((a+b)+2)*x))/2)
   Jacobiの標準有限和から、元の実パラメータを保持して低次数を評価する。
