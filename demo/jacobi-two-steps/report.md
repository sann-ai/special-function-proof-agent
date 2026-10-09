# Special Function Proof Agent

Jacobi(2,a,b,x) = (((((a+1)*(a+2))/2)+((((a+b)+3)*(a+2))*((x-1)/2)))+(((((a+b)+3)*((a+b)+4))/2)*(((x-1)/2)^2)))

条件：a is real、b is real、x is real

完全Lean証明：proved
数値診断：no_mismatch_found

構造化ステップ（各等式を元の全条件で検査）：
1. Jacobi(2,a,b,x) = (((((a+1)*(a+2))/2)+((((a+b)+3)*(a+2))*((x-1)/2)))+(((((a+b)+3)*((a+b)+4))/2)*(((x-1)/2)^2)))
   Jacobiの標準有限和から、元の実パラメータを保持して低次数を評価する。
