# Special Function Proof Agent

int(-1,1,(P_{n}(t)*P_{(n+1)}(t)),t) = 0

条件：n is nat

完全Lean証明：proved
数値診断：no_mismatch_found

構造化ステップ（各等式を元の全条件で検査）：
1. int(-1,1,(P_{n}(t)*P_{(n+1)}(t)),t) = 0
   自然数次数の隣接するルジャンドル多項式の直交積分を適用する。
