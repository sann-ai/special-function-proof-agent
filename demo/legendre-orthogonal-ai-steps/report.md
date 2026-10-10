# Special Function Proof Agent

int(-1,1,(P_{m}(t)*P_{n}(t)),t) = 0

条件：m is nat、n is nat、m != n

完全Lean証明：proved
数値診断：no_mismatch_found

構造化ステップ（各等式を元の全条件で検査）：
1. int(-1,1,(P_{m}(t)*P_{n}(t)),t) = 0
   次数が異なる自然数次数のルジャンドル多項式の直交性を適用する。
