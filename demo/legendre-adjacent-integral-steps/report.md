# Special Function Proof Agent

int(-1,1,(P_{n}(t)*P_{(n+1)}(t)),t) = 0

条件：n is nat

完全Lean証明：proved
数値診断：no_mismatch_found

構造化ステップ（各等式を元の全条件で検査）：
1. int(-1,1,(P_{n}(t)*P_{(n+1)}(t)),t) = 0
   隣接次数のLegendre積は奇関数であり、連続性と対称区間の積分から積分値0を得る。
