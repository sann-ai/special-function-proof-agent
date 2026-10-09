# Special Function Proof Agent

P_{n}((-x)) = ((-1^(n))*P_{n}(x))

条件：n is nat、x is real

完全Lean証明：proved
数値診断：no_mismatch_found

構造化ステップ（各等式を元の全条件で検査）：
1. P_{n}((-x)) = ((-1^(n))*P_{n}(x))
   標準Legendreとshifted Legendreの変換から、自然数次数の鏡映公式を適用する。
