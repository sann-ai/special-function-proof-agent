# Special Function Proof Agent

int(-1,1,(P_{n}(t)^2),t) = (2/((2*n)+1))

条件：n is nat

完全Lean証明：proved
数値診断：no_mismatch_found

構造化ステップ（各等式を元の全条件で検査）：
1. int(-1,1,(P_{n}(t)^2),t) = (2/((2*n)+1))
   標準Legendreの直交性と三項漸化式から、区間[-1,1]上の二乗積分2/(2n+1)を評価する。
