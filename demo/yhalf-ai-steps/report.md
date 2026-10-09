# Special Function Proof Agent

D_x(YNoninteger(1/2,x)) = ((YNoninteger(-1/2,x)-YNoninteger(3/2,x))/2)

条件：x is real、x > 0

完全Lean証明：proved
数値診断：no_mismatch_found

構造化ステップ（各等式を元の全条件で検査）：
1. D_x(YNoninteger(1/2,x)) = ((YNoninteger(-1/2,x)-YNoninteger(3/2,x))/2)
   半整数次数の第二種ベッセル関数の微分公式を適用する。
