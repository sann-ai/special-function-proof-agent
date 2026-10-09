# Special Function Proof Agent

D_x(YNoninteger(1/2,x)) = ((YNoninteger(-1/2,x)-YNoninteger(3/2,x))/2)

条件：x is real、x > 0

完全Lean証明：proved
数値診断：no_mismatch_found

構造化ステップ（各等式を元の全条件で検査）：
1. D_x(YNoninteger(1/2,x)) = ((YNoninteger(-1/2,x)-YNoninteger(3/2,x))/2)
   非整数次数Yの標準接続とJの微分から、半整数Yの対称微分公式を適用する。
