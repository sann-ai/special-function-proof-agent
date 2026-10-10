# Special Function Proof Agent

ShiftedGamma(u=x) = (x*Gamma(x))

条件：x is real、x > 0

完全Lean証明：proved
数値診断：no_mismatch_found

研究関数の明示定義：元の呼出しを含むtheorem targetと、定義を展開したexpanded_targetをLeanの定義等式で接続します。
- ShiftedGamma(u: real) = Gamma((u+1))。定義ID：70c67638866fbb45129965ce8b08bfd30ffe8c4b4a1ce6a6ec641e2aa98e1580
展開後の式：Gamma((x+1)) = (x*Gamma(x))
定義・依存関係・元条件は request.json、analysis.json、certificate.lean に保存します。
