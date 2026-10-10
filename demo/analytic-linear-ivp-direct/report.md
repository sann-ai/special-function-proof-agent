# Special Function Proof Agent

LinearFlow(a=a,c=c,u=x) = (c*exp((a*x)))

条件：a is real、c is real、x is real

完全Lean証明：proved
数値診断：no_mismatch_found

研究関数の明示定義：元の呼出しを含むtheorem targetと、定義を展開したexpanded_targetを検証済みの解析的橋渡し定理で接続します。
- LinearFlow(a: real, c: real, u: real) = IVP(y'= (a)*y, y(0)=c; t=u)。定義ID：66b143907cd9432ec06146f8a839686dc1f8461d20b6022565509dbdb5a86fe0
- LinearFlow の定義根拠：rate と initial を固定し、全実数上の各点で y'=rate*y を満たし y(0)=initial となる関数の存在・一意性を検証します。 橋渡し：SpecialFunctionProofAgent.homogeneousIVPSolution_eq_exp
展開後の式：(c*exp((a*x))) = (c*exp((a*x)))
定義・依存関係・元条件は request.json、analysis.json、certificate.lean に保存します。
