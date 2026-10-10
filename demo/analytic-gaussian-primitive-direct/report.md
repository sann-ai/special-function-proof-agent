# Special Function Proof Agent

GaussianArea(u=x) = ((sqrt(pi)/2)*erf(x))

条件：x is real

完全Lean証明：proved
数値診断：no_mismatch_found

研究関数の明示定義：元の呼出しを含むtheorem targetと、定義を展開したexpanded_targetを検証済みの解析的橋渡し定理で接続します。
- GaussianArea(u: real) = integral(0..u, exp(-t^2) dt)。定義ID：81a34d239981e263eea547af58facdda907c950fc76bd9a9a620432e614d31eb
- GaussianArea の定義根拠：0から実端点への有向区間で可積分性を検証し、sqrt(pi)/2 * erf との等式を適用します。 橋渡し：SpecialFunctionProofAgent.gaussianPrimitive_eq_erf
展開後の式：((sqrt(pi)/2)*erf(x)) = ((sqrt(pi)/2)*erf(x))
定義・依存関係・元条件は request.json、analysis.json、certificate.lean に保存します。
