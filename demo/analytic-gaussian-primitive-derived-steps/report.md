# Special Function Proof Agent

(2*GaussianArea(u=x)) = (2*((sqrt(pi)/2)*erf(x)))

条件：x is real

完全Lean証明：proved
数値診断：no_mismatch_found

研究関数の明示定義：元の呼出しを含むtheorem targetと、定義を展開したexpanded_targetを検証済みの解析的橋渡し定理で接続します。
- GaussianArea(u: real) = integral(0..u, exp(-t^2) dt)。定義ID：81a34d239981e263eea547af58facdda907c950fc76bd9a9a620432e614d31eb
- GaussianArea の定義根拠：0から実端点への有向区間で可積分性を検証し、sqrt(pi)/2 * erf との等式を適用します。 橋渡し：SpecialFunctionProofAgent.gaussianPrimitive_eq_erf
展開後の式：(2*((sqrt(pi)/2)*erf(x))) = (2*((sqrt(pi)/2)*erf(x)))
定義・依存関係・元条件は request.json、analysis.json、certificate.lean に保存します。

研究補題の再利用：元の命題と全条件を固定し、各補題の仮定をこの命題の条件からLeanで確認します。
- gaussian-primitive-identity (f57a2d4868ffb0b676d09f7e4c7c04b413ccfcaa431c7993ab5b624a5a0d8b50)
  Function[81a34d239981e263eea547af58facdda907c950fc76bd9a9a620432e614d31eb](u=x) = ((sqrt(pi)/2)*erf(x))
  補題の条件：x is real
適用1：f57a2d4868ffb0b676d09f7e4c7c04b413ccfcaa431c7993ab5b624a5a0d8b50、x ← x。左辺から右辺へ使います。
証明と依存関係は certificate.lean、request.json、analysis.json に保存します。

構造化ステップ（各等式を元の全条件で検査）：
1. (2*GaussianArea(u=x)) = (2*((sqrt(pi)/2)*erf(x)))
   元の解析定義の検証済み等式を適用し、両辺を2倍する。
