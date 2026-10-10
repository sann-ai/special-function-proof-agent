# Special Function Proof Agent

GammaTail(u=x) = (((x+1)*x)*Gamma(x))

条件：x is real、x > 0

完全Lean証明：proved
数値診断：no_mismatch_found

研究関数の明示定義：元の呼出しを含むtheorem targetと、定義を展開したexpanded_targetをLeanの定義等式で接続します。
- ShiftedGamma(u: real) = Gamma((u+1))。定義ID：70c67638866fbb45129965ce8b08bfd30ffe8c4b4a1ce6a6ec641e2aa98e1580
- GammaTail(u: real) = ShiftedGamma(u=(u+1))。定義ID：c439083182700d907034c4d4ae9d604640f9167f17d1763929cc179e19876d3a
展開後の式：Gamma(((x+1)+1)) = (((x+1)*x)*Gamma(x))
定義・依存関係・元条件は request.json、analysis.json、certificate.lean に保存します。

研究補題の再利用：元の命題と全条件を固定し、各補題の仮定をこの命題の条件からLeanで確認します。
- shifted-gamma-recurrence (4d736e7c15aef1431a2f07c04b60871fa820f01fddc321162696482a52d99b86)
  Function[70c67638866fbb45129965ce8b08bfd30ffe8c4b4a1ce6a6ec641e2aa98e1580](u=x) = (x*Gamma(x))
  補題の条件：x is real、x > 0
適用1：4d736e7c15aef1431a2f07c04b60871fa820f01fddc321162696482a52d99b86、x ← (x+1)。左辺から右辺へ使います。
適用2：4d736e7c15aef1431a2f07c04b60871fa820f01fddc321162696482a52d99b86、x ← x。左辺から右辺へ使います。
証明と依存関係は certificate.lean、request.json、analysis.json に保存します。

構造化ステップ（各等式を元の全条件で検査）：
1. GammaTail(u=x) = ((x+1)*Gamma((x+1)))
   定義を展開し、x>0から従うx+1>0で漸化式を適用する。
2. ((x+1)*Gamma((x+1))) = (((x+1)*x)*Gamma(x))
   x>0で漸化式を適用し、積の結合を整理する。
