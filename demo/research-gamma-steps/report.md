# Special Function Proof Agent

Gamma((x+2)) = (((x+1)*x)*Gamma(x))

条件：x is real、x > 0

完全Lean証明：proved
数値診断：no_mismatch_found

研究補題の再利用：元の命題と全条件を固定し、各補題の仮定をこの命題の条件からLeanで確認します。
- gamma-step (b2d6b64014f068f0def5d3915656e24a4e87278f5830181a4acf8985bd689421)
  Gamma((x+1)) = (x*Gamma(x))
証明と依存関係は certificate.lean、request.json、analysis.json に保存します。

構造化ステップ（各等式を元の全条件で検査）：
1. Gamma((x+2)) = Gamma(((x+1)+1))
   引数を漸化式に合う形に整理する。
2. Gamma(((x+1)+1)) = ((x+1)*Gamma((x+1)))
   x+1>0よりガンマ関数の漸化式を適用する。
3. ((x+1)*Gamma((x+1))) = ((x+1)*(x*Gamma(x)))
   x>0より漸化式をもう一度適用する。
4. ((x+1)*(x*Gamma(x))) = (((x+1)*x)*Gamma(x))
   積の結合則で右辺の形に整理する。
