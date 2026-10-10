# Special Function Proof Agent

Gamma((x+4)) = (((((x+3)*(x+2))*(x+1))*x)*Gamma(x))

条件：x is real、x > 0

完全Lean証明：proved
数値診断：no_mismatch_found

研究補題の再利用：元の命題と全条件を固定し、各補題の仮定をこの命題の条件からLeanで確認します。
- gamma-step (b2d6b64014f068f0def5d3915656e24a4e87278f5830181a4acf8985bd689421)
  Gamma((x+1)) = (x*Gamma(x))
  補題の条件：x is real、x > 0
- gamma-two-direct (72d00d010da2202291c65793060121cb709a578694aaaeee1d22433778c986c0)
  Gamma((x+2)) = (((x+1)*x)*Gamma(x))
  補題の条件：x is real、x > 0
適用1：72d00d010da2202291c65793060121cb709a578694aaaeee1d22433778c986c0、x ← (x+2)。左辺から右辺へ使います。
適用1：72d00d010da2202291c65793060121cb709a578694aaaeee1d22433778c986c0、x ← x。左辺から右辺へ使います。
証明と依存関係は certificate.lean、request.json、analysis.json に保存します。
