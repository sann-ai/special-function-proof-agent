# Special Function Proof Agent

(2*ForcedMotion(c=c,v0=v0,x=x)) = (2*((c+(v0*(x-1)))+((((((2*(x^2))/1)/2)+(((1*(x^3))/2)/3))-((((2*(1^2))/1)/2)+(((1*(1^3))/2)/3)))-((((2*(1^1))/1)+((1*(1^2))/2))*(x-1)))))

条件：c is real、v0 is real、x is real

完全Lean証明：proved
数値診断：no_mismatch_found

研究関数の明示定義：元の呼出しを含むtheorem targetと、定義を展開したexpanded_targetを検証済みの解析的橋渡し定理で接続します。
- ForcedMotion(c: real, v0: real, x: real) = IVP(y''=(t+2), y(1)=c, y'(1)=v0; t=x)。定義ID：1812679c57e9e54a71dd7d16484548c093ff85a26526ec75c3e442e92dc3ab12
- ForcedMotion の定義根拠：元二階式 y''=p(t) を位置・速度の組の y'=v, v'=p(t) へ接続します。全実時間の両微分条件と独立な位置・速度初期値を満たす組の存在一意性を Lean で検証します。 橋渡し：ResearchAdvanced_aa5d4560e0353f79ce6e214a79372cf96be8d62e5cae0fc6a1e98da25065a10b_bridge
展開後の式：(2*((c+(v0*(x-1)))+((((((2*(x^2))/1)/2)+(((1*(x^3))/2)/3))-((((2*(1^2))/1)/2)+(((1*(1^3))/2)/3)))-((((2*(1^1))/1)+((1*(1^2))/2))*(x-1))))) = (2*((c+(v0*(x-1)))+((((((2*(x^2))/1)/2)+(((1*(x^3))/2)/3))-((((2*(1^2))/1)/2)+(((1*(1^3))/2)/3)))-((((2*(1^1))/1)+((1*(1^2))/2))*(x-1)))))
定義・依存関係・元条件は request.json、analysis.json、certificate.lean に保存します。

研究補題の再利用：元の命題と全条件を固定し、各補題の仮定をこの命題の条件からLeanで確認します。
- second-order-identity (ce3faa3814cd1945c34fee234dce1b6418198932956e800fc1015f2f5ce4bb5f)
  Function[1812679c57e9e54a71dd7d16484548c093ff85a26526ec75c3e442e92dc3ab12](c=c,v0=v0,x=x) = ((c+(v0*(x-1)))+((((((2*(x^2))/1)/2)+(((1*(x^3))/2)/3))-((((2*(1^2))/1)/2)+(((1*(1^3))/2)/3)))-((((2*(1^1))/1)+((1*(1^2))/2))*(x-1))))
  補題の条件：c is real、v0 is real、x is real
適用1：ce3faa3814cd1945c34fee234dce1b6418198932956e800fc1015f2f5ce4bb5f、c ← c、v0 ← v0、x ← x。左辺から右辺へ使います。
証明と依存関係は certificate.lean、request.json、analysis.json に保存します。
