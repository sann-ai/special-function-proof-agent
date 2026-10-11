# Special Function Proof Agent

(2*WeightedSeries(a=a,x=x)) = (2*((a*exp(x))+((1-a)*exp((-x)))))

条件：a is real、x is real

完全Lean証明：proved
数値診断：no_mismatch_found

研究関数の明示定義：元の呼出しを含むtheorem targetと、定義を展開したexpanded_targetを検証済みの解析的橋渡し定理で接続します。
- WeightedSeries(a: real, x: real) = sum(k=0..infinity, ((a*((x)^(k)/k!))+((1-a)*(((-x))^(k)/k!))))。定義ID：a57070a8fad22ee60df32dff63ce460de5d28198e293d254874dd7caa41e650d
- WeightedSeries の定義根拠：入力された一般項と階乗核の有限線形結合の一致、および HasSum・収束を Lean で検証します。係数と核引数は自然数の和変数に依存しません。 橋渡し：ResearchAnalytic_90db31acc78eebd021d3330f316406541c6b10968aa2350c41bed421a3e67b84_bridge
展開後の式：(2*((a*exp(x))+((1-a)*exp((-x))))) = (2*((a*exp(x))+((1-a)*exp((-x)))))
定義・依存関係・元条件は request.json、analysis.json、certificate.lean に保存します。

研究補題の再利用：元の命題と全条件を固定し、各補題の仮定をこの命題の条件からLeanで確認します。
- series-identity (dd5c8c8d92419008da5df0339ae6219d83f9ae4e5fed8032b71609f2727fb730)
  Function[a57070a8fad22ee60df32dff63ce460de5d28198e293d254874dd7caa41e650d](a=a,x=x) = ((a*exp(x))+((1-a)*exp((-x))))
  補題の条件：a is real、x is real
適用1：dd5c8c8d92419008da5df0339ae6219d83f9ae4e5fed8032b71609f2727fb730、a ← a、x ← x。左辺から右辺へ使います。
証明と依存関係は certificate.lean、request.json、analysis.json に保存します。
