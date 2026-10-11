# Special Function Proof Agent

WeightedSeries(a=a,x=x) = ((a*exp(x))+((1-a)*exp((-x))))

条件：a is real、x is real

完全Lean証明：proved
数値診断：no_mismatch_found

研究関数の明示定義：元の呼出しを含むtheorem targetと、定義を展開したexpanded_targetを検証済みの解析的橋渡し定理で接続します。
- WeightedSeries(a: real, x: real) = sum(k=0..infinity, ((a*((x)^(k)/k!))+((1-a)*(((-x))^(k)/k!))))。定義ID：a57070a8fad22ee60df32dff63ce460de5d28198e293d254874dd7caa41e650d
- WeightedSeries の定義根拠：入力された一般項と階乗核の有限線形結合の一致、および HasSum・収束を Lean で検証します。係数と核引数は自然数の和変数に依存しません。 橋渡し：ResearchAnalytic_90db31acc78eebd021d3330f316406541c6b10968aa2350c41bed421a3e67b84_bridge
展開後の式：((a*exp(x))+((1-a)*exp((-x)))) = ((a*exp(x))+((1-a)*exp((-x))))
定義・依存関係・元条件は request.json、analysis.json、certificate.lean に保存します。
