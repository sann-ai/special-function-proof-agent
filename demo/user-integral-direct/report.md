# Special Function Proof Agent

ShiftedArea(a=a,b=b,x=x) = ((((b+x)^3)-((a+x)^3))/3)

条件：a is real、b is real、x is real

完全Lean証明：proved
数値診断：no_mismatch_found

研究関数の明示定義：元の呼出しを含むtheorem targetと、定義を展開したexpanded_targetを検証済みの解析的橋渡し定理で接続します。
- ShiftedArea(a: real, b: real, x: real) = integral(a..b, ((t+x)^2) dt)。定義ID：5dc64c7ea8c9d68692eede8fd9dea99b1921b04e399fcde1429b8d23b7993d4e
- ShiftedArea の定義根拠：入力された被積分多項式との一致と、指定した実端点間の有向積分の可積分性・原始関数公式を Lean で検証します。 橋渡し：ResearchAnalytic_afaea59c0c1ce0b13c3a5051c72089744a1763649dc6403f0f2622f324569129_bridge
展開後の式：((((((x*x)*(b^1))/1)+(((x+x)*(b^2))/2))+((1*(b^3))/3))-(((((x*x)*(a^1))/1)+(((x+x)*(a^2))/2))+((1*(a^3))/3))) = ((((b+x)^3)-((a+x)^3))/3)
定義・依存関係・元条件は request.json、analysis.json、certificate.lean に保存します。
