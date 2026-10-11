# Special Function Proof Agent

PolynomialFlow(a=a,c=c,x=x) = (c*exp((((a*((x^2)-1))/2)+(2*(x-1)))))

条件：a is real、c is real、x is real

完全Lean証明：proved
数値診断：no_mismatch_found

研究関数の明示定義：元の呼出しを含むtheorem targetと、定義を展開したexpanded_targetを検証済みの解析的橋渡し定理で接続します。
- PolynomialFlow(a: real, c: real, x: real) = IVP(y'=(((a*t)+2)*y), y(1)=c; t=x)。定義ID：82261b175938d10e2dea2c231c3706699e10d94f3a2fdfcd598fc7c557a0e96a
- PolynomialFlow の定義根拠：入力された右辺・初期時刻・初期値を保持し、全実数上の各点でその微分条件を満たす実関数の存在一意性を Lean で検証します。 橋渡し：ResearchAnalytic_f1f930a436d777928bc4b8d4c5db2337293b325b03ff5bb76667acdaae3b197d_bridge
展開後の式：(c*exp(((((2*(x^1))/1)+((a*(x^2))/2))-(((2*(1^1))/1)+((a*(1^2))/2))))) = (c*exp((((a*((x^2)-1))/2)+(2*(x-1)))))
定義・依存関係・元条件は request.json、analysis.json、certificate.lean に保存します。
