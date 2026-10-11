# Special Function Proof Agent

(2*PolynomialFlow(a=a,c=c,x=x)) = (2*(c*exp((((a*((x^2)-1))/2)+(2*(x-1))))))

条件：a is real、c is real、x is real

完全Lean証明：proved
数値診断：no_mismatch_found

研究関数の明示定義：元の呼出しを含むtheorem targetと、定義を展開したexpanded_targetを検証済みの解析的橋渡し定理で接続します。
- PolynomialFlow(a: real, c: real, x: real) = IVP(y'=(((a*t)+2)*y), y(1)=c; t=x)。定義ID：82261b175938d10e2dea2c231c3706699e10d94f3a2fdfcd598fc7c557a0e96a
- PolynomialFlow の定義根拠：入力された右辺・初期時刻・初期値を保持し、全実数上の各点でその微分条件を満たす実関数の存在一意性を Lean で検証します。 橋渡し：ResearchAnalytic_f1f930a436d777928bc4b8d4c5db2337293b325b03ff5bb76667acdaae3b197d_bridge
展開後の式：(2*(c*exp(((((2*(x^1))/1)+((a*(x^2))/2))-(((2*(1^1))/1)+((a*(1^2))/2)))))) = (2*(c*exp((((a*((x^2)-1))/2)+(2*(x-1))))))
定義・依存関係・元条件は request.json、analysis.json、certificate.lean に保存します。

研究補題の再利用：元の命題と全条件を固定し、各補題の仮定をこの命題の条件からLeanで確認します。
- ode-identity (5c82279c78cdd3e65d45b632c5908016729bda180de48d2ce54ab6c87daf33d4)
  Function[82261b175938d10e2dea2c231c3706699e10d94f3a2fdfcd598fc7c557a0e96a](a=a,c=c,x=x) = (c*exp((((a*((x^2)-1))/2)+(2*(x-1)))))
  補題の条件：a is real、c is real、x is real
適用1：5c82279c78cdd3e65d45b632c5908016729bda180de48d2ce54ab6c87daf33d4、a ← a、c ← c、x ← x。左辺から右辺へ使います。
証明と依存関係は certificate.lean、request.json、analysis.json に保存します。

構造化ステップ（各等式を元の全条件で検査）：
1. (2*PolynomialFlow(a=a,c=c,x=x)) = (2*(c*exp((((a*((x^2)-1))/2)+(2*(x-1))))))
   検証済み補題で定義関数を書き換え、外側の2倍を保つ。
