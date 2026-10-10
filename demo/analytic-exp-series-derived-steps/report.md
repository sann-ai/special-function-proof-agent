# Special Function Proof Agent

(2*SeriesExp(u=x)) = (2*exp(x))

条件：x is real

完全Lean証明：proved
数値診断：no_mismatch_found

研究関数の明示定義：元の呼出しを含むtheorem targetと、定義を展開したexpanded_targetを検証済みの解析的橋渡し定理で接続します。
- SeriesExp(u: real) = sum(n=0..infinity, (u)^n/n!)。定義ID：a9cd0c69e62cd05c0dda348d582b8639afb20e9074aeefbce7b704c23da4082b
- SeriesExp の定義根拠：全実引数で階乗級数の HasSum と収束を検証し、exp との等式を適用します。 橋渡し：SpecialFunctionProofAgent.exponentialSeries_eq_exp
展開後の式：(2*exp(x)) = (2*exp(x))
定義・依存関係・元条件は request.json、analysis.json、certificate.lean に保存します。

研究補題の再利用：元の命題と全条件を固定し、各補題の仮定をこの命題の条件からLeanで確認します。
- exp-series-identity (b282c1d9e15835c110a406007a8f103b1d632a6aac514c7147b82b75854a4498)
  Function[a9cd0c69e62cd05c0dda348d582b8639afb20e9074aeefbce7b704c23da4082b](u=x) = exp(x)
  補題の条件：x is real
適用1：b282c1d9e15835c110a406007a8f103b1d632a6aac514c7147b82b75854a4498、x ← x。左辺から右辺へ使います。
証明と依存関係は certificate.lean、request.json、analysis.json に保存します。

構造化ステップ（各等式を元の全条件で検査）：
1. (2*SeriesExp(u=x)) = (2*exp(x))
   元の解析定義の検証済み等式を適用し、両辺を2倍する。
