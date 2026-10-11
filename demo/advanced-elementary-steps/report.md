# Special Function Proof Agent

ElementaryArea(a=a,b=b,x=x) = ((((1*(exp(((2*b)+x))/2))+(3*((-cos(((1*b)+(-x))))/1)))+(1*(b*cos(x))))-(((1*(exp(((2*a)+x))/2))+(3*((-cos(((1*a)+(-x))))/1)))+(1*(a*cos(x)))))

条件：a is real、b is real、x is real

完全Lean証明：proved
数値診断：no_mismatch_found

研究関数の明示定義：元の呼出しを含むtheorem targetと、定義を展開したexpanded_targetを検証済みの解析的橋渡し定理で接続します。
- ElementaryArea(a: real, b: real, x: real) = integral(a..b, ((exp(((2*t)+x))+(3*sin((t-x))))+cos(x)) dt)。定義ID：b986f1978247a78cfdf0803337f4e332fb93b4eae06cd70bf83ff162e372a61b
- ElementaryArea の定義根拠：固定有理傾きのexp/sin/cos有限線形結合と元被積分式の一致、指定実端点間の可積分性・原始関数公式を Lean で検証します。傾き0と逆向き区間を含みます。 橋渡し：ResearchAdvanced_c49593e9c96b7619457e349bd6f8c59aafe6c3deb0c81a59dc0c2732e888d391_bridge
展開後の式：((((1*(exp(((2*b)+x))/2))+(3*((-cos(((1*b)+(-x))))/1)))+(1*(b*cos(x))))-(((1*(exp(((2*a)+x))/2))+(3*((-cos(((1*a)+(-x))))/1)))+(1*(a*cos(x))))) = ((((1*(exp(((2*b)+x))/2))+(3*((-cos(((1*b)+(-x))))/1)))+(1*(b*cos(x))))-(((1*(exp(((2*a)+x))/2))+(3*((-cos(((1*a)+(-x))))/1)))+(1*(a*cos(x)))))
定義・依存関係・元条件は request.json、analysis.json、certificate.lean に保存します。

構造化ステップ（各等式を元の全条件で検査）：
1. ElementaryArea(a=a,b=b,x=x) = ((((1*(exp(((2*b)+x))/2))+(3*((-cos(((1*b)+(-x))))/1)))+(1*(b*cos(x))))-(((1*(exp(((2*a)+x))/2))+(3*((-cos(((1*a)+(-x))))/1)))+(1*(a*cos(x)))))
   定義の同時展開後、両辺は同一の式となり、ringで等式を確認する。
