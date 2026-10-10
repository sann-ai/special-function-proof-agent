# 正実数のBessel診断

(Y_{(n-1)}(x)+Y_{(n+1)}(x)) = (((2*n)/x)*Y_{n}(x))

条件：n is int、x is real、x > 0

状態：unresolved。この記録は明示前提からの条件付き証拠を保持します。同じ元式の完全証明はdirect/steps経路で新しく保存できます。

数値診断：no_mismatch_found。有限標本の結果を numerical.json に保存しました。

## 解析テンプレート
正の引数xを固定し、Jの次数0と1での次数微分可能性を明示前提とする。
Jの漸化式から次数微分可能性を全整数点へ伝播させる。
Jの漸化式を次数で微分し、標準次数微分式で定義したbesselYIntの漸化式へ接続する。
同じ2前提から非整数Yの整数次数への極限とbesselYIntの一致を得る。

## 条件付きLean
明示前提の下での検査：True。仮定：0 < x、DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 0、DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 1
残る形式化：正の引数でJの次数0における次数微分可能性を証明すること。、正の引数でJの次数1における次数微分可能性を証明すること。
