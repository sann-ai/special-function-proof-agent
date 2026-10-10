# Bessel Yの定義と形式化範囲

`SpecialFunctionProofAgent/BesselY.lean` は、正実軸の第二種Bessel関数を既存の `Complex.besselJ` と標準接続式から構成します。関連モジュールは、非整数次数の公式、全整数次数での標準極限・漸化式・Wronskian、Y₀とY₁の引数微分、元の根条件付き交差積を公開しています。

## 非整数次数の標準定義

実数次数a、正の実引数xについて、まず

\[
j(a,x)=\operatorname{Re}(\texttt{Complex.besselJ}(a,x))
\]

を `realBesselJ` と定義します。`ofReal_realBesselJ` は、x>0なら、この実数を複素数へ埋め戻した値が `Complex.besselJ` の値全体に一致することを証明します。証明では既存Jの正則化超幾何級数とGamma関数の実軸上の共役対称性を使います。

非整数aについて、[DLMF 10.2.3](https://dlmf.nist.gov/10.2.E3) の標準接続式

\[
Y_a(x)=\frac{j(a,x)\cos(\pi a)-j(-a,x)}{\sin(\pi a)}
\]

を `besselYNoninteger (a x : ℝ)` と定義します。`ofReal_besselYNoninteger` により、同じ式を既存の複素Bessel Jで書いた値との一致を確認できます。分母の条件 `sin(a*pi)≠0` と「aがどの整数とも等しくない」という条件の同値は `sin_order_pi_ne_zero_iff` です。

正実軸・非整数次数では、既存Jの漸化式と微分補題から次を証明しています。

- `besselYNoninteger_neg`：次数反転の接続式。
- `besselYNoninteger_recurrence`：`Y(a-1,x)+Y(a+1,x)=(2*a/x)*Y(a,x)`。
- `hasDerivAt_besselYNoninteger` と `deriv_besselYNoninteger`：`Y'(a,x)=(a/x)*Y(a,x)-Y(a+1,x)`。
- `besselYNoninteger_ode`：`x^2*Y''+x*Y'+(x^2-a^2)*Y=0`。

漸化式・微分・微分方程式の引数条件は `x>0`、次数条件は `sin(a*pi)≠0` です。次数反転は接続式と三角関数の恒等式から導きます。これらの定理は標準接続式で定義したYを対象とし、Jと三角関数の証明済み補題から導きます。

## CLIで完全証明する固定半整数の2公式

CLIでは明示名 `YNoninteger(order,x)` を使用します。構造化入力は `bessel_y_noninteger {order,arg}` で、次数は既存の正確な `rational {numerator,denominator}` 形式です。初期の入力範囲は次数−1/2、1/2、3/2、正の実引数です。

```text
YNoninteger(-1/2,x)+YNoninteger(3/2,x)=YNoninteger(1/2,x)/x; x>0
```

この式は `Yhalf_recurrence` に接続します。

```text
D_x(YNoninteger(1/2,x))=(YNoninteger(-1/2,x)-YNoninteger(3/2,x))/2; x>0
```

この式は `Yhalf_derivative` に接続します。`hasDerivAt_Yhalf` は同じ点での微分可能性も含みます。どちらの公式も、Leanへの入力条件は `x>0` のみです。半整数における正弦の非零性は `sin_half_order_pi_ne_zero` で証明済みです。

directは対応する補題を元の等式へ適用します。stepsは元の全条件の下で各等式を検査し、元の左辺から右辺へ接続します。完全なLean証明と公理監査が通ると、`proved`、`full_function_proof: true`、`full_bessel_proof: true` と保存します。変数型・左右辺・全条件・関数規約は保存され、replayでは保存された証明と再生成した命題の一致も確認します。数値診断に使うmpmathがない環境でも、このLean検査と証拠保存を実行できます。

従来の `Y_n(x)`、`Y(order,x)` と交差積 `X_nm(s,t)` は既存のASTを保持します。整数Yの登録漸化式、Y₀・Y₁の引数微分、全整数の隣接次数Wronskian、同点X₀₁と固定された根条件付き交差積は下記の完全証明へ接続します。対応範囲外の入力は `unresolved`、`full_bessel_proof: false` です。引数や除算の条件が不足する場合は `needs_conditions` となります。旧diagnostic経路では、元の全条件と条件付き代数定理の前提を保存します。

## 整数次数の標準定義と極限

[DLMF 10.2.4](https://dlmf.nist.gov/10.2.E4) に従い、整数nについて

\[
\operatorname{besselYInt}(n,x)
=\frac{\left.\partial_a j(a,x)\right|_{a=n}
+(-1)^n\left.\partial_a j(a,x)\right|_{a=-n}}{\pi}
\]

を定義します。次数0・1・2での式の展開と、負次数の対称性 `Y(-n,x)=(-1)^n*Y(n,x)` を証明しています。

`tendsto_besselYNoninteger_int_of_differentiable_order` は、次の2つの前提から非整数接続式のnでの極限がこの定義に一致することを証明します。

```lean
DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) (n : ℝ)
DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) (-n : ℝ)
```

ここで微分する変数は次数aです。この条件付き補題は、既存Jの負整数次数の対称性と、分子・分母の微分から得る差商の極限を使います。n=0では同じ点の微分可能性が両方の前提を満たします。

## 整数Yの追加接続と明示前提

`SpecialFunctionProofAgent/BesselYInteger.lean` は上のJ・Yの定義をそのままimportします。正の実引数xを固定し、次の2つを前提として整数次数全体への接続を証明します。

```lean
h0 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 0
h1 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 1
```

`differentiableAt_realBesselJ_int_order_of_zero_one` は、Jの三項漸化式で隣接次数の微分可能性を正負両方向へ伝播させ、任意整数nでの次数微分可能性を導きます。これにより、整数Yの三項漸化式と整数極限の前提をこの2点へ集約します。

- `besselYInt_recurrence_of_order_differentiable_zero_one`：任意整数n、x>0、h0、h1の下で `Y(n-1,x)+Y(n+1,x)=(2*n/x)*Y(n,x)`。
- `tendsto_besselYNoninteger_int_of_order_differentiable_zero_one`：同じ前提から、非整数Yのnへの極限が `besselYInt n x` に一致すること。
- `besselYInt_recurrence_of_differentiable_order`：次数n−1,n,n+1,−n−1,−n,−n+1の微分可能性を個別に指定する形。次数方向に微分したJの漸化式と整数反転公式から導きます。

`BesselYAnalytic.lean` はx>0からh0とh1を証明します。以下の項ごとの証明を、次数に依存する級数の一様評価へ接続しました。`differentiable_hgCoeff_order` と `differentiable_besselJ_series_term_order` は、逆Gammaの全平面での微分可能性を使い、各係数と各J級数項が次数について複素微分可能であることを証明します。`hasSum_besselJ_order_series` は、それらの項の和を既存の `Complex.besselJ` に接続します。複素円板 `|a−1/2|<1` 上では `Re(a)>−1/2` です。逆Gammaの漸化式から `|1/Gamma(a+1+k)| ≤ C·2^k` を得て、正則化超幾何級数の各項を `C·(2|z|)^k/k!` で一様に評価します。固定mathlibの複素関数級数の微分可能性定理と、指数級数の総和可能性を適用し、次数0と1の複素微分可能性から実微分可能性を導きます。

Y₀・Y₁の引数微分の既存補題には、証明済みh0、h1と次の混合微分の前提を使います。cは次数0、1、−1のいずれかです。

```lean
HasDerivAt
  (fun t : ℝ => deriv (fun a : ℝ => realBesselJ a t) c)
  (deriv (fun a : ℝ => deriv (realBesselJ a) x) c) x
```

この前提は、次数微分をxで微分でき、その値が逆順の微分と一致することを表します。`BesselYArgument.lean` はx>0からc=0,1,−1のこの前提を証明します。次の条件付き補題も、保存済み証拠の意味を保持するため引き続き利用できます。

- `hasDerivAt_besselYInt_zero_of_order_derivative_exchange` はc=0の前提から `Y₀'(x)=−Y₁(x)` を導きます。
- `hasDerivAt_besselYInt_one_of_order_derivative_exchange` はc=1,−1の前提から `Y₁'(x)=Y₀(x)−Y₁(x)/x` を導きます。
- `besselYInt_wronskian_zero_of_order_derivative_exchange` はc=0の前提から、`J₀Y₀'−J₀'Y₀=J₁Y₀−J₀Y₁` を導きます。
- `hasDerivAt_besselYInt_scaled_wronskian_of_order_derivative_exchange` はc=0,1,−1の前提から、`x*(J₁(x)*Y₀(x)−J₀(x)*Y₁(x))` のx微分が0であることを導きます。定数2/πの評価は下記のWronskian規格化で証明します。

引数微分・Wronskianの前提付き定理を使うときは、必要な混合微分の条件を元命題と分けて明示します。新しい引数微分とWronskianの完全証明は、下記の前提を解消した定理に接続します。

## 引数微分の交換と完全証明

`BesselYArgument.lean` は正則化超幾何級数の次数微分係数をCauchy評価で抑えます。階乗を含む可算和の評価により、次数で微分した級数を引数でも項別微分し、係数シフト式とJの積の微分公式へ接続します。非負の実次数cでは `hasDerivAt_realBesselJ_order_deriv_of_nonneg` を証明し、次数−1はJの既存漸化式から導きます。

`realBesselJ_order_derivative_exchange_zero/one/neg_one` の前提はx>0のみです。これを既存のY微分補題へ適用した `hasDerivAt_besselYInt_zero/one` と `deriv_besselYInt_zero/one` は、同じ条件で

\[
Y_0'(x)=-Y_1(x),\qquad Y_1'(x)=Y_0(x)-Y_1(x)/x
\]

を証明します。CLIの微分変数は同じ実引数であり、次の2例をdirect/stepsへ接続します。

```text
D_x(Y_0(x))=-Y_1(x); x>0
D_x(Y_1(x))=Y_0(x)-Y_1(x)/x; x>0
```

入力ファイルは `examples/integer-y-zero-derivative.txt` と `examples/integer-y-one-derivative.txt` です。別変数の微分や合成引数へこのレシピを適用するには、その式の微分を別途証明する必要があります。

## Wronskianの規格化と交差積の符号

`BesselYWronskian.lean` は、既存Jの微分と漸化式から
`x*(J_(a+1)(x)*J_(-a)(x)+J_a(x)*J_(-a-1)(x))` が正実軸上で定数になることを示します。原点極限では冪を相殺して正則化超幾何関数の零点値に帰着し、Gamma反射式で定数を評価します。`realBesselJ_opposite_order_product` がこの接続を担います。

標準接続式で定義した非整数Yへ代入すると、`besselYNoninteger_wronskian` はx>0、sin(aπ)≠0から係数2/πを確定します。既存の整数次数極限をa→0へ適用し、整数J/Yの漸化式で正負両方向へ伝播させた `besselYInt_wronskian` は、全整数nとx>0で

\[
J_{n+1}(x)Y_n(x)-J_n(x)Y_{n+1}(x)=\frac{2}{\pi x}
\]

を証明します。CLIも `examples/integer-y-wronskian.txt` の `n integer,x>0` をそのまま扱います。標準Wronskianの微分形と同じ並び順の隣接次数式です。

既存の交差積定義 `X_nm(s,t)=J_n(s)Y_m(t)-Y_n(s)J_m(t)` では、同点の次数0,1が逆順になり、

\[
X_{01}(x,x)=J_0(x)Y_1(x)-Y_0(x)J_1(x)=-\frac{2}{\pi x}<0
\]

です。`besselYInt_cross_zero_one` と `besselYInt_cross_zero_one_neg` が等式と厳密な負値を証明します。`examples/integer-y-cross-same-point.txt` は元のX ASTと定義の順序を保持して、この等式を検査します。

```sh
python3 -m special_function_agent verify examples/integer-y-zero-derivative.txt --route direct --output runs/y0-derivative --archive
python3 -m special_function_agent verify examples/integer-y-one-derivative.txt --route steps --output runs/y1-derivative --archive
python3 -m special_function_agent verify examples/integer-y-wronskian.txt --route steps --output runs/y-wronskian --archive
python3 -m special_function_agent verify examples/integer-y-cross-same-point.txt --route direct --output runs/x01 --archive
python3 -m special_function_agent replay runs/x01
```

## CLIで完全証明する整数Y漸化式

`BesselYAnalytic.lean` の `besselYInt_recurrence (n : ℤ) (x : ℝ) (hx : 0 < x)` は

\[
Y_{n-1}(x)+Y_{n+1}(x)=\frac{2n}{x}Y_n(x)
\]

を証明します。全整数への次数微分可能性は `differentiableAt_realBesselJ_int_order`、標準非整数Yから整数Yへの極限は `tendsto_besselYNoninteger_int` です。いずれも実引数の条件はx>0です。次数微分・混合微分・分母非零を追加前提として生成定理に加える処理はありません。除算に必要なx≠0は元のx>0から導きます。

CLIは `n integer` と安全なASCII実変数名を使った次の形を受け付けます。次数変数nの値は負・零・正の全整数を含みます。現在の登録レシピは次数表現n−1,n,n+1の同じ引数の漸化式です。

```text
Y_{n-1}(x)+Y_{n+1}(x)=2*n/x*Y_n(x); n integer,x>0
```

```sh
python3 -m special_function_agent verify examples/integer-y-complete.txt --route direct --output runs/integer-y-direct --archive
python3 -m special_function_agent verify examples/integer-y-complete.txt --route steps --output runs/integer-y-steps --archive
python3 -m special_function_agent replay runs/integer-y-steps
```

成功時は `proved`、`full_function_proof: true`、`full_bessel_proof: true` を保存します。型・全条件・元のY ASTと規約を保持し、Leanでは標準定義 `besselYInt` へ変換します。`examples/integer-y-recurrence.txt` も同じ元命題なので、direct/stepsではこの完全証明を利用します。

## 従来の条件付き整数Y証拠の互換性

保存済みの `proof: {mode: diagnostic}` は元の2前提と条件付き範囲を保持します。明示的に作る場合は `--route diagnostic` を指定します。

```sh
python3 -m special_function_agent verify examples/integer-y-recurrence.txt --route diagnostic --output runs/integer-y --archive
python3 -m special_function_agent replay runs/integer-y
```

このdiagnostic経路は `n integer,x>0` を元条件とし、h0・h1を条件付き定理の追加前提として `analysis.json`、`conditional_certificate.lean`、結果JSON、レポート、archiveの詳細へ保存します。両コマンドの終了コードは `1`、元命題の状態は `unresolved` です。条件付き証拠の再検査が通ると `conditional_replayed: true`、`replayed: false`、`full_bessel_proof: false` を返します。

条件付き定理の前提とLeanソースは標準名 `x` を使い、解析テンプレートの `substitutions` で元入力の実変数名へ対応させます。例えば引数名 `radius` の入力は `{"n":"n","x":"radius"}` を保存します。元入力の変数名・型・全条件を保持したまま、追加前提の意味を確認できます。

## 元の根条件付き交差積の完全証明

`BesselYCross.lean` の `besselCross` は元のASTと同じ
`X_nm(s,t)=J_n(s)Y_m(t)-Y_n(s)J_m(t)` を定義します。
`z>0,0<lambda<1,X_01(z,lambda*z)=0` から、次の式を証明します。

\[
\frac{X_{00}(z,\lambda z)^2}
 {X_{01}(z,z)^2+\lambda^2X_{00}(z,\lambda z)X_{02}(z,\lambda z)}
=\frac1\lambda\frac{X_{00}(z,\lambda z)}
 {X_{11}(z,\lambda z)-\lambda X_{00}(z,\lambda z)}.
\]

引数微分からエネルギー関数
`F(t)=t^2/2*(X_00(z,t)^2+X_01(z,t)^2)` の微分が
`t*X_00(z,t)^2` になることを証明します。区間 `[lambda*z,z]` 上で積分し、
Wronskianと根条件から得た下端の `X_00 != 0` を使って積分の厳密な正値性を導きます。
`besselCross_root_left_denominator_pos` は元の左分母が正であることを、
`besselCross_root_right_denominator_ne_zero` は元の右分母が非零であることを証明します。
`besselCross_root_identity` はこの2定理と因数分解を使って除算の等式を閉じます。

```sh
python3 -m special_function_agent verify examples/cross-product-root.txt --route direct --output runs/cross-direct --archive
python3 -m special_function_agent verify examples/cross-product-root.txt --route steps --output runs/cross-steps --archive
python3 -m special_function_agent replay runs/cross-steps
```

生成される定理は元の正値条件・上限条件・根条件を保持し、両分母の非零性を証明内で導出します。
左右を交換した式、安全な変数名を使った同じ構造にも対応します。結果は
`proved`、`full_bessel_proof: true` で、数値診断は独立に保存します。

## 今後の範囲

一般整数次数の引数微分をCLIへ登録する拡張、別の次数や複数の根条件を持つ交差積、
複素引数・枝の扱いは後続の範囲です。各公式を標準定義から証明し、元入力の条件へ接続して登録します。

旧条件付き証拠は元の前提を保存します。同じ漸化式・根条件付き交差積の新しい完全証明は、
元記録を残して明示的に作成します。[archive更新手順](archive.md#条件付き記録から完全証明へ)を参照してください。

## 検査

```sh
lake build SpecialFunctionProofAgent.BesselY
lake build SpecialFunctionProofAgent.BesselYInteger
lake build SpecialFunctionProofAgent.BesselYAnalytic
lake build SpecialFunctionProofAgent.BesselYArgument
lake build SpecialFunctionProofAgent.BesselYWronskian
lake build SpecialFunctionProofAgent.BesselYCross
python3 -m unittest discover -s tests -p 'test_bessel_y_formal.py' -v
SF_RUN_LEAN_TESTS=1 python3 -m unittest discover -s tests -p 'test_bessel_y_formal.py' -v
SF_RUN_LEAN_TESTS=1 python3 -m unittest discover -s tests -p 'test_integer_y_conditional.py' -v
SF_RUN_LEAN_TESTS=1 python3 -m unittest discover -s tests -p 'test_integer_y_complete.py' -v
SF_RUN_LEAN_TESTS=1 python3 -m unittest discover -s tests -p 'test_integer_y_calculus.py' -v
SF_RUN_LEAN_TESTS=1 python3 -m unittest discover -s tests -p 'test_cross_complete.py' -v
```

基礎の `BesselY.lean` は定義3個と公開定理22個を `#print axioms` で監査します。依存公理は `propext`、`Classical.choice`、`Quot.sound` です。受入テストでは固定半整数の両公式・両経路・replay、次数と係数の誤り、条件不足、候補からの命題や仮定の注入、保存証拠の改変、数値backend欠落時の保存継続、旧diagnostic証拠の状態保持を検査します。

`BesselYInteger.lean`、`BesselYAnalytic.lean`、`BesselYArgument.lean`、`BesselYWronskian.lean`、`BesselYCross.lean` の全公開定理を、同じ標準公理の許可集合で監査します。CLI検査には微分変数、合成引数、正値条件不足、Wronskianの符号・次数・係数、同点と異なる2点の取り違え、根条件・区間条件の欠落、X₀₂と右分子の改変、両分母の非零性を含めます。全モジュールを合わせた公開監査は141宣言です。
