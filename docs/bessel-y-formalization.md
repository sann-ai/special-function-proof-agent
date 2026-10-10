# Bessel Yの定義と形式化範囲

`SpecialFunctionProofAgent/BesselY.lean` は、正実軸の第二種Bessel関数を既存の `Complex.besselJ` と標準接続式から構成します。非整数次数の証明と、整数次数の解析的な橋渡しを分けて公開しています。

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

従来の `Y_n(x)`、`Y(order,x)` と交差積 `X_nm(s,t)` は既存の診断用ASTを保持します。必要な引数条件がそろった従来経路の判定は `unresolved`、`full_bessel_proof: false` です。引数や除算の条件が不足する場合は `needs_conditions` となります。既存の根条件を使う交差積の条件付き代数証明では、元の全条件と残る解析的な接続事項を保存します。

## 整数次数の定義と条件付き極限

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

h0とh1の無条件の証明には、次数に依存する級数の微分を正当化する収束評価が残っています。`differentiable_hgCoeff_order` と `differentiable_besselJ_series_term_order` は、逆Gammaの全平面での微分可能性を使い、各係数と各J級数項が次数について複素微分可能であることを証明します。`hasSum_besselJ_order_series` は、それらの項の和を既存の `Complex.besselJ` に接続します。次の工程は、次数0と1の近傍で級数または導関数級数を一様に制御することです。

Y₀・Y₁の引数微分には、h0、h1に加えて次の混合微分の前提を使います。cは次数0、1、−1のいずれかです。

```lean
HasDerivAt
  (fun t : ℝ => deriv (fun a : ℝ => realBesselJ a t) c)
  (deriv (fun a : ℝ => deriv (realBesselJ a) x) c) x
```

この前提は、次数微分をxで微分でき、その値が逆順の微分と一致することを表します。

- `hasDerivAt_besselYInt_zero_of_order_derivative_exchange` はc=0の前提から `Y₀'(x)=−Y₁(x)` を導きます。
- `hasDerivAt_besselYInt_one_of_order_derivative_exchange` はc=1,−1の前提から `Y₁'(x)=Y₀(x)−Y₁(x)/x` を導きます。
- `besselYInt_wronskian_zero_of_order_derivative_exchange` はc=0の前提から、`J₀Y₀'−J₀'Y₀=J₁Y₀−J₀Y₁` を導きます。
- `hasDerivAt_besselYInt_scaled_wronskian_of_order_derivative_exchange` はc=0,1,−1の前提から、`x*(J₁(x)*Y₀(x)−J₀(x)*Y₁(x))` のx微分が0であることを導きます。標準の定数2/πの評価は次の接続事項です。

これらの前提付き定理を保存証拠へ使うときは、h0・h1および必要な混合微分の条件を元命題と分けて明示します。元入力からその前提を導く証明が揃うまで、整数Y・交差積の元命題は `unresolved`、`full_bessel_proof: false` を保持します。

CLIの整数Y漸化式の例は `examples/integer-y-recurrence.txt` です。

```sh
python3 -m special_function_agent verify examples/integer-y-recurrence.txt --output runs/integer-y --archive
python3 -m special_function_agent replay runs/integer-y
```

この入力は `n integer,x>0` を元条件とし、h0・h1を条件付き定理の追加前提として `analysis.json`、`conditional_certificate.lean`、結果JSON、レポート、archiveの詳細へ保存します。両コマンドの終了コードは `1`、元命題の状態は `unresolved` です。条件付き証拠の再検査が通ると `conditional_replayed: true`、`replayed: false`、`full_bessel_proof: false` を返します。

条件付き定理の前提とLeanソースは標準名 `x` を使い、解析テンプレートの `substitutions` で元入力の実変数名へ対応させます。例えば引数名 `radius` の入力は `{"n":"n","x":"radius"}` を保存します。元入力の変数名・型・全条件を保持したまま、追加前提の意味を確認できます。

## 残る解析的な接続

整数Yと交差積の完全証明には、次の内容をLeanで証明し、接続する必要があります。

1. **次数方向の微分可能性**：正のxを固定した `a ↦ realBesselJ a x` が、次数0と1で微分可能であること。上記の伝播補題で任意整数へ移せます。固定mathlibの正則化超幾何関数が持つ引数方向の解析性に加え、パラメータ方向の級数微分を正当化する収束評価が必要です。
2. **整数次数の引数微分**：次数微分と引数微分の交換、または整数極限と引数微分の交換を正当化すること。Y₀・Y₁の公式は上記の交換前提から導出済みです。
3. **Wronskianの正規化**：同じJ・Yの定義から `J_n(x)*Y_n'(x)-J_n'(x)*Y_n(x)=2/(pi*x)` を証明すること。次数0では交換前提から得る微分ゼロの関係に、標準定義による定数2/πの評価を加えます。
4. **交差積への接続**：`X_nm(s,t)=J_n(s)*Y_m(t)-Y_n(s)*J_m(t)` の定義、対象の根条件からの漸化式、正エネルギー積分の可積分性と厳密な正値性を証明すること。
5. **除算の条件**：上の解析的な結果から、元の交差積等式に現れる各分母の非零性を導くこと。

整数次数の微分可能性は、条件付きLean補題の前提として保持します。整数Y・交差積の状態を完全証明へ変更する際は、必要な接続を元の明示条件からLeanで証明します。

## 検査

```sh
lake build SpecialFunctionProofAgent.BesselY
lake build SpecialFunctionProofAgent.BesselYInteger
python3 -m unittest discover -s tests -p 'test_bessel_y_formal.py' -v
SF_RUN_LEAN_TESTS=1 python3 -m unittest discover -s tests -p 'test_bessel_y_formal.py' -v
SF_RUN_LEAN_TESTS=1 python3 -m unittest discover -s tests -p 'test_integer_y_conditional.py' -v
```

数学モジュールは定義3個と公開定理22個を `#print axioms` で監査します。依存公理は `propext`、`Classical.choice`、`Quot.sound` です。受入テストでは固定半整数の両公式・両経路・replay、次数と係数の誤り、条件不足、候補からの命題や仮定の注入、保存証拠の改変、数値backend欠落時の保存継続、従来Y・交差積の状態保持を検査します。

追加した `BesselYInteger.lean` も全公開定理をコンパイルし、同じ標準公理の許可集合で監査します。次数微分可能性と微分交換は、各定理の明示前提に残ります。
