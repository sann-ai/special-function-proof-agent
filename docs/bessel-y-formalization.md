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

## 残る解析的な接続

整数Yと交差積の完全証明には、次の内容をLeanで証明し、接続する必要があります。

1. **次数方向の微分可能性**：正のxを固定した `a ↦ realBesselJ a x` が、対象の±整数次数で微分可能であること。固定mathlibの正則化超幾何関数が持つ引数方向の解析性に加え、パラメータ方向の級数微分を正当化する収束評価が必要です。
2. **整数次数の引数微分**：次数微分と引数微分の交換、または整数極限と引数微分の交換を正当化し、整数Yの漸化式・微分公式へ接続すること。
3. **Wronskianの正規化**：同じJ・Yの定義から `J_n(x)*Y_n'(x)-J_n'(x)*Y_n(x)=2/(pi*x)` を証明すること。微分方程式から得られる比例形に、標準定義による定数の評価を加えます。
4. **交差積への接続**：`X_nm(s,t)=J_n(s)*Y_m(t)-Y_n(s)*J_m(t)` の定義、対象の根条件からの漸化式、正エネルギー積分の可積分性と厳密な正値性を証明すること。
5. **除算の条件**：上の解析的な結果から、元の交差積等式に現れる各分母の非零性を導くこと。

整数次数の微分可能性は、条件付きLean補題の前提として保持します。整数Y・交差積の状態を完全証明へ変更する際は、必要な接続を元の明示条件からLeanで証明します。

## 検査

```sh
lake build SpecialFunctionProofAgent.BesselY
python3 -m unittest discover -s tests -p 'test_bessel_y_formal.py' -v
SF_RUN_LEAN_TESTS=1 python3 -m unittest discover -s tests -p 'test_bessel_y_formal.py' -v
```

数学モジュールは定義3個と公開定理22個を `#print axioms` で監査します。依存公理は `propext`、`Classical.choice`、`Quot.sound` です。受入テストでは固定半整数の両公式・両経路・replay、次数と係数の誤り、条件不足、候補からの命題や仮定の注入、保存証拠の改変、数値backend欠落時の保存継続、従来Y・交差積の状態保持を検査します。
