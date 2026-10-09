# 共通v2の数理仕様

v2は実数型の自由変数（最大3個）、次数変数nの型、構造化した全仮定、左辺・右辺を保存します。Besselのnは整数、Hermite・Legendre・Laguerre・Jacobiのnは自然数として宣言します。識別子は安全ASCII名、積分は `var` フィールドで束縛し、自由変数との同名衝突を拒否します。微分は実変数名を明示して保存し、他の自由実変数を固定します。Leanへの変換は入れ子の微分と積分に別々の束縛名を割り当てます。固定したmathlibの意味とプロジェクトの追加定義を、関数別登録表と環境ハッシュに含めます。

- `gamma {arg}`：`Real.Gamma`。
- `exp {arg}`：`Real.exp`。
- `rpow {base, exponent}`：`Real.rpow`。指数も実数ASTです。
- `pi`、`sqrt {arg}`：`Real.pi`、`Real.sqrt`。
- `hermite_h {order, arg}`、`hermite_he {order, arg}`：物理学規約H、確率論規約He。次数は自然数です。
- `legendre {order, arg}`、`laguerre {order, alpha, arg}`、`jacobi {order, alpha, beta, arg}`：標準多項式。次数は自然数、引数とパラメータは実数です。
- `bessel_y_noninteger {order, arg}`：正実軸の標準非整数Y。CLIの次数は−1/2、1/2、3/2の `rational {numerator, denominator}` に対応します。
- `erf {arg}`：後述する標準の実誤差関数。
- `deriv {var, arg}`：指定した自由実変数の実微分を、その変数の現在値で評価します。
- `integral {var, lower, upper, body}`：有限上端は向き付き実区間積分。`upper: {"op":"infinity"}` は `Set.Ioi lower` 上のルベーグ積分。`infinity`は積分上端だけで許可します。
- 算術はint、var、neg、add/sub/mul/div、非負整数指数pow。比較仮定は有理数とのcompareと、式を0と比較するexpr_compareです。

plain入力は `int(0,1,t^(a-1)*(1-t)^(b-1),t)`、`D_x(H_n(x))`、`erf(-x)` などです。LaTeXの `\Gamma`、`\exp`、`\int_0^1 ... dt`、`\infty`、`\sqrt{\pi}`、`\operatorname{erf}` にも対応します。全実数を対象とする式には `x real`、自然数次数には `n natural` を使います。正性などの追加条件が必要な式では、その条件を保存して検査し、不足時は `needs_conditions` を返します。

## GammaとBeta

次の3式について、各パラメータの正性を元の仮定からLeanで導出します。

1. `Gamma(x+1)=x*Gamma(x)`、x>0。
2. `int(0,1,t^(a-1)*(1-t)^(b-1),t)=Gamma(a)*Gamma(b)/Gamma(a+b)`、a,b>0。
3. `int(0,infinity,t^(a-1)*exp(-r*t),t)=r^(-a)*Gamma(a)`、a,r>0。

Betaでは実関数積分の複素埋込みとmathlibの `Complex.betaIntegral` を結び、実数Gamma比へ戻しています。scaled Gammaはmathlibの実Gamma積分から証明します。Gammaの正引数とBeta分母の非零性は定義域検査にも反映します。

## Hermiteの規約と微分

固定mathlibの `Polynomial.hermite : ℕ → Polynomial ℤ` は確率論規約の多項式です。`SpecialFunctionProofAgent/Hermite.lean` では、その実数での評価を

\[
\operatorname{He}_n(x)=\operatorname{aeval}_x(\texttt{Polynomial.hermite}\ n),
\qquad n\in\mathbb N,\ x\in\mathbb R
\]

として `hermiteHe` に定義します。物理学規約の `hermiteH` は

\[
H_n(x)=(\sqrt 2)^n\operatorname{He}_n(\sqrt 2\,x)
\]

と定義し、公開補題 `hermiteH_eq_scaled_hermiteHe` に同じ関係を記録します。入力の `H_n(x)` は物理学規約、`He_n(x)` は確率論規約へそれぞれ接続します。

自然数次数n≥1と任意の実数xについて、

\[
\frac{d}{dx}\operatorname{He}_n(x)=n\operatorname{He}_{n-1}(x),
\qquad
\frac{d}{dx}H_n(x)=2nH_{n-1}(x)
\]

を `hermiteHe_derivative`、`hermiteH_derivative` で証明します。まずmathlibの多項式の再帰定義から形式微分の次数降下を帰納法で示し、`Polynomial.hasDerivAt_aeval` を用いて実微分に移します。Hの公式は上記スケーリングと合成関数の微分から導きます。`hasDerivAt_hermiteHe_succ` と `hasDerivAt_hermiteH_succ` は次数n+1での微分可能性を含む補題です。

初期値と物理学規約の漸化式も公開します。

\[
\operatorname{He}_0(x)=1,\quad \operatorname{He}_1(x)=x,
\qquad H_0(x)=1,\quad H_1(x)=2x,
\]
\[
H_{n+1}(x)=2xH_n(x)-2nH_{n-1}(x),\qquad n\ge1.
\]

補題名は `hermiteHe_zero`、`hermiteHe_one`、`hermiteH_zero`、`hermiteH_one`、`hermiteH_recurrence` です。全自然数nに対する後続次数形は `hermiteHe_succ_succ`、`hermiteH_succ_succ` にあります。Lean補題を組み合わせると `H_2(x)=4x²−2` も導出できます。CLIの値レシピは0・1次に対応します。

CLIの代表入力は `D_x(H_n(x))=2*n*H_{n-1}(x); n natural,n>=1,x real` です。次数の入力範囲は0〜1000の自然数リテラル、n、n+k、n−kで、kは0〜12です。n−kを含む入力はn≥kを導く元条件を確認します。Leanでは次数を `ℕ`、係数中のnを実数へのキャストとして扱い、減算の下限と微分公式の正次数条件をそれぞれ検査します。

## 実誤差関数とGaussian有限区間積分

`SpecialFunctionProofAgent/Erf.lean` の公開定義 `erf : ℝ → ℝ` は

\[
\operatorname{erf}(x)=\frac{2}{\sqrt\pi}\int_0^x e^{-t^2}\,dt
\]

です。実指数関数 `Real.exp` と向き付き `intervalIntegral` を使用します。Gaussianの連続性から任意の有限実区間での可積分性を得て、積分の基本定理に接続します。任意の実数xについて

\[
\operatorname{erf}'(x)=\frac{2}{\sqrt\pi}e^{-x^2},
\qquad \operatorname{erf}(0)=0,
\qquad \operatorname{erf}(-x)=-\operatorname{erf}(x)
\]

を `deriv_erf`、`erf_zero`、`erf_neg` で証明します。`hasDerivAt_erf` は全実数での微分可能性も与えます。奇関数性の証明にはGaussianの偶関数性と積分方向の反転を使います。

任意の実数端点a,bに対して、`gaussian_integral` は

\[
\int_a^b e^{-t^2}\,dt
=\frac{\sqrt\pi}{2}\bigl(\operatorname{erf}(b)-\operatorname{erf}(a)\bigr)
\]

を与えます。a<b、a=b、a>bの各場合を同じ向き付き積分で扱います。証明は0を基点とする2つの積分の差、erfの定義、`Real.pi_pos` から得る√πの非零性を使います。

代表入力は `D_x(erf(x))=2/sqrt(pi)*exp(-x^2); x real` と `int(a,b,exp(-t^2),t)=sqrt(pi)/2*(erf(b)-erf(a)); a real,b real` です。これらの例は、実数型の宣言のみを条件として全域を検査します。

## Legendre・Laguerre・Jacobi

自然数次数nと実数の引数xを使います。一般化Laguerreのα、Jacobiのα,βは有限多項式の定義で全実数を扱い、通常のLaguerreはα=0です。微分公式はn≥1の条件で次数を1下げ、Laguerreはα、Jacobiはα,βをそれぞれ1増やします。微分変数以外のパラメータを固定して適用します。定義・正規化・正確な補題と直交性へ進む際の条件は[専用仕様](orthogonal-polynomials.md)に記載しています。

両経路で検証する公開入力は、次の `.txt` と同名の `.target.json` です。

- Legendre：`legendre-parity`、`legendre-zero`、`legendre-one`、`legendre-two`、`legendre-right`、`legendre-left`。全自然数での偶奇性・両端値と0〜2次の値です。
- Laguerre：`laguerre-zero`、`laguerre-one`、`laguerre-two`、`ordinary-laguerre-one`、`ordinary-laguerre-two`、`laguerre-derivative`。全実パラメータの低次数値、通常規約の値とn≥1の微分です。
- Jacobi：`jacobi-zero`、`jacobi-one`、`jacobi-two`、`jacobi-derivative`、`jacobi-legendre`。全実パラメータの低次数値、n≥1の微分、全自然数でのα=β=0からLegendreへの特殊化です。

## 正実軸の非整数Bessel Y

`SpecialFunctionProofAgent/BesselY.lean` は既存の `Complex.besselJ` を正実軸で実数値へ接続し、標準のJによる接続式から `besselYNoninteger` を定義します。x>0、sin(πa)≠0の条件で、次数反転・漸化式・微分・Bessel微分方程式を証明します。[標準定義、条件付き整数極限、残る接続](bessel-y-formalization.md)を参照してください。

CLIは `YNoninteger(order,x)` の明示名を使い、固定次数−1/2・1/2・3/2とx>0で次の2式をdirect/stepsの両経路へ接続します。

```text
YNoninteger(-1/2,x)+YNoninteger(3/2,x)=YNoninteger(1/2,x)/x; x>0
D_x(YNoninteger(1/2,x))=(YNoninteger(-1/2,x)-YNoninteger(3/2,x))/2; x>0
```

公開例は `examples/yhalf-recurrence.txt` と `examples/yhalf-derivative.txt` です。半整数での正弦の非零性はLeanで証明し、入力からはx>0を確認します。元の全命題と公理監査が通れば `proved`、`full_function_proof: true`、`full_bessel_proof: true` を保存します。

## 証明の接続・監査と現在の範囲

`classical.py`、`orthogonal.py`、`bessel_y_formal.py` は関数規約、微分変数、次数、パラメータ、積分端点、係数を含む等式構造を照合し、対応する公開Lean補題を選びます。`real_special.py` は元の全変数・全仮定・左右辺から対象定理を生成します。directとstepsは同じ固定対象を検査し、stepsでは各等式の端点連結も確認します。

追加関数の公開定義と定理は固定Lean/mathlibでコンパイルし、`#print axioms` を実行しました。依存公理は `propext`、`Classical.choice`、`Quot.sound` です。生成証明もこの許可集合で監査し、元入力・証明ソース・規約・環境の同一性を再検証時に確認します。数学的対象の登録表には、H/Heの区別、自然数次数、多項式のパラメータ規約、erfの正規化、非整数Yの定義と次数範囲、微分変数と積分方向を含めます。

v2の完全証明経路は上記の登録公式と実数環の整理を対象とします。Hermiteは自然数次数・実引数、erfは実引数の微分・初期値・奇関数性・Gaussian有限区間積分を扱います。複素erf、erfc、誤差関数の近似式・近似誤差の評価、Gaussianの一般変形や無限区間公式は追加の定義・補題・レシピを要する範囲です。数値診断は既存mpmathによる有限標本、条件の残差、差の候補、計算できなかった理由を記録します。Hermiteの数値計算は次数0〜40・引数の絶対値60以下を対象とし、範囲外では理由を保存します。近似誤差の厳密な区間評価は今後の対象です。

従来の `Y_n`・`Y(order,x)` と交差積Xは正実数の数値診断、解析テンプレート、条件付き代数証明に対応し、元の全命題の状態は `unresolved`、`full_bessel_proof: false` です。整数Yの標準次数微分による定義と、±整数次数でのJの微分可能性を前提とする極限補題を公開しています。残る義務はこの次数微分可能性、次数と引数の微分交換、正規化したWronskian、正エネルギー積分と分母非零性の証明です。一般積分の収束、複素枝、極での式の扱いにも、それぞれ対応する条件確認と証明が必要です。

## 引き継いだBessel v1の基盤

# 数学的対象と検証範囲

CLIの形式証明経路（schema version 1）の対象は第1種ベッセル関数の整数次数と固定有理数次数である。整数次数のLean公開定義は
`BesselProofAgent.J (n : ℤ) (x : ℝ) : ℂ` とし、
`Complex.besselJ (n : ℂ) (x : ℂ)` に接続している。
CLIの等式判定は基底の `∀ (n : ℤ) (x : ℝ), 0 < x → lhs = rhs` に、入力されたスカラー比較の追加条件を明示して行い、
関数値の等式は複素数体で検証する。

## 固定したライブラリ

- Lean: `leanprover/lean4:v4.34.0`
- mathlib: `db00fb3901b1bb4954f8a2373285959a5930bbfa`
- 上流モジュール: `Mathlib.Analysis.SpecialFunctions.Bessel`
- プロジェクトの公開 import: `BesselProofAgent`

このコミットは mathlib に Bessel モジュールが追加された版である。
同リポジトリの `lean-toolchain` に合わせて Lean の版を固定した。
mathlib の `v4.34.1` タグでは Bessel モジュールの存在を確認できなかったため、
コミットを直接指定している。依存ライブラリの版は `lake-manifest.json` に記録する。

上流の定義は、正則化超幾何関数を用いた

\[
J_a(z)=(z/2)^a\,{}_0\widetilde F_1(;a+1;-(z/2)^2)
\]

に基づく。`regularizedHGFun` が、ガンマ関数による正則化を含む
超幾何関数を直接定義し、負の整数次数も扱う。

出典:
[mathlib の Bessel モジュール](https://github.com/leanprover-community/mathlib4/blob/db00fb3901b1bb4954f8a2373285959a5930bbfa/Mathlib/Analysis/SpecialFunctions/Bessel.lean)

## コンパイル済みの恒等式

`BesselProofAgent/Basic.lean` には、任意の `n : ℤ`、`x : ℝ` について次を証明した。

- `argument_neg`: `J n (-x) = (-1 : ℂ) ^ n * J n x`
- `order_neg`: `J (-n) x = (-1 : ℂ) ^ n * J n x`
- `order_argument_neg`: `J (-n) x = J n (-x)`
- `double_neg`: `J (-n) (-x) = J n x`
- `recurrence_zero`: `J (-1) x + J 1 x = (2 * (0 : ℂ) / (x : ℂ)) * J 0 x`

最初の2式は、上流の `Complex.besselJ_int_neg` と
`Complex.besselJ_neg_int` から導出する。次数0の漸化式は、次数1の反転公式で証明する。
`sign_cancel` と `sign_mul_self` は整数指数の符号因子を整理する補題である。

反証例 `J n x + 1 = J n x` については、各点での否定 `add_one_ne` と、
`x > 0` 上の全称命題の否定 `not_forall_add_one` を証明した。
全称命題の反証では `n = 0, x = 1` を代入し、加法の消去律で矛盾を導く。
ベッセル関数値の数値近似は用いない。

## 一般3項漸化式の形式証明

`Recurrence.lean` は、任意の複素次数 `a`、非零複素引数 `z` について

\[
J_{a-1}(z)+J_{a+1}(z)=\frac{2a}{z}J_a(z)
\]

を証明する。整数次数・実引数 `x > 0` 用には `recurrence` を公開している。
固定したmathlibには専用の漸化式補題がないため、正則化超幾何級数から導出した。

1. `gamma_inv_step`: `1/Gamma(a)=a/Gamma(a+1)` を `a=0` も含めて証明。
2. `hg_coeff_zero`、`hg_coeff_succ`: 正則化 `₀F₁` の級数係数の隣接関係を証明。
3. `hg_hasSum`: 上流の全域収束級数を `HasSum` に接続。
4. `hg_contiguous`: 係数関係を級数の和に移し、
   `H(a,z)=a H(a+1,z)+z H(a+2,z)` を証明。
5. `bessel_recurrence`: Bessel定義の複素冪因子を整理。

## 微分と定積分

`Derivative.lean` では `(k+1) C_a(k+1)=C_{a+1}(k)` を証明し、
`FormalMultilinearSeries.derivSeries` に接続して `H'_a=H_{a+1}` を得る。
積と合成の微分から、`z ∈ Complex.slitPlane` を条件として

\[
J'_a(z)=\frac{a}{z}J_a(z)-J_{a+1}(z)
       =\frac{J_{a-1}(z)-J_{a+1}(z)}2
\]

を証明する。`RealCalculus.lean` の `deriv_bessel_real` は任意の複素次数と
正の実引数を扱い、`deriv_J`、`deriv_J_symmetric` は整数次数向けの補題である。

`Calculus.lean` は整数次数の実解析性、微分・積分の次数反転公式、
任意の実数端点についての

\[
\int_a^b J'_n(t)\,dt=J_n(b)-J_n(a)
\]

を証明する。さらに `RealCalculus.lean` では漸化式と微分公式から
`(x J_1(x))'=x J_0(x)` を導き、`x > 0` のもとで

\[
\int_0^x tJ_0(t)\,dt=xJ_1(x)
\]

を証明する。端点0は原始関数の連続性と値を使い、開区間の微分から
積分の基本定理を適用している。

## 非整数次数と可積分性

`NonintegerCalculus.lean` は固定有理数次数の微分を公開し、正の両端点の
区間全体で微分可能性・被積分関数の可積分性を証明してFTCへ接続する。

\[
\int_l^u \left(\frac{a}{t}J_a(t)-J_{a+1}(t)\right)dt
=J_a(u)-J_a(l),\qquad l>0,\ u>0.
\]

Lean補題の次数aは任意の複素数で、CLIの具体例はa=1/2、l=1、u=xである。
さらにsqrtの微分と三項漸化式を使い、

\[
\int_1^x\sqrt t\,J_{-1/2}(t)dt
=\sqrt x\,J_{1/2}(x)-J_{1/2}(1),\qquad x>0
\]

を証明した。両端点が正であることから積分区間の正値性を確保する。

`SingularIntegrals.lean` では、実数冪を用いた原点の特異例

\[
\int_0^x t^{-1/2}dt=2\sqrt x
\]

と実・複素埋め込みの可積分性を証明した。負の指数はReal.rpowの意味であり、
CLIの数学的な積分領域の確認にもこの可積分性を使用する。
`not_intervalIntegrable_inv` はx>0で1/tが[0,x]上可積分でないことを示す。
非可積分な関数の全域化積分値を通常の積分恒等式として受理しないよう、
入力検査はこの特異例を拒否する。

## Bessel関数を含む原点特異積分

`OriginSingularBessel.lean` は、x>0における

\[
\int_0^x t^{1/4}J_{-3/4}(t)\,dt=x^{1/4}J_{1/4}(x)
\]

を証明する。右辺の原始関数は0で右極限0を持ち、左辺の被積分関数のノルムは
正側から原点に近づくと∞へ発散する。可積分性を以下の構成で証明してからFTCを使う。

1. `real_weighted_bessel_eq` は正の実引数で、実数冪とBessel関数の積を
   `t^(p+a)` と連続な正則化超幾何因子に分解する。
2. `hasDerivAt_rpow_mul_bessel` は任意の実次数aについて
   `(t^a J_a(t))'=t^a J_(a-1)(t)` を正の引数上で証明する。
3. `origin_weighted_bessel_factor` は被積分関数を `t^(-1/2)` と
   連続因子に分解する。冪の可積分性から `intervalIntegrable_origin_weighted_bessel` を得る。
4. `tendsto_origin_weighted_bessel_primitive` は原始関数の右極限0を証明する。
   `tendsto_norm_origin_weighted_bessel` はGamma(1/4)の非零性を使って被積分関数のノルムの発散を証明する。
5. `integral_origin_weighted_bessel` は可積分性と端点極限を持つFTCを適用する。

LeanのBessel定義での原点の値は0であり、`origin_weighted_bessel_zero` に記録する。
特異性の主張は正側からの極限についてである。
CLIは `t^(1/4)*J_{-3/4}(t)`、下端0、上端xの組を構造で認識し、
検証証明に `intervalIntegrable_origin_weighted_bessel x hx` を必ず含める。
`x^a J_a` の一般微分補題はLean APIで利用でき、CLIの原点積分は上記の具体次数を扱う。

## 第2種Yと交差積の診断経路

従来の診断用schema version 2では複数の実変数、J・Y、および
`X_nm(s,t) = J_n(s)*Y_m(t) - Y_n(s)*J_m(t)` を入力し、関数値の根・非零条件を保持する。
整数Yの次数微分による定義から、標準の引数微分・Wronskian・積分公式を接続する工程が残っており、
元命題の判定は `unresolved`、定義域条件の追加確認が必要な場合は `needs_conditions` とする。
証拠は自然言語解析、条件付きLean証明、数値診断に分けて記録する。

`examples/cross-product-root.txt` は、`0 < lambda < 1`、`z > 0`、
`X_01(z,lambda*z) = 0` を仮定する分数恒等式である。
`A = X_00(z,lambda*z)`、`B = X_11(z,lambda*z)`、
`C = X_02(z,lambda*z)`、`Q = X_01(z,z)` と置くと、対象式は

\[
\frac{A^2}{Q^2+\lambda^2 AC}
=\frac{1}{\lambda}\frac{A}{B-\lambda A}
\]

となる。根の条件と漸化式から `C = -A`、Wronskianと交差積の行列式から
`lambda*A*B = Q^2` と `Q = -2/(pi*z) != 0` を得る。
`u(t) = X_00(z,t)` のBessel方程式と端点の値を使うと、

\[
Q^2-\lambda^2 A^2
=\frac{2}{z^2}\int_{\lambda z}^{z}t\,u(t)^2\,dt>0.
\]

これにより両分母の非零性が従い、約分して対象式を得る。
生成する条件付きLean証明は `0 < lambda`、`Q != 0`、`C = -A`、
`lambda*A*B = Q^2`、`0 < Q^2-lambda^2*A^2` を前提にした代数定理を検査する。
自然言語解析のBessel関数・微分方程式・正の積分からこれらの前提を導く部分を、
元命題の形式化で残る検査義務として記録する。
この解析と条件付き証明は、対応する式と全条件を構造で認識した場合に生成する。

既存の `mpmath` が使える場合は有限個の標本を数値評価し、根の近似、条件の残差、
対象式の差、評価できなかった標本の理由を保存する。根の数値近似と式の一致は数値診断として扱う。
数値バックエンドがない場合も、条件付きLeanと解析の結果を独立に保存する。

## 数学ライブラリと入力インターフェイスの対応

Leanの漸化式は任意の複素次数を扱う。schema version 1のCLIは整数式と固定有理数次数を入力し、
等式の変数を整数 `n` と正の実数 `x` に固定する。
非整数次数の引数は正と確認できる式に限定する。
微分公式の複素版は分岐領域上で、CLIは正の実引数上で利用する。
積分は、整数次数のJと多項式など、区間内の正則性を入力構造から確認できる式を受理する。

実数の有理数冪・平方根は正の底を確認し、値を複素数へ埋め込む。
追加条件はxまたはnと固定有理数との比較・等値・非零条件である。
有理数区間と除外点を使い、x>0およびnの整数性との両立を入力時に検査する。
等値条件と同じ一次等式を主張する入力は確認待ちとする。
条件を満たす整数nと有理数xの候補を選び、反証時にも全条件をLeanで検査する。
外側xの条件は、積分の束縛変数には引き継がない。
除算・負冪には分母・底の非零確認が必要である。
固定した上下界・等値・非零条件から確認できる式を受理し、追加条件が必要な式は
`needs_conditions` とする。数値診断で見つけた差は `unresolved` の反例候補として保存する。

## 検証方法

- `lake build`: 公開定義と全補題をコンパイルする。
- `lake env lean BesselProofAgent/Examples.lean`: CLI 向けの固定された証明手順で、
  引数反転、次数反転、同時反転、段階的な符号反転の積、および誤った等式の両向きの反証を確認する。
- `#print axioms`: 主要補題の依存公理を確認する。
  出力は Lean/mathlib の標準公理 `propext`、`Classical.choice`、`Quot.sound` のみであった。

全補題は証明項を伴う。判定には未証明の追加公理や数値的な一致を採用しない。
