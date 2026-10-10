# Legendre・Laguerre・Jacobi 多項式

この実装は、自然数次数の標準 Legendre、多項式として全実パラメータへ拡張した一般化 Laguerre・Jacobi を扱います。Lean の定義、入力 AST、数値評価、保存記録で同じ規約を使います。微分公式では次数を `n ≥ 1` とし、実パラメータを固定して実変数 `x` で微分します。

## 標準 Legendre の規約

`SpecialFunctionProofAgent.legendreP (n : ℕ) (x : ℝ)` は、mathlib の整数係数多項式 `Polynomial.shiftedLegendre n` を `(1-x)/2` で実評価したものです。mathlib 側の一次式は `1-2t` なので、変数変換は

\[
P_n(1-2t)=\operatorname{aeval}_t(\mathrm{shiftedLegendre}_n)
\]

となります。この等式を `legendreP_shifted` で証明しています。さらに有限和

\[
P_n(x)=\sum_{k=0}^{n}\binom nk\binom{n+k}{n}
  \left(\frac{x-1}{2}\right)^k
\]

を `legendreP_finite_sum` で導いています。正規化の確認式は

\[
P_0(x)=1,\qquad P_1(x)=x,\qquad
P_2(x)=\frac{3x^2-1}{2}.
\]

それぞれ `legendreP_zero`、`legendreP_one`、`legendreP_two` に対応します。全自然数次数について、鏡映と端点

\[
P_n(-x)=(-1)^n P_n(x),\qquad P_n(1)=1,\qquad P_n(-1)=(-1)^n
\]

を `legendreP_neg`、`legendreP_at_one`、`legendreP_at_neg_one` で証明しています。実引数の符号条件はありません。

## 一般化 Laguerre と通常 Laguerre

上昇階乗を `(z)_0=1`、`(z)_m=z(z+1)\cdots(z+m-1)` とします。実装では既存の `ascPochhammer ℝ m` の実評価を用います。

`SpecialFunctionProofAgent.laguerreL (n : ℕ) (α x : ℝ)` は、[DLMF 18.5.12](https://dlmf.nist.gov/18.5.E12) の有限和

\[
L_n^{(\alpha)}(x)=\sum_{k=0}^{n}
 \frac{(\alpha+k+1)_{n-k}}{(n-k)!\,k!}(-x)^k
\]

で定義します。分母は自然数の階乗なので、`α=-1,-2,…` を含む全実数で値が定まります。`laguerreL_finite_sum` はこの標準形を公開します。通常の `L_n(x)` は `L_n^{(0)}(x)` として入力を正規化します。

低次数の公式は

\[
L_0^{(\alpha)}(x)=1,\qquad L_1^{(\alpha)}(x)=\alpha+1-x,
\]
\[
L_2^{(\alpha)}(x)=
 \frac{x^2-2(\alpha+2)x+(\alpha+1)(\alpha+2)}2.
\]

通常規約では `L₁(x)=1-x`、`L₂(x)=(x²-4x+2)/2` です。`laguerreL_zero`、`laguerreL_one`、`laguerreL_two` が低次数を扱います。

`n ≥ 1` での微分公式

\[
\frac{d}{dx}L_n^{(\alpha)}(x)=-L_{n-1}^{(\alpha+1)}(x)
\]

は `laguerreL_derivative` に対応します。有限和を項別微分し、係数の階乗を整理して証明します。この公式は [DLMF 18.9.23](https://dlmf.nist.gov/18.9.E23) の規約と一致します。`hasDerivAt_laguerreL_succ` は微分可能性を含む次数 `n+1` の形です。

Lean には原点値 `L_n^{(α)}(0)=(α+1)_n/n!` と `L_n^{(0)}(0)=1` もあります。CLI の専用レシピは低次数、微分公式、n≥1での三項漸化式を対象にします。[漸化式と隣接直交の仕様](polynomial-calculus.md)を参照してください。

## Jacobi と Legendre への特殊化

`SpecialFunctionProofAgent.jacobiP (n : ℕ) (α β x : ℝ)` は、[DLMF 18.5.7](https://dlmf.nist.gov/18.5.E7) の有限和

\[
P_n^{(\alpha,\beta)}(x)=\sum_{k=0}^{n}
 \frac{(n+\alpha+\beta+1)_k(\alpha+k+1)_{n-k}}
      {k!\,(n-k)!}
 \left(\frac{x-1}{2}\right)^k
\]

で定義します。`jacobiP_finite_sum` が定義の標準形を公開します。`α`、`β`、`x` は全実数で、パラメータによって最高次係数が消える場合も同じ有限和を使います。

低次数は

\[
P_0^{(\alpha,\beta)}(x)=1,\qquad
P_1^{(\alpha,\beta)}(x)=
 \frac{\alpha-\beta+(\alpha+\beta+2)x}{2},
\]
\[
P_2^{(\alpha,\beta)}(x)=
 \frac{(\alpha+1)(\alpha+2)}2
 +(\alpha+\beta+3)(\alpha+2)\frac{x-1}{2}
 +\frac{(\alpha+\beta+3)(\alpha+\beta+4)}2
   \left(\frac{x-1}{2}\right)^2.
\]

`jacobiP_zero`、`jacobiP_one`、`jacobiP_two` が対応します。

`n ≥ 1` で

\[
\frac{d}{dx}P_n^{(\alpha,\beta)}(x)
 =\frac{n+\alpha+\beta+1}{2}
   P_{n-1}^{(\alpha+1,\beta+1)}(x)
\]

を `jacobiP_derivative` で証明します。有限和の項別微分と上昇階乗・階乗の係数恒等式を用います。[DLMF 18.9.15](https://dlmf.nist.gov/18.9.E15) と同じ係数・パラメータ移動です。`hasDerivAt_jacobiP_succ` は微分可能性を含む形です。

全自然数 `n`、全実数 `x` について

\[
P_n^{(0,0)}(x)=P_n(x)
\]

を `jacobiP_zero_zero` で証明しています。上昇階乗を階乗と二項係数へ変換し、Legendre の有限和と各係数を一致させます。低次数 `0,1,2` についても個別の橋渡し定理を設けています。

Lean の右端点値 `P_n^{(α,β)}(1)=(α+1)_n/n!` は `jacobiP_at_one` です。現 CLI の専用レシピは低次数・微分・Legendre への特殊化を対象にします。

## 入力と CLI の範囲

入力 AST は schema version 2 を使います。次数の自由変数は `n natural`、実数の自由変数は最大3個です。微分の次数条件を `n>=1` で明示します。自然数の離散性により `n>0`、`n>=1/2`、`n>=0,n!=0` からも同じ下限を確認できます。リテラル次数の入力上限は1000です。負次数と、下限条件を伴わない `n-1` は入力検査で拒否します。

受け付ける族の表記は次のとおりです。

- Legendre：`P_n(x)`、`Legendre(n,x)`。
- 通常 Laguerre：`L_n(x)`、`Laguerre(n,0,x)`。
- 一般化 Laguerre：`L_n^{(α)}(x)`、`Laguerre(n,alpha,x)`。
- Jacobi：`P_n^{(α,β)}(x)`、`Jacobi(n,alpha,beta,x)`。

`α`・`β` と TeX の `\alpha`・`\beta` は ASCII 名 `alpha`・`beta` に揃えます。陪 Legendre `P_n^m` は今回の入力範囲外です。微分変数は `D_x(...)` で指定できます。上記の微分公式はパラメータを固定する場合に適用します。パラメータにも `x` を含む入力は関数全体の微分として翻訳されます。たとえば `Laguerre(1,x,x)=1` なので、その微分を `-1` とする候補は Lean で拒否されます。積分でも、束縛変数は引数・両パラメータに同じ意味で適用されます。

登録レシピは `legendre_values`、`legendre_parity`、`legendre_endpoints`、`laguerre_values`、`laguerre_derivative`、`jacobi_values`、`jacobi_derivative`、`jacobi_legendre` です。各レシピは登録式の AST と両辺を照合し、左右反転にも対応します。`direct` と `steps` は同じ固定された型・全条件・結論を Lean へ渡します。

たとえばリポジトリで次を実行します。

```sh
mkdir -p runs
cat > runs/jacobi-input.txt <<'EOF'
D_x(Jacobi(n,a,b,x))=(n+a+b+1)/2*Jacobi(n-1,a+1,b+1,x); n natural,n>=1,a real,b real,x real
EOF
python3 -m special_function_agent verify runs/jacobi-input.txt \
  --route direct --output runs/jacobi-direct
python3 -m special_function_agent verify runs/jacobi-input.txt \
  --route steps --output runs/jacobi-steps
python3 -m special_function_agent replay runs/jacobi-steps
```

出力先には新しいディレクトリを指定します。ほかの主要入力例は次のとおりです。

```text
P_n(-x)=(-1)^n*P_n(x); n natural,x real
D_x(Laguerre(n,a,x))=-Laguerre(n-1,a+1,x); n natural,n>=1,a real,x real
Jacobi(n,0,0,x)=P_n(x); n natural,x real
P_2(x)=(3*x^2-1)/2; x real
L_2(x)=(x^2-4*x+2)/2; x real
```

証明候補が変更できるのは登録レシピと閉じたステップ計画です。ターゲットの変更・仮定の追加は入力検査で拒否します。微分と積分の束縛変数は Lean への翻訳時にも区別します。

## 検証・数値診断・記録

3族の定理は Lean 4.34.0 と固定 mathlib `db00fb3901b1bb4954f8a2373285959a5930bbfa` で検査します。3族と有限和微分の補助ファイルにある公開28定理について、依存公理は `propext`・`Classical.choice`・`Quot.sound` です。

```sh
lake build
python3 scripts/audit_special_functions.py
python3 -m unittest discover -s tests -p 'test_orthogonal_functions.py' -v
SF_RUN_LEAN_TESTS=1 python3 -m unittest discover -s tests -p 'test_orthogonal_functions.py' -v
```

受入テストは全登録レシピ、主要4式の両経路と replay、低次数規約、負の実パラメータ、自然数次数条件、誤係数・パラメータ移動漏れ・変数捕獲・証拠改変を確認します。数学的な証明状態は固定命題の Lean 検査と標準公理の監査から決めます。

数値診断は既存 mpmath を使い、自然数次数 `0..40`、実引数の絶対値 `60` 以下の有限標本を扱います。Laguerre・Jacobi は上記と同じ有限和を評価し、負の整数パラメータでの多項式延長も保ちます。正パラメータの標本は mpmath の専用関数との比較でも検査します。mpmath がない環境では `backend_unavailable` を記録し、対応する Lean 検査を続けます。

新3族を含む命題は規約 version 3 を使います。Hermite・erf の既存命題は version 2、Gamma・Beta の既存命題は version 1 の同一性を維持します。数学モジュールを追加した環境で旧証拠を利用するときは、保存 request の明示的な再検証を行います。手順は [archive の文書](archive.md) にあります。

## 後続の数学範囲

今回の公開範囲は上記の有限和・低次数・鏡映・端点・微分・特殊化です。直交性は、Legendre の区間 `[-1,1]`、Laguerre の区間 `[0,∞)`・重み `x^α exp(-x)`・`α>-1`、Jacobi の区間 `[-1,1]`・重み `(1-x)^α(1+x)^β`・`α,β>-1` に対する可積分性・直交積分・ノルムを揃える段階で追加します。三項漸化式、微分方程式、零点、複素引数、陪 Legendre は、それぞれ対応する定義と証明を整えた後の拡張範囲です。
