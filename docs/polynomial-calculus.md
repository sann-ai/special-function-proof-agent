# Legendre の隣接直交と多項式の三項漸化式

自然数次数の標準 Legendre と、全実パラメータの一般化 Laguerre に対して、三項漸化式を利用できます。Legendre には区間 `[-1,1]` 上の隣接次数の直交積分もあります。いずれも [既存の標準規約と有限和](orthogonal-polynomials.md) から Lean で証明した公式です。

## Legendre の三項漸化式

`n : ℕ`、`n ≥ 1`、`x : ℝ` に対して

\[
(n+1)P_{n+1}(x)=(2n+1)xP_n(x)-nP_{n-1}(x)
\]

が成立します。公開定理は `SpecialFunctionProofAgent.legendreP_recurrence (n : ℕ) (x : ℝ) (hn : 1 ≤ n)` です。

証明では、mathlib の `Polynomial.shiftedLegendre` の係数

\[
(-1)^k\binom nk\binom{n+k}{n}
\]

に二項係数の恒等式を適用し、多項式の各係数を比較します。その多項式を `(1-x)/2` で実評価して、既存の `legendreP` に接続します。標準規約 `P₀(x)=1`、`P₁(x)=x`、`P₂(x)=(3x²-1)/2` を保ちます。

低次数から次の次数を求める式として使えます。`n=1` では `2P₂(x)=3xP₁(x)-P₀(x)` です。

入力例：

```text
(n+1)*P_{n+1}(x)=(2*n+1)*x*P_n(x)-n*P_{n-1}(x); n natural,n>=1,x real
```

## Legendre の隣接次数の直交積分

全自然数 `n` に対して

\[
\int_{-1}^{1}P_n(t)P_{n+1}(t)\,dt=0
\]

が成立します。公開定理は `SpecialFunctionProofAgent.legendreP_adjacent_integral (n : ℕ)` です。`continuous_legendreP (n : ℕ)` は全実数上の連続性を提供します。

既存の鏡映公式 `Pₙ(-t)=(-1)ⁿPₙ(t)` により、隣接次数の積は奇関数です。区間積分の変数反転と符号反転から積分値を求めます。`n=0` では `P₀(t)P₁(t)=t` に対応します。

この公開レシピは次数 `n` と `n+1`、区間 `[-1,1]`、積分変数を共通に持つ積を扱います。任意の異なる2次数の直交性と、規格化積分 `∫₋₁¹Pₙ(t)²dt=2/(2n+1)` は、後続の定理として整備する範囲です。

入力例：

```text
int(-1,1,P_n(t)*P_{n+1}(t),t)=0; n natural
int(-1,1,P_0(t)*P_1(t),t)=0
```

`t` は積分の束縛変数です。積の一方を自由変数 `x` の関数に変えた式は別の命題になります。区間 `[-1,2]` や `[0,1]` の零積分候補も、指定された端点を保って検査します。

## 一般化 Laguerre の三項漸化式

`n : ℕ`、`n ≥ 1`、`a,x : ℝ` に対して

\[
(n+1)L_{n+1}^{(a)}(x)
 =(2n+a+1-x)L_n^{(a)}(x)-(n+a)L_{n-1}^{(a)}(x)
\]

が成立します。公開定理は `SpecialFunctionProofAgent.laguerreL_recurrence (n : ℕ) (a x : ℝ) (hn : 1 ≤ n)` です。通常 Laguerre は `a=0` に対応します。

証明は既存の有限和の係数

\[
\frac{(a+k+1)_{n-k}}{(n-k)!\,k!}
\]

と上昇階乗の恒等式を使います。次数を超える係数を零として多項式恒等式を示し、`-x` で評価した値を `laguerreL` の公開有限和に接続します。分母の整理は自然数の階乗と正の自然数差を用いるので、`a=-1,-2,…` を含む全実パラメータで公式が成立します。

入力例：

```text
(n+1)*Laguerre(n+1,a,x)=(2*n+a+1-x)*Laguerre(n,a,x)-(n+a)*Laguerre(n-1,a,x); n natural,n>=1,a real,x real
(n+1)*Laguerre(n+1,a,x)=(2*n+a+1-x)*Laguerre(n,a,x)-(n+a)*Laguerre(n-1,a,x); n natural,n>=1,a=-2,x real
```

漸化式は実数値の等式なので、共通の実引数に `y+z` を使う場合や、Laguerre のパラメータと引数をともに `x` とする場合も、代入した値を保って検査できます。

## 検証経路と次数条件

登録レシピは `legendre_recurrence`、`legendre_adjacent_integral`、`laguerre_recurrence` です。`direct` と `steps` の両経路に対応し、命題の左右反転にも対応します。漸化式の `n-1` には自然数次数の下限が必要です。`n>=1` と `n>0` は同じ正の自然数次数を指定します。隣接直交の次数は `n=0` を含みます。

次の例は、同じ固定命題を両経路で検査し、保存した証拠を再検査します。

```sh
mkdir -p runs
cat > runs/adjacent-input.txt <<'EOF'
int(-1,1,P_n(t)*P_{n+1}(t),t)=0; n natural
EOF
python3 -m special_function_agent verify runs/adjacent-input.txt --route direct --output runs/adjacent-direct
python3 -m special_function_agent verify runs/adjacent-input.txt --route steps --output runs/adjacent-steps
python3 -m special_function_agent replay runs/adjacent-steps
```

出力先には新しいディレクトリを指定します。数値診断には既存 mpmath を利用します。mpmath がない環境では `backend_unavailable` を記録し、Lean による証明検査と replay を実行します。

数学実装は [LegendreCalculus.lean](../SpecialFunctionProofAgent/LegendreCalculus.lean) と [LaguerreRecurrence.lean](../SpecialFunctionProofAgent/LaguerreRecurrence.lean) にあります。Lean 4.34.0・固定 mathlib で、上記の公開4定理の依存公理 `propext`・`Classical.choice`・`Quot.sound` を検査しています。

```sh
lake build
python3 scripts/audit_special_functions.py
python3 -m unittest discover -s tests -p 'test_polynomial_calculus.py' -v
SF_RUN_LEAN_TESTS=1 python3 -m unittest discover -s tests -p 'test_polynomial_calculus.py' -v
```

受入検査には3公式の両経路と replay、負の Laguerre パラメータ、次数条件、束縛変数と自由変数、係数・添字・区間端点を変更した候補を含みます。
