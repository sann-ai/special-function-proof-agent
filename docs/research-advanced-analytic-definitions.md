# 幾何級数・初等積分・非線形と二階の初期値問題

利用者が指定する式について、次の4クラスを登録できます。研究フォルダへ元式・型・束縛・初期条件・正規化式・解析根拠を保存し、Leanで定義根拠を検査します。登録状態は `defined`、その関数を含む検証済み恒等式は `proved` です。

- 幾何級数の有限線形結合。各底の絶対値が1未満であることを証明できる入力形式に対応します。
- 固定有理傾きの `exp`・`sin`・`cos` を組み合わせた有限有向積分。
- `y'=p(t)*sqrt(1+y²)` の全実数上の非線形初期値問題。
- `y''=p(t)` の全実数上の二階初期値問題。位置と速度の初期値を独立に指定します。

`p` は利用者指定の12次以下の多項式です。旧[階乗級数・多項式積分・斉次線形ODE](research-user-analytic-definitions.md)も引き続き利用できます。

## 共通の入力と保存

入力は型付きJSONです。関数の実パラメータは1〜3個、証明targetの自由実変数は最大3個です。内部の和変数・時間・状態・速度は、外側パラメータと異なる安全なASCII名を使います。係数・平行移動・端点・初期値には、内部束縛変数に依存しない既存の有限実式を使えます。追加された有限実演算は `sin`、`cos`、`sinh`、`arsinh` で、Leanの同名実関数に対応します。

Gammaの引数条件や分母非零など、有限実式に必要な条件は元targetの仮定から確認します。係数が相殺して0になる場合も原式と分母を保持し、条件が不足する入力を `needs_conditions` として保存します。

`request.json` は原式と定義snapshot、`analysis.json` と `result.json` は正規化・解析契約・依存情報、`certificate.lean` は原式との橋渡しと固定target、`report.md` は日本語の証明説明を含みます。候補は登録された手順だけを選び、仮定の追加やtargetの置換を行えません。

## A. 一般項を指定する幾何級数

`geometric_series_definition` に自然数添字 `index` と `term` を指定します。和・差・符号反転・添字に依存しない有限係数の乗除で、最大16個の核 `q^k` を組み合わせられます。底は次のどちらかです。

1. 絶対値が1未満の固定有理数。
2. 有限実式 `u` に対する `±u/(1+u²)`。分母の項順交換や `u*u` の平方表記にも対応します。

係数と底の `u` は添字 `k` に依存しません。定義時に各底の絶対値が1未満であること、元一般項との一致、`HasSum` と `Summable` をLeanで証明します。`q=1`、`q=-1`、区間外の定数、制約のない変数をそのまま底にする入力は具体的な未対応理由とともに拒否します。

```json
{
  "op": "geometric_series_definition", "index": "k",
  "term": {
    "op": "pow", "exponent": {"op": "var", "name": "k"},
    "base": {"op": "div", "args": [
      {"op": "var", "name": "x"},
      {"op": "add", "args": [
        {"op": "int", "value": 1},
        {"op": "pow", "base": {"op": "var", "name": "x"}, "exponent": 2}
      ]}
    ]}
  }
}
```

[配布例](../examples/research-advanced-geometric.definition.json)は `q=x/(1+x²)` として

\[
G(a,x)=\sum_{k=0}^{\infty}\left(aq^k+(1-a)(-1/2)^k\right)
=\frac{a}{1-q}+\frac{1-a}{1-(-1/2)}
\]

を検証します。全実数 `a,x` を扱えます。数学モジュールには任意実底と明示した絶対値条件の定理があり、CLIの登録対象は上記の自動証明できる底の形式です。

## B. exp・sin・cosの被積分関数

`elementary_integral_definition` に `var`、`integrand`、`lower`、`upper` を指定します。被積分関数は

\[
\sum_j c_j f_j(a_jt+b_j),\quad f_j\in\{\exp,\sin,\cos\}
\]

の有限線形結合です。項数は最大16、傾き `a_j` は固定有理数です。係数 `c_j`、平行移動 `b_j`、両端点は内部時間に依存しない有限実式です。`exp(t+t+x)` のような入力は一次式へ正規化し、元引数との等式をLeanで証明します。

傾き0では定数関数の原始関数 `t*f(b)`、非零傾きでは通常の原始関数を用います。どちらも任意の有限実端点で連続性・可積分性・原始関数公式を検証し、逆向き区間と同一端点を含みます。

[配布例](../examples/research-advanced-elementary.definition.json)は

\[
E(a,b,x)=\int_a^b\{e^{2t+x}+3\sin(t-x)+\cos x\}\,dt
\]

です。原始関数は `exp(2t+x)/2-3*cos(t-x)+t*cos(x)` です。変数を含む傾き、核同士の積、二次以上の核引数、無限端点はこのクラスの対応範囲外です。

## C. 非線形初期値問題

`nonlinear_ode_definition` は `var`、`state`、`rhs`、`initial_time`、`initial_value`、`arg` を持ちます。右辺を

\[
y'(t)=p(t)\sqrt{1+y(t)^2},\qquad y(t_0)=c
\]

へ正規化できる入力を受け付けます。`sqrt(y*y+1)` の表記も使えます。状態変数はこの平方根の中に現れ、多項式係数は時間と外側の実パラメータに依存します。

`P'=p` となる多項式原始関数を用いて

\[
y(x)=\sinh\bigl(\operatorname{arsinh}(c)+P(x)-P(t_0)\bigr)
\]

を構成します。Leanで微分方程式と初期値を検証し、任意の候補解を `arsinh` で変換して一意性を証明します。解のクラスは、**全実数上の各点で元の微分条件を満たし、指定した実初期時刻で初期値が一致する実関数**です。初期値・初期時刻・評価点は任意実数です。

[配布例](../examples/research-advanced-nonlinear.definition.json)は `y'=(a*t+2)*sqrt(1+y²), y(1)=c` です。平方根以外の状態依存、複数の状態核の積、独立な加法項、有限領域だけの解は後続課題です。

## D. 独立した初期条件を持つ二階方程式

`second_order_ode_definition` はCのフィールドに `velocity` と `initial_derivative` を加えます。

\[
y''(t)=p(t),\qquad y(t_0)=c,\quad y'(t_0)=v_0
\]

について、証拠では位置・速度の組 `(y,v)` を使い、全実数上で `y'=v`、`v'=p(t)` と2個の初期条件を記述します。`HasDerivAt y (v t) t` が各点で成立するため、速度は位置の実微分に一致します。右辺は時間の多項式で、位置・速度への依存は相殺前の入力から検査します。

`P'=p`、`Q'=P` として

\[
v(x)=v_0+P(x)-P(t_0),
\]
\[
y(x)=c+v_0(x-t_0)+Q(x)-Q(t_0)-P(t_0)(x-t_0)
\]

を構成します。両微分条件・両初期値と、**全実数上の各点でこれらを満たす位置・速度の組**の存在一意性をLeanで証明します。

[配布例](../examples/research-advanced-second-order.definition.json)は `y''=t+2, y(1)=c, y'(1)=v0` です。実パラメータ `c,v0,x` により、位置と速度の初期値を独立に指定できます。3階以上、位置・速度に依存する加速度、有限領域だけの解は後続課題です。

## 登録・証明・別命題への再利用

```sh
lake build
lake build SpecialFunctionProofAgent.AnalyticDefinitions SpecialFunctionProofAgent.UserAnalyticDefinitions SpecialFunctionProofAgent.AdvancedAnalyticDefinitions
python3 scripts/doctor.py
python3 -m special_function_agent research function add examples/research-advanced-geometric.definition.json
```

返されたpackageの `id` を `FUNCTION_PACKAGE_ID` に入れます。

```sh
python3 -m special_function_agent research function generate examples/research-advanced-geometric.source.input.json --using FUNCTION_PACKAGE_ID --route direct --output runs/advanced-geometric --archive
python3 -m special_function_agent research add runs/advanced-geometric/attempt-1/verification --name geometric-identity --original-input examples/research-advanced-geometric.source.target.json
```

補題登録で返された `id` を `LEMMA_ID` に入れ、両辺を2倍した別命題に使います。

```sh
python3 -m special_function_agent research generate examples/research-advanced-geometric.derived.target.json --using LEMMA_ID --route steps --output runs/advanced-derived --archive
```

同じ入力・経路・選択補題での再実行は、保存証拠を再検査して `ai_called:false` で再利用します。初回からローカルの既定候補を使う場合は `generate` を `verify` に置き換えます。ローカル `verify` の証拠フォルダは直接補題登録できます。AI生成では成功した `attempt-N/verification` の証拠7ファイルを使い、同居するAIログを登録対象から分けます。

配布ファイル名の `geometric` を `elementary`、`nonlinear`、`second-order` に変えると、各クラスの定義・元target・派生targetを使えます。

私有研究フォルダ、選択export/import、依存順再検証は[研究関数の手順](research-functions.md#私有保存選択共有環境更新)と共通です。今回の証拠には `AdvancedAnalyticDefinitions.lean` と依存解析モジュールのhashを記録します。旧証拠を保持し、環境変更後の明示再検証は新記録を追記します。

## Codexへの依頼例

> `q=x/(1+x²)` として、`G(a,x)=Σ_{k=0}^∞[a*q^k+(1-a)*(-1/2)^k]` を研究関数として登録してください。実数a,xで `G(a,x)=a/(1-q)+(1-a)/(1-(-1/2))` をdirectで証明し、その補題で両辺を2倍した別命題をstepsで検査してください。収束根拠、原式との対応、Lean証明、日本語説明を保存し、履歴から再利用してください。`docs/research-advanced-analytic-definitions.md` と `examples/research-advanced-geometric.*.json` を使ってください。

## 対応外入力の扱い

一般の任意級数の収束判定、上記以外の非多項式積分、非線形方程式全般、3階以上の方程式は、この版の登録範囲外として理由を返します。任意のLeanコード、追加公理、未証明の性質を共有bundleから読み込む経路はありません。数値診断は証明と分けて保存し、mpmathが未導入でも対応するLean検証と保存を継続します。
