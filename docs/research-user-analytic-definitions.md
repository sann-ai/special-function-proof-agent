# ユーザーが式を指定する解析定義

一般項を指定する階乗核の有限線形結合、多項式を指定する有限積分、多項式係数を指定する斉次線形初期値問題を登録できます。入力の式・束縛・端点・初期条件を保存し、正規化した式との一致と解析的な成立根拠を Lean で検査します。

登録した関数は `defined`、その関数を使って Lean 検査した恒等式は `proved` として保存します。登録時に収束・可積分性・解の存在一意性の該当証明を検査します。証明に成功した恒等式を研究補題として登録すると、異なる target に適用できます。

## 一般項を指定する級数

`series_definition` に自然数の和変数 `index` と一般項 `term` を指定します。受け付ける一般項は

\[
\sum_{j=1}^{N} c_j\frac{q_j^k}{k!},\quad k=0,1,2,\ldots,\quad N\leq16
\]

の形に正規化できる有限線形結合です。`c_j,q_j` は内部添字 `k` に依存しない有限実式で、実パラメータ、既存関数、四則演算、固定自然冪などを使えます。和・差・符号反転・添字に依存しない係数による乗除を入力できます。

核の JSON は次の形です。

```json
{
  "op": "series_definition", "index": "k",
  "term": {
    "op": "div", "args": [
      {"op": "pow", "base": {"op": "var", "name": "x"},
       "exponent": {"op": "var", "name": "k"}},
      {"op": "factorial", "arg": {"op": "var", "name": "k"}}
    ]
  }
}
```

一般項を Lean の実際の無限和として保持します。入力一般項と有限核和の一致を証明し、全実係数・実核引数での `HasSum` と `Summable` から閉形式 `Σ c_j*exp(q_j)` を得ます。

配布例 `examples/research-user-series.definition.json` は

\[
W(a,x)=\sum_{k=0}^\infty\left(a\frac{x^k}{k!}+(1-a)\frac{(-x)^k}{k!}\right)
=a e^x+(1-a)e^{-x}
\]

です。添字に依存する係数、幾何級数、二つの核の積、異なる添字の階乗、級数の開始番号変更は対応範囲外として拒否します。

## 被積分式と端点を指定する積分

`integral_definition` は `var`、`integrand`、`lower`、`upper` を持ちます。被積分式は内部実変数に関する次数 12 以下の多項式です。加減乗算、固定自然冪、内部変数に依存しない有限実式の係数と、その係数による除算を使えます。

```json
{
  "op": "integral_definition", "var": "t",
  "integrand": {"op": "pow", "base": {
    "op": "add", "args": [{"op": "var", "name": "t"},
                            {"op": "var", "name": "x"}]
  }, "exponent": 2},
  "lower": {"op": "var", "name": "a"},
  "upper": {"op": "var", "name": "b"}
}
```

この配布例 `examples/research-user-integral.definition.json` は

\[
A(a,b,x)=\int_a^b(t+x)^2\,dt=\frac{(b+x)^3-(a+x)^3}{3}
\]

です。`a,b,x` は実数で、`a>b` の向き、同一端点、負の端点も含みます。内部変数 `t` は被積分式だけを束縛し、端点・外側パラメータと区別します。入力式と係数多項式の一致、任意実端点での `IntervalIntegrable`、原始関数の微分と積分公式を Lean で確認します。内部変数を含む分母、非多項式の被積分関数、無限端点はこのクラスの対応範囲外です。

## 方程式と初期条件を指定する ODE

`ode_definition` は内部時間 `var`、状態変数 `state`、右辺 `rhs`、`initial_time`、`initial_value`、評価点 `arg` を持ちます。右辺が

\[
y'(t)=p(t)y(t),\qquad y(t_0)=c
\]

という形へ正規化できる入力を受け付けます。`p` は内部時間に関する次数 12 以下の多項式です。たとえば `(a*t+2)*y` と `a*t*y+2*y` の両方を入力できます。係数・初期時刻・初期値は内部時間と状態に依存しない有限実式です。

`P'=p` となる多項式原始関数から、解を

\[
y(x)=c\exp(P(x)-P(t_0))
\]

と構成します。存在一意性の対象は、**全実数上の各点で `HasDerivAt y (p(t)*y(t)) t` を満たし、指定した実初期時刻で初期値が一致する実関数**です。入力右辺と `p(t)*y` の一致、微分方程式、初期値、積分因子による一意性を証明します。

配布例 `examples/research-user-ode.definition.json` は `y'=(a*t+2)*y, y(1)=c` を指定し、

\[
F(a,c,x)=c\exp\left(\frac{a(x^2-1)}2+2(x-1)\right)
\]

を証明します。任意実初期時刻、初期値 0、負の評価時刻も扱えます。非斉次項、非線形の状態依存、非多項式の時間係数、高階方程式、有限領域だけの解は後続です。

## 登録から別の命題への適用

事前に本体と解析モジュールをビルドします。

```sh
lake build
lake build SpecialFunctionProofAgent.AnalyticDefinitions SpecialFunctionProofAgent.UserAnalyticDefinitions
python3 scripts/doctor.py
```

級数の例を登録し、返された保存 package の `id` を `FUNCTION_PACKAGE_ID` に入れます。意味の `definition_id` は入力例に埋め込まれています。

```sh
python3 -m special_function_agent research function add examples/research-user-series.definition.json
python3 -m special_function_agent research function generate examples/research-user-series.source.input.json --using FUNCTION_PACKAGE_ID --route direct --output runs/user-series --archive
```

AI の候補を使う `generate` の出力では、成功した `attempt-1/verification` が検証証拠です。その証拠を補題登録します。複数回の試行を明示した場合は、成功した試行番号を選びます。

```sh
python3 -m special_function_agent research add runs/user-series/attempt-1/verification --name weighted-series --original-input examples/research-user-series.source.target.json
python3 -m special_function_agent research generate examples/research-user-series.derived.target.json --using LEMMA_ID --route steps --output runs/user-derived --archive
```

`derived.target.json` は先の恒等式の両辺を 2 倍した別命題です。返された補題 ID を `LEMMA_ID` に入れます。同じ target・経路・選択補題で再実行すると、保存証拠を再検査して `ai_called:false` で再利用します。初回からローカルの既定候補を使う場合は `research function verify ... --route direct|steps` に置き換えます。その出力フォルダを直接 `research add` に渡せます。

`series` を `integral` または `ode` に変えると各入力例を使えます。各族に `definition.json`、`source.input.json`、定義 snapshot 付き `source.target.json`、`derived.target.json` があります。

## 元式・定義域・保存の扱い

- 研究関数の実パラメータは 1〜3 個、target の自由実変数は最大 3 個です。内部の自然数添字・実時間・状態変数は外側パラメータと異なる安全な ASCII 名を使います。関数呼出しの同時代入と外側の微積分では、生成した別名で内部束縛を保ちます。
- 係数・核引数・端点・初期値の有限式は、既存関数の有限合成と同じ型検査を通します。内部束縛変数、他の研究関数呼出し、解析定義、微分・積分を係数へ埋め込む形式は拒否します。
- 分母非零、Gamma や既存 Bessel の引数条件などは使用時に元 target の全仮定から確認します。相殺で係数がゼロになっても元の有限式と分母を保持し、条件不足を `needs_conditions` にします。条件を入力へ追加する操作は候補に許可しません。
- `request.json` に原式と定義 snapshot、`analysis.json` と `result.json` に正規化式・解析契約・定義依存を記録します。`certificate.lean` は原式との橋渡しと元 target を含み、`report.md` に日本語の説明を保存します。
- 新モジュール `UserAnalyticDefinitions.lean` の hash は、この機能を使う定義・証明へ追加します。旧保存証拠と旧解析モジュールを保持します。環境更新後の明示再検証は新記録を追記します。
- 私有研究フォルダへの保存、選択 export/import、依存順再検証は[研究関数の手順](research-functions.md#私有保存選択共有環境更新)と共通です。共有物から任意 Lean コードを実行する代わりに、構造化入力から証明を再生成します。

## Codex への依頼例

> `W(a,x)=Σ_{k=0}^∞[a*x^k/k!+(1-a)*(-x)^k/k!]` を自分の研究関数として登録してください。実数 a,x で `W(a,x)=a*exp(x)+(1-a)*exp(-x)` を direct で証明し、その補題で `2*W(a,x)=2*(a*exp(x)+(1-a)*exp(-x))` を steps で検査してください。収束根拠、元式との対応、Lean 証明、日本語説明を保存し、履歴から再利用してください。手順は `docs/research-user-analytic-definitions.md` にあります。
