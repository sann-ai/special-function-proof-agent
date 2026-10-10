# 級数・積分・初期値問題による研究関数

指数級数、Gaussian の有限積分、定係数の斉次線形初期値問題を、3 種類の固定した解析定義として登録できます。各定義は元の級数・積分・初期値問題、成立域、標準関数への橋渡し定理を保持します。登録時には展開等式に加え、級数の収束、積分可能性、初期値問題の存在一意性を Lean で検査します。

研究関数の登録状態は `defined`、その関数について検査した恒等式の状態は `proved` です。恒等式は直接証明と自然言語ステップの両経路で扱い、成功した source の証明を研究補題として別の derived target へ適用できます。[研究関数の基本手順](research-functions.md)と[研究補題の保存・適用](research-lemmas.md)も参照してください。

## 3 種類の定義と成立域

### 指数級数

`SeriesExp(u)` は、自然数 `n=0,1,2,…` にわたる級数です。

\[
\operatorname{SeriesExp}(u)=\sum_{n=0}^{\infty}\frac{u^n}{n!}=e^u,
\qquad u\in\mathbb R.
\]

定義本体は `{"op":"exp_series","arg":{"op":"var","name":"u"}}` です。Lean の `exponentialSeries` を使い、`hasSum_exponentialSeries` と `summable_exponentialSeries` が全実数での収束を、`exponentialSeries_eq_exp` が標準指数関数との一致を与えます。

配布例は `examples/research-analytic-exp-series.definition.json` です。source は `SeriesExp(x)=exp(x)`、derived は `2*SeriesExp(x)=2*exp(x)` で、自由変数 `x` は実数です。

### Gaussian の有向有限積分

`GaussianArea(u)` は原点から実数 `u` までの有向積分です。

\[
\operatorname{GaussianArea}(u)=\int_0^u e^{-t^2}\,dt
=\frac{\sqrt\pi}{2}\operatorname{erf}(u),
\qquad u\in\mathbb R.
\]

定義本体は `{"op":"gaussian_primitive","arg":{"op":"var","name":"u"}}` です。`u<0` の場合も積分の向きを `0` から `u` へ保ちます。`u=0` も同じ定義の範囲です。

Lean の `gaussianPrimitive` を使い、`intervalIntegrable_gaussian` が任意の実端点間での積分可能性を、`gaussianPrimitive_eq_erf` が上の規格化を与えます。`hasDerivAt_gaussianPrimitive` は全実数で導関数が `exp(-u²)` となることを証明しています。

配布例は `examples/research-analytic-gaussian-primitive.definition.json` です。source は `GaussianArea(x)=sqrt(pi)/2*erf(x)`、derived は両辺を 2 倍した等式です。

### 斉次線形初期値問題

実値パラメータ `a,c` を固定して、内部の独立変数 `t∈ℝ` に関する次の初期値問題を扱います。

\[
y'(t)=a\,y(t),\qquad y(0)=c.
\]

全実時間で微分可能な解は一意で、その `u` における値を `LinearFlow(a,c,u)` とします。Lean での解の条件は、各実数 `t` での `HasDerivAt y (a*y t) t` と `y 0 = c` です。

\[
\operatorname{LinearFlow}(a,c,u)=c\,e^{au},
\qquad a,c,u\in\mathbb R.
\]

```json
{
  "op": "linear_ivp",
  "rate": {"op": "var", "name": "a"},
  "initial": {"op": "var", "name": "c"},
  "arg": {"op": "var", "name": "u"}
}
```

`rate` と `initial` は、内部時間 `t` を動かす間に固定する実値です。`arg` は解を評価する時刻です。たとえば外側のパラメータに式を代入するときも、3 個の式をそれぞれ評価し、その rate・initial の解を arg で評価します。rate や initial が 0 の場合、負の rate、負の評価時刻も含みます。

Lean の `homogeneousIVPSolution rate initial arg` を使います。`hasDerivAt_homogeneousIVPSolution`、`homogeneousIVPSolution_zero`、`homogeneousIVPSolution_unique`、`existsUnique_homogeneousIVPSolution` が微分方程式・時刻 0 の初期値・一意性・存在一意性を与え、`homogeneousIVPSolution_eq_exp` が閉形式へ接続します。

配布例は `examples/research-analytic-linear-ivp.definition.json` です。source は `LinearFlow(a,c,x)=c*exp(a*x)`、derived は両辺を 2 倍した等式です。自由変数は実数 `a,c,x` の 3 個です。

## 登録、直接証明、ステップ証明

以下は指数級数の例です。登録結果に含まれる保存 package の `id` を `FUNCTION_PACKAGE_ID` に置き換えます。関数呼出しに使う意味の `definition_id` は、配布入力へ埋め込み済みです。

```sh
python3 -m special_function_agent research function add examples/research-analytic-exp-series.definition.json
python3 -m special_function_agent research function verify examples/research-analytic-exp-series.source.input.json --using FUNCTION_PACKAGE_ID --route direct --output runs/analytic-series-direct --archive
python3 -m special_function_agent research function verify examples/research-analytic-exp-series.source.input.json --using FUNCTION_PACKAGE_ID --route steps --output runs/analytic-series-steps --archive
python3 -m special_function_agent replay runs/analytic-series-steps
```

`exp-series` を `gaussian-primitive` または `linear-ivp` に置き換えると、対応する定義と source 入力を使えます。登録した各関数の package ID を選んでください。

各族に 4 個の JSON を用意しています。

- `definition.json`：名前、実パラメータ、解析定義本体。
- `source.input.json`：`research function verify --using` で使う固定命題。
- `source.target.json`：定義 snapshot を含む独立した固定命題。
- `derived.target.json`：source の等式を使って両辺を 2 倍する別命題と定義 snapshot。

snapshot を含む入力をローカルで検査する場合は、通常の `verify` を使えます。

```sh
python3 -m special_function_agent verify examples/research-analytic-gaussian-primitive.source.target.json --route steps --output runs/analytic-gaussian
```

## source を別の target に適用する

先の直接証明を研究補題として登録し、返された保存 ID を `LEMMA_ID` に入れます。

```sh
python3 -m special_function_agent research add runs/analytic-series-direct --name analytic-series-source --original-input examples/research-analytic-exp-series.source.target.json
python3 -m special_function_agent research generate examples/research-analytic-exp-series.derived.target.json --using LEMMA_ID --route direct --output runs/analytic-derived-direct --archive
python3 -m special_function_agent research generate examples/research-analytic-exp-series.derived.target.json --using LEMMA_ID --route steps --output runs/analytic-derived-steps --archive
```

AI 候補は選択した補題 ID、型付き代入式、閉じた証明手順を返します。検査器は source の証明を再生成し、元の仮定を保って derived の等式へ適用します。`research verify --plan ... --using LEMMA_ID` では保存した候補をローカルで再検査できます。同じ target・経路・選択補題で `research generate ... --archive` を再実行すると、保存証拠を Lean で検査して `ai_called: false` で再利用します。

## 保存される数学的根拠

定義 package の `certificate` は、解析定義から閉形式への等式と、対応する収束・積分可能性・存在一意性の命題を含みます。これらをまとめた監査対象について、標準公理のみへの依存を確認します。

恒等式の `certificate.lean` は、元の研究関数呼出しを含む `target` と、閉形式へ展開した `expanded_target` を、固定した橋渡し定理で接続します。`request.json` は元の定義・呼出し・型・全条件を保持し、`analysis.json` と `result.json` は定義 ID、依存定義、原始定義の契約、展開後の命題、適用補題を記録します。`report.md` に日本語の式と検証手順を保存します。

解析定義を使う定義・証明には専用 Lean module の hash を数学環境として追加します。意味の定義 ID と target ID は数学的入力から計算し、環境 hash を含めません。環境更新後は明示した `research function reverify`、研究補題には `research reverify` を使い、固定した定義・命題を再検査して新しい package を追記します。旧 package の内容を保持します。私有保存・選択 export/import の操作は[研究関数の保存手順](research-functions.md#私有保存選択共有環境更新)と共通です。

## Codex への最短の依頼

> `SeriesExp(u)=Σ_{n=0}^∞ u^n/n!` を研究関数として登録してください。全実数 x で `SeriesExp(x)=exp(x)` を direct で証明し、その補題を使って `2*SeriesExp(x)=2*exp(x)` を steps で Lean 検査してください。定義・収束根拠・証明・日本語説明を保存し、archive から再利用してください。入力例と手順は `docs/research-analytic-definitions.md` にあります。

自然言語の依頼は、3 つの明示形式と入力 JSON へ対応付けてから検査します。原始定義の本文には、上に示した固定の級数、積分、初期値問題を使います。

## 入力範囲と検査

- 定義の実パラメータは 1〜3 個、target の自由実変数は最大 3 個です。依存定義は最大 12 個・深さ 4、JSON/package は 256 KiB 以内です。
- 各解析 primitive の引数は既存の有限実式です。primitive の内部に `defined` 呼出し、別の解析 primitive、微分・積分・無限大を置く入力は拒否します。
- 別の有限研究関数が、解析研究関数を `defined` で呼ぶ依存合成に対応します。たとえば `DoubleSeries(v)=2*SeriesExp(v)` は `SeriesExp` の意味 snapshot と解析契約を保持します。
- 一般項・積分関数・積分上下限・内部 binder・初期時刻・方程式を入力フィールドで置き換える形式は拒否します。今回の解析契約は全実数上の上記 3 形式です。
- Gamma の正引数や分母非零など、子の有限式に必要な使用条件は展開後に検査します。条件不足と誤係数は元の入力の検査結果へ反映します。
- 恒等式の検査は、閉形式へ展開した後に既存の証明レシピまたは登録補題を適用できる範囲です。微分・積分を含む任意の変形は後続です。
- 数値診断は証明済みの閉形式を使い、既存 mpmath がある場合に保存します。未導入時も対応する Lean 検査と私有保存を続けます。

焦点テストは次のコマンドで実行できます。

```sh
python3 -m unittest discover -s tests -p 'test_research_analytic.py' -v
SF_RUN_LEAN_TESTS=1 python3 -m unittest discover -s tests -p 'test_research_analytic_integration.py' -v
```
