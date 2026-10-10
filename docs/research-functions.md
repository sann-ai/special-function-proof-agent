# 明示定義した研究関数を証明に使う

既存の特殊関数・四則演算・有限の合成で表せる実関数を、私有の研究フォルダへ登録できます。たとえば `ShiftedGamma(u)=Gamma(u+1)` を定義し、`x>0` の下で `ShiftedGamma(x)=x*Gamma(x)` を証明します。その証明を研究補題として登録すると、さらに `GammaTail(u)=ShiftedGamma(u+1)` の等式 `GammaTail(x)=(x+1)*x*Gamma(x)` へ使えます。

指数の階乗級数・Gaussian積分・初期時刻0の一次斉次ODEは、[解析的研究定義の3形式](research-analytic-definitions.md) を使います。

定義の登録は `status: defined` です。検査対象は、型の付いたLeanの定義と、その展開等式です。各恒等式の `status: proved` は、元の命題と全条件について別途Lean証明と標準公理監査を通したときに保存します。

## Codexへの最短の依頼

セットアップ済みのこのプロジェクトを開いて依頼します。

> 私の研究用に `ShiftedGamma(u)=Gamma(u+1)` と `GammaTail(u)=ShiftedGamma(u+1)` を実関数として登録してください。`x>0` で `ShiftedGamma(x)=x*Gamma(x)` を直接証明し、その証明を補題にして `GammaTail(x)=(x+1)*x*Gamma(x)` を自然言語ステップ付きでLean検証してください。元の定義と全条件を保存し、証明・依存関係・日本語説明を示し、同じ命題をarchiveから再利用してください。`docs/research-functions.md` の手順を使ってください。

数学的定義、規約、研究条件、共有する範囲は利用者が指定します。Codexはその内容を型付きJSONへ転記し、定義の登録、許可された証明候補、検査、説明の作成を支援します。研究関数名を含む自由なTeX・文字列の読取りは、CodexによるJSON作成の段階で原式と照合します。この版のCLI入力は明示したJSONです。

## 定義形式と初回の検査

`examples/research-function-shifted-gamma.definition.json` は次の形です。

```json
{
  "schema_version": 1,
  "name": "ShiftedGamma",
  "parameters": {"u": "real"},
  "body": {"op": "gamma", "arg": {"op": "add", "args": [
    {"op": "var", "name": "u"}, {"op": "int", "value": 1}
  ]}},
  "definitions": []
}
```

```sh
python3 -m special_function_agent research function add examples/research-function-shifted-gamma.definition.json
python3 -m special_function_agent research function list
```

登録結果には保存packageの `id` と、定義の意味を識別する `definition_id` があります。呼出しASTは `{"op":"defined","function":"DEFINITION_ID","arguments":{"u":...}}` で、全パラメータを名前付きで指定します。定義名が同じでも内容が異なる場合は別IDになります。

上で返された保存packageの `id` を `FUNCTION_PACKAGE_ID` へ入れます。

```sh
python3 -m special_function_agent research function verify examples/research-function-shifted-gamma.input.json --using FUNCTION_PACKAGE_ID --route direct --output runs/defined-direct --archive
python3 -m special_function_agent research function verify examples/research-function-shifted-gamma.input.json --using FUNCTION_PACKAGE_ID --route steps --output runs/defined-steps --archive
python3 -m special_function_agent replay runs/defined-steps
```

`input.json` は元の式・変数・仮定を持ち、選択した定義snapshotと証明候補は検査器が付けます。配布した `target.json` は定義snapshotも含む独立した入力です。新しいAI候補を求める場合は `research function generate` を同じ入力・`--using`・`--route` で呼び、既存のCodex CLI認証を使います。

## 証明を別の命題へ使う

先の直接証明を研究補題に登録します。返されたIDを `LEMMA_ID` とします。

```sh
python3 -m special_function_agent research add runs/defined-direct --name shifted-gamma-recurrence --original-input examples/research-function-shifted-gamma.target.json
python3 -m special_function_agent research function add examples/research-function-gamma-tail.definition.json
python3 -m special_function_agent research generate examples/research-function-gamma-tail.target.json --using LEMMA_ID --route steps --output runs/defined-tail --archive
```

`GammaTail` の定義snapshotは `ShiftedGamma` の定義を依存として含みます。証明では登録補題を `x+1` と `x` に適用し、必要な正値条件を元の `x>0` からLeanで導きます。同じtarget・経路・選択補題で再度 `research generate ... --archive` を実行すると、保存証拠のLean再検査後に `ai_called: false` で再利用できます。

検証結果の `request.json` は元の研究関数呼出しと定義を保持します。`certificate.lean` は依存順の `ResearchFunction_ID` 定義、展開後の `expanded_target`、元の呼出しを含む `target` を持ち、両命題をLeanの定義等式で接続します。`analysis.json` と `result.json` は展開後の命題、元定義ID、適用した補題ID、条件と検査状態を記録します。`report.md` は関数名を使う日本語説明と各等式を示します。

## 私有保存、選択共有、環境更新

保存先は既定で `~/SpecialFunctionProofAgentData/research/functions` です。`--research-dir` または `SPECIAL_FUNCTION_RESEARCH_DIR` で研究rootを指定できます。研究補題はroot直下、関数はその `functions` 内に保存し、本体リポジトリ外で管理します。出典は登録時の `--source`、元定義のJSONは `original_input` に保持します。

```sh
python3 -m special_function_agent research function export FUNCTION_PACKAGE_ID ~/selected-function.json
python3 -m special_function_agent research function import ~/selected-function.json --research-dir ~/SecondResearch
python3 -m special_function_agent research export LEMMA_ID ~/selected-lemma.json
python3 -m special_function_agent research import ~/selected-lemma.json --research-dir ~/SecondResearch
python3 -m special_function_agent research function reverify FUNCTION_PACKAGE_ID
python3 -m special_function_agent research function import ~/selected-function.json --reverify
```

選択した関数packageには必要な依存定義を含みます。補題packageにも、その証明の定義・補題snapshotが入ります。共有前に、同梱される元入力と出典を確認してください。

通常importは環境・規約と再生成Leanの一致を確認して再検査します。環境が変わった場合は明示した `reverify` で定義から検査し直し、新しい保存packageを追記します。意味の `definition_id` と元JSONは保持します。研究補題も `research reverify` で依存順に再検証できます。受け取ったLean文字列は再生成結果との照合に使い、実行する証明は構造化定義・閉じた計画から作ります。

## 配布例をAIなしで再検査

```sh
python3 -m special_function_agent replay demo/defined-gamma-direct
python3 -m special_function_agent replay demo/defined-gamma-steps
python3 -m special_function_agent replay demo/defined-gamma-tail-direct
python3 -m special_function_agent replay demo/defined-gamma-tail-steps
```

## 対応範囲

- 定義は1〜3個の実パラメータ、証明targetは最大3個の自由実変数です。安全なASCII名を使い、関数名と変数・束縛名の衝突を検査します。
- 定義本体は四則演算、自然数冪、実冪、平方根、既存特殊関数の有限合成です。多項式・Besselは既存ASTで認めた固定次数を使います。定数関数と複数パラメータも扱います。
- 定義本体では、[閉じた3形式の解析的定義](research-analytic-definitions.md) を利用できます。一般の微分・積分・無限級数と、微積分を含む関数呼出しの代入式は後続です。外側のtargetに微分・積分がある場合は、その束縛を保って定義を展開します。恒等式の証明には対応する既存レシピまたは検証済み研究補題を使います。
- Gammaの正引数、分母非零などの使用条件は展開後の式で検査し、元の仮定から確認します。数値標本の一致は独立した診断として保存します。mpmath未導入時もLean検査・保存を続けます。
- 依存定義は最大12個・深さ4、入力とpackageは256 KiB以内です。循環、不足した引数、型違い、未知ID、内容改変を拒否します。
- 自由な自然数／整数次数の研究代入、任意の一般項・被積分関数・ODEの指定は後続です。それぞれ型、収束、存在、一意性、規約の根拠を追加する段階で対応します。
