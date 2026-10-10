# 研究用の補題を別の命題へ使う

既存の関数についてLeanで検査した等式を、リポジトリ外の研究フォルダへ登録できます。登録した補題の実変数へ式を代入し、その仮定を新しい命題の元条件から導いて、別の等式を直接・ステップ両経路で証明します。

たとえば `Gamma(x+1)=x*Gamma(x); x>0` を2回適用し、`Gamma(x+2)=(x+1)*x*Gamma(x); x>0` を証明します。生成Leanには補題IDを含む名前空間と、`x+1`・`x` への適用が現れます。`analysis.json` と `result.json` には元補題のtarget ID・式・条件・出典・証明scopeを記録します。

archiveは同じtargetの候補を検索・再検査して使います。researchは別targetの証明へ補題を適用します。研究経路で得た証明もarchiveへ保存でき、同じtargetを再び求めた際はLean再検査後に `ai_called: false` で再利用します。

## Codexへの依頼

セットアップ済みのこのプロジェクトをCodexで開いて依頼します。

> `examples/gamma-recurrence.txt` をLeanで検証して、補題名 `gamma-step` で私の研究フォルダに登録してください。その補題を使い、`examples/research-gamma-two-step.txt` を直接証明と自然言語ステップの両方で検査してください。元のx>0を保持し、補題をx+1とxへ適用した箇所、各仮定の導出、形式証明と日本語説明を示してください。成功した証拠をarchiveへ保存し、同じ式をAI再呼出しなしで再利用できることも確認してください。

出典がある場合は、利用者が選んだ論文名・URL等を `--source` に指定します。数学的定義、関数の規約、研究上の条件は利用者の入力に従います。Codexは構造化入力・適用候補・説明の作成を支援します。

## 初回の登録とAI候補生成

```sh
python3 -m special_function_agent verify examples/gamma-recurrence.txt --route direct --output runs/research-source
python3 -m special_function_agent research add runs/research-source --name gamma-step --original-input examples/gamma-recurrence.txt
python3 -m special_function_agent research list
```

`add` が返す64桁の `id` を、次の `LEMMA_ID` に置き換えます。新規AI候補の生成は既存のCodex CLI認証を使います。保存・検査・replayはAIを呼びません。

```sh
python3 -m special_function_agent research generate examples/research-gamma-two-step.txt --using LEMMA_ID --route direct --output runs/research-direct --archive
python3 -m special_function_agent research generate examples/research-gamma-two-step.txt --using LEMMA_ID --route steps --output runs/research-steps --archive
python3 -m special_function_agent replay runs/research-steps/attempt-1/verification
python3 -m special_function_agent research generate examples/research-gamma-two-step.txt --using LEMMA_ID --route steps --output runs/research-reuse --archive
```

最初の候補が通った場合、`attempt-1/verification` に `request.json`、`certificate.lean`、`report.md`、`result.json`、`analysis.json`、`numerical.json` を保存します。日本語レポートには適用した補題と、ステップ経路の各等式・理由を記載します。形式検査は各等式と元の全条件を対象とします。

成功した派生証明を `research add` でさらに登録し、次の命題にも使えます。例として2段のGamma公式を `x+2` と `x` へ適用すると、`examples/research-gamma-four-step.txt` の4段公式になります。依存する証拠も選択packageに含まれます。

## 保存した候補をローカルで検査する

配布済みの研究証拠は、AI認証を使わず次のように検査できます。補題のsnapshotもrequestに保存されています。

```sh
python3 -m special_function_agent verify demo/research-gamma-steps/request.json --output runs/research-example
python3 -m special_function_agent replay runs/research-example
python3 -m special_function_agent replay demo/research-gamma-four-direct
```

AIの `attempt-1/candidate.json` は補題ID・型付き引数・閉じた手順だけを持ちます。同じ選択補題を使って再検査できます。

```sh
python3 -m special_function_agent research verify examples/research-gamma-two-step.txt --plan runs/research-steps/attempt-1/candidate.json --using LEMMA_ID --output runs/research-local --archive
```

直接候補の形は次のとおりです。`LEMMA_ID` は登録済みの完全なIDへ置き換えます。

```json
{"mode":"direct","recipe":"research","uses":[
  {"lemma":"LEMMA_ID","arguments":{"x":{"op":"add","args":[{"op":"var","name":"x"},{"op":"int","value":1}]}},"reverse":false},
  {"lemma":"LEMMA_ID","arguments":{"x":{"op":"var","name":"x"}},"reverse":false}
]}
```

ステップ候補は `mode: steps` と `steps` を持ち、各ステップに `before`、`after`、`recipe`、`uses`、`reason`、`conditions` を指定します。`recipe: research` は補題の適用、`recipe: ring` は `uses: []` として代数式を整理します。等式の始点・終点と連結、補題の全引数、元条件との対応を検査します。

## 私有保存・選択共有・更新

既定の保存先は `~/SpecialFunctionProofAgentData/research` です。`--research-dir` または環境変数 `SPECIAL_FUNCTION_RESEARCH_DIR` で外部フォルダへ変更できます。本体リポジトリ内を保存先に指定すると拒否します。登録は内容ハッシュによる追記で、以前のpackageを保持します。

packageは元入力、固定request、変数型・仮定・関数規約、出典、Lean証明、検査結果、数値診断、環境・依存証拠、各ファイルのハッシュを含むJSONです。共有する1件を利用者が選びます。選択したpackageには、その証明に必要な依存補題の元入力・出典も含まれます。

```sh
python3 -m special_function_agent research export LEMMA_ID ~/gamma-step.research.json
python3 -m special_function_agent research import ~/gamma-step.research.json
python3 -m special_function_agent research reverify LEMMA_ID
python3 -m special_function_agent research import ~/gamma-step.research.json --reverify
```

通常のimportは現在の数学環境で証明を再生成・replayします。環境差があるpackageは、明示した `reverify` または `import --reverify` で、依存する補題から順に元の命題を検査し、新しいIDを保存します。元のJSONは保持します。検査器は構造化requestからLeanを生成し、受け取ったLean文字列との一致を確認します。共有ファイル内の任意のLeanを直接実行する経路はありません。

## この版の対応範囲

- schema_version 2、最大3個の自由実変数、既存の関数定義・規約を扱います。自然数・整数の自由次数を持つ補題の研究適用は後続です。固定の自然数・整数次数は既存ASTの範囲で扱います。
- 補題の代入引数は型付き実式です。代入する式自体に微分・積分を含む場合は入力検査で拒否します。元補題にある微分・積分の束縛は、再生成した定理への引数適用で保持します。
- 各補題の仮定は、新targetの元仮定から固定のLean手順で導出します。条件不足・係数違い・証拠改変・環境差がある候補は完全証明へ進みません。
- 保存できる証拠の状態は完全証明、元の追加前提付き検証、未解決、条件不足です。新targetへ適用する補題は、完全なLean証明と標準公理監査が通った等式に限ります。
- 1候補は最大12回の適用・12補題の依存閉包・深さ4、JSONとpackageは256 KiBまでです。現在の代数整理と条件導出で扱えない候補は `unresolved` となります。
- 数値診断は既存mpmathがある場合に実行します。未導入時もLean検査と保存を続けます。
- 新しい関数の定義・表記・数値評価・Lean APIを登録する段階は今後の対象です。
