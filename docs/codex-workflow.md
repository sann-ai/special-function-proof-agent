# Codexで式を伝え、検証結果を受け取る

利用者との対話はCodexが担当し、このプロジェクトのCLIが固定した命題をLeanで検査します。式の構造化、証明計画、実行と結果の読み取りをCodexに依頼できます。

## 最初の一回

リポジトリをcloneまたはZIP展開し、そのフォルダをCodexの作業フォルダとして開きます。Codex CLIを利用する場合は取得したフォルダで `codex` を起動します。プロジェクトの指示は [AGENTS.md](../AGENTS.md) にあります。Codexの[プロジェクト指示の読み込み](https://learn.chatgpt.com/docs/agent-configuration/agents-md)と[初回利用](https://learn.chatgpt.com/docs/quickstart)は公式資料を参照してください。

> このプロジェクトのAGENTS.mdとdocs/setup.mdを確認し、既存ツールで固定Lean環境を準備してください。不足するツールと必要な操作があれば教えてください。準備後、正の実数 shape に対する Γ(shape+1)=shape Γ(shape) を、日本語の手順付きでLean検証してください。

Python 3.12以上、Git、elanが管理する固定Lean環境を使います。Codexは `doctor.py` で現在の状態を確認し、[セットアップ](setup.md)の取得・ビルドを行います。初回の依存取得にはネット接続と数GB規模の領域が必要です。利用者のCodex設定・認証・グローバルskillは保持します。実行に必要な権限が足りない場合は、具体的な操作と理由を伝えます。

## 普段の依頼

式、変数の型や範囲、採用する規約を分かる範囲で伝えてください。文章、TeX、式を含むファイルを使えます。次はそのまま依頼できる例です。

> 正の実数 shape について、Γ(shape+1)=shape Γ(shape) をこのエージェントで確かめてください。日本語の証明手順とLean証明を示し、結果を自分用の `~/SpecialFunctionProofAgentData/archive` に保存してください。同じ条件の検証済み履歴があれば再検査して使ってください。

> 実数 x に対する erf(-x)=-erf(x) を、追加の符号条件を置かずにLeanで検証し、日本語で説明してください。今回は外部履歴への保存は不要です。

> 先ほど保存した正の実数 shape のGamma漸化式を、同じ変数・条件・ステップ経路で再検査して使い、結果と証明ファイルを示してください。

表記の意味が一意なら、Codexは解釈した式と条件を短く示して進めます。例えばHermiteのH/He、積分端点、次数の型が曖昧な場合は、その点だけ確認します。実数全域を指定した依頼に正値条件が必要になった場合は、元の依頼の検査結果と必要な条件を説明し、条件を採用するか利用者に確認します。

## Codexが行う処理

1. 作業用の新しい `runs/` サブフォルダに元の依頼文を保存する。既存ファイルを上書きしない。
2. 対応する式表記へ変換し、`parse` で固定targetを作る。変数名・型・全条件・束縛・関数規約を元の依頼に照合する。対応する研究関数では定義IDと元の呼出しも保持する。
3. 履歴再利用を依頼されていれば、同じtargetと経路を `archive lookup` で検索する。現環境のLean再検査まで成功した完全証明を使う。
4. 新規検証は `verify --route steps` または指定された `direct` を実行する。説明を求められた場合はstepsを使う。複数段の計画が必要なら、既存の構造化ステップだけを作り検査へ渡す。
5. `result.json`、`report.md`、成功した `certificate.lean` を読み、検査された式と条件、証明範囲、説明、保存場所を返す。保存依頼があるときは外部archiveへ登録する。

通常の対話は現在のCodexとローカル検証器で進みます。`special_function_agent.generate` は単独の候補生成を明示的に依頼した場合の補助コマンドです。利用者がJSONを書く必要のある場面では、Codexが既存形式に沿って準備します。

一つの依頼を処理するために、本体の数学コードや対応範囲を変更する作業は含めません。必要な式が未対応なら、該当する入力形式・定理・条件を具体的に報告し、拡張は別の依頼として扱います。

## 受け取る説明とファイル

成功したGammaの例では、次の内容を日本語で示します。

> shapeを正の実数として、Γ(shape+1)=shape Γ(shape) のLean検証が成功しました。正の引数に対するGammaの漸化式を適用し、元の等式を得ます。検査した条件はshape>0です。日本語手順はreport.md、形式証明はcertificate.leanにあります。

`report.md` には入力式、条件、状態、ステップごとの等式と理由を記録します。`certificate.lean` は成功した形式証明、`request.json` は元の型・全条件と検査した証明計画、`result.json` は機械判定と環境情報です。`analysis.json` と `numerical.json` がある経路では、それぞれ解析情報と数値診断を確認できます。

自然言語の理由は説明用の文章です。検査の根拠は各ステップの等式、固定された全条件、Leanの証明結果です。Codexはこの範囲に沿って説明を補い、証明済み部分と未解決部分を分けて伝えます。検査に失敗した `proof_attempt.lean` は途中の試行として扱います。

- `proved`：元の型・全条件の命題がLeanと公理監査を通過。
- `needs_conditions`：現在の入力・対応レシピで必要な条件を確認できない。条件の追加は利用者の判断で行う。
- `unresolved`：対応外の形式、証明計画の失敗、環境の未準備、または明示前提付きの部分証拠。理由と確認済みの範囲を示す。
- `refuted`：対応する反証経路で検査された反証。未対応、検索ヒットなし、数値の不一致とは区別する。

`no_mismatch_found` などの数値診断は数値欄で報告します。任意の `mpmath` が未導入でも、対応するLean検証と証拠の保存は続けられます。

## 履歴の場所と再利用

外部履歴の既定保存先は `~/SpecialFunctionProofAgentData/archive`、研究用の補題・定義は `~/SpecialFunctionProofAgentData/research` です。会話や研究設定で保存・再利用と保存先が既に決まっていれば、その範囲で確認を繰り返さず継続します。初めて保存する利用者が保存先を指定していない場合は、既定の場所を提案し、その点だけ確認します。作業ファイルはGit対象外の `runs/` に置きます。別の保存先を使う場合も、Codexへの依頼で指定できます。

同じ命題の再利用では、式・名前・型・全仮定・規約を照合し、現環境で再検査します。`archive lookup` が返す `ai_called: false` は、保存証拠の検索と検査で新しいAI候補生成を行わなかったことを表します。元の記録は保持します。環境差や証拠改変があれば理由を報告し、再検証を依頼されたときは同じ元targetから新しい記録を作ります。

別の命題へ補題を適用する場合は、[研究補題](research-lemmas.md)の仕組みを使います。[研究関数](research-functions.md)と解析的定義には個別の対応範囲があります。共有は利用者が選んだ定義・補題とその依存だけを明示的にexportします。

## Codexが使う最小のコマンド例

以下は会話の内部でCodexが実行する例です。手動でも使えます。プロジェクトのルートから、新しい作業フォルダを作ります。

```sh
mkdir -p runs
sf_run=$(mktemp -d "$PWD/runs/conversation.XXXXXX")
printf '%s\n' 'Gamma(shape+1)=shape*Gamma(shape); shape>0' > "$sf_run/input.txt"
python3 -m special_function_agent parse "$sf_run/input.txt" --output "$sf_run/target.json"
python3 -m special_function_agent archive lookup "$sf_run/target.json" --route steps
```

lookupが `not_found` の場合は新規検証へ進めます。保存依頼がある例：

```sh
python3 -m special_function_agent verify "$sf_run/input.txt" --route steps \
  --output "$sf_run/verification" --archive
python3 -m special_function_agent archive lookup "$sf_run/target.json" --route steps
```

保存を依頼されていなければ `--archive` を付けずに検証します。lookupは完全一致する `proved` 証拠を再検査し、ヒット時に元記録IDと証拠の場所を返します。該当なし・不一致のときは新しいAI呼出しや保存を行いません。終了コードと詳細は[archive仕様](archive.md)を参照してください。
