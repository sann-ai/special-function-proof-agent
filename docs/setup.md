# 初回セットアップ

最初は[READMEのGitHub URLと導入プロンプト](../README.md#codexから使う)をCodexのローカル作業用チャットへ貼ってください。Codexがソースの取得を進め、取得先を作業フォルダとして開く操作が必要なら案内します。取得済みの場合は、そのフォルダで準備を依頼できます。Codexが内部のJSONとコマンドを扱い、元の式・変数・全条件を確認してLean検証へ進めます。日常の依頼と履歴再利用の手順は[Codexでの使い方](codex-workflow.md)を参照してください。

以下はmacOS・Linux向けの手順です。Windows向けの初回手順は未検証です。Codex自体の導入・サインインとフォルダの選択は[OpenAI公式のQuickstart](https://developers.openai.com/codex/quickstart)を参照してください。

Codexでの対話は利用者のアカウントの契約・利用枠を使い、このツール用の別のAPI契約は必須ではありません。準備済みの環境でのローカル検査・再検査は外部AIを呼びません。数式のクラウド送信、平文保存と選択共有の範囲は[データの扱い](codex-workflow.md#データの扱いと共有)を確認してください。

## 補助：ソースを手動で取得する

通常はCodexへ取得を依頼できます。以下は手動で取得する場合や、Codexが行う操作を確認する場合の手順です。

Gitで取得する場合:

```sh
git clone https://github.com/sann-ai/special-function-proof-agent.git
cd special-function-proof-agent
```

ZIPで取得する場合は、[リポジトリ](https://github.com/sann-ai/special-function-proof-agent)の **Code → Download ZIP** を選びます。ダウンロード先で次を実行し、展開したディレクトリへ移動します。

```sh
python3 -m zipfile -e special-function-proof-agent-main.zip .
cd special-function-proof-agent-main
```

ZIPにはプロジェクトのGit履歴が含まれません。Lakeはmathlibなどの依存をGitで取得するため、ZIPから利用する場合もGitを用意してください。

## フォルダをCodexで開き、初回準備を依頼する

`README.md`、`AGENTS.md`、`lean-toolchain` があるフォルダをCodexの作業対象に選びます。ZIPの場合も、展開したプロジェクトの直下を選んでください。Codexは作業前にプロジェクトの `AGENTS.md` を読み取ります。[OpenAI公式のAGENTS.md案内](https://developers.openai.com/codex/guides/agents-md)

最初のチャットで、次のように依頼します。

```text
このフォルダの sann-ai/special-function-proof-agent を初回利用できる状態にしてください。
AGENTS.md と docs/setup.md を読み、対象フォルダと既存の Python・Git・elan・Lean/Lake を確認してください。
Pythonが利用できれば scripts/doctor.py を実行し、不足ツールや固定版との相違を具体的に報告してください。
Lean 4.34.0 とリポジトリに固定されたmathlib・lockfileを維持して、必要な固定環境の取得とビルドを進めてください。
基礎モジュールと3つの解析定義モジュールをビルドし、doctorを再実行して、Gammaの例1件をverifyとreplayで確認してください。
不足ツールや追加パッケージの導入が必要なら、対象と理由を示して確認してください。
個人設定・グローバルのAGENTS.md・skillは変更しないでください。
このチャットで準備を進め、Codex CLIを入れ子に起動したAI候補生成は行わないでください。
今回の準備では外部archiveへの保存は不要です。
```

固定Lean、mathlibとビルドキャッシュの初回取得にはネット接続と数GB規模の空き容量を使います。Python追加パッケージは不要です。既存の数値計算用 `mpmath` があれば利用し、未導入時は数値欄に `backend_unavailable` を記録して、対応するLean検証を進めます。

## 準備後は式と条件をチャットで渡す

自然言語やTeXで、式・変数の型・条件をCodexに渡します。例えば次のように依頼できます。

> 正の実数xについて、$\Gamma(x+1)=x\Gamma(x)$ を検証してください。元の式と条件を確認し、直接証明と、理由を添えたステップ証明をLeanで検査してreplayしてください。

通常はこのチャットのCodexが `verify --route direct` / `verify --route steps` を使います。既存の履歴を利用する依頼では、同一命題の厳密照合と現在の環境でのreplayを行い、その記録の証明状態を確認します。型・束縛・条件・規約を含めた照合の手順は[Codexでの使い方](codex-workflow.md)に従います。

検証ごとに `runs/` 内の未使用サブフォルダへ出力します。通常の検証結果は次のファイルで確認できます。

- `request.json`：固定した命題・全条件と証明候補。
- `result.json`：証明の状態、実行結果、環境情報。
- `proof_attempt.lean`：Leanへ渡した証明候補。受理された証明は `certificate.lean` に保存します。
- `report.md`：式・条件・検証結果の説明。
- `analysis.json` / `numerical.json`：v2入力の解析と数値診断。

入力検査で停止した場合は、コマンドの診断と、その時点までに作成したファイルを確認します。数値結果を再現する際は、保存された計算精度・標本・数値環境も参照してください。

長期保存を希望するときは、例えば「この証拠を `~/SpecialFunctionProofAgentData/archive` へ保存し、次回から同じ命題の履歴を再利用してください」と依頼します。Codexは承認された保存方針に従って `--archive` を使います。会話や研究設定で保存・再利用と保存先が承認済みなら、都度の確認を挟まず継続します。新規利用者で保存先が未指定の場合は、リポジトリ外の既定先 `~/SpecialFunctionProofAgentData/archive` を提案し、保存先だけ確認します。共有・公開する記録は利用者が選びます。

## 補助：固定環境をコマンドで準備する

ここからは、Codexが実行する内容を確認したい場合や、ターミナルで操作する場合の補助手順です。保存済み候補の検証にはPython 3.12以上、Git、elanが管理する固定版Lean / Lakeを使います。不足ツールは名前と必要な版を確認して準備します。elanの導入方法は[Lean公式のインストール案内](https://lean-lang.org/install/)を参照してください。

プロジェクトのディレクトリ内で、まず既存環境を診断します。初回は未取得の依存や未ビルドの項目が「要準備」になります。

```sh
python3 scripts/doctor.py
```

Python・Git・elanが利用できる状態で固定環境を取得し、ビルド後に再診断します。

```sh
elan toolchain install leanprover/lean4:v4.34.0
lake exe cache get
lake build
lake build SpecialFunctionProofAgent.AnalyticDefinitions SpecialFunctionProofAgent.UserAnalyticDefinitions SpecialFunctionProofAgent.AdvancedAnalyticDefinitions
python3 scripts/doctor.py
```

`lean-toolchain` は `leanprover/lean4:v4.34.0`、`lakefile.toml` のmathlibは `db00fb3901b1bb4954f8a2373285959a5930bbfa` に固定しています。`lake-manifest.json` は間接依存のコミットも記録します。これら3ファイルを保持したまま上記を実行してください。通常の導入・再検証では `lake update` や最新版への更新は必要ありません。

`doctor.py` はPython、Git、固定版のLean / Lake、依存コミット、ビルド出力の存在を確認します。インストール、AI実行、認証情報の読み取り、個人記録ディレクトリの作成は行いません。終了コード `0` は全項目確認済み、`1` は準備が必要な項目があることを表します。ソース更新後のビルドと証明の検査は、次の手順で行います。

## 補助：最初の検証と再検証

Gamma漸化式を検証し、生成された証明と配布済みの証明を再検査します。出力先には未使用のディレクトリを指定してください。

```sh
python3 -m special_function_agent verify examples/gamma-recurrence.txt --route direct --output runs/first-check
python3 -m special_function_agent replay runs/first-check
python3 -m special_function_agent replay demo/gamma-direct
```

`proved` と、再検査時の `replayed: true` を確認します。これらの操作はCodex CLI、AIへの接続、APIキーを使いません。固定環境の取得とビルドが完了した端末ではローカルで実行できます。

保存済みの同じ命題・経路を利用するときは、厳密照合とreplayをまとめて実行します。

```sh
python3 -m special_function_agent archive lookup examples/gamma-recurrence.target.json --route direct
```

成功時は `proved`、`replayed: true` と再利用した記録IDを確認します。該当する証拠がない場合は `not_found`（終了コード1）となるので、Codexへ新しい検証を依頼します。この照合はAI呼出しや新規保存を行いません。保存先を指定する場合は `--archive-dir PATH` を付けます。

多項式の漸化式・隣接直交と半整数Yを確認する場合：

```sh
python3 -m special_function_agent verify examples/legendre-recurrence.txt --route direct --output runs/first-legendre
python3 -m special_function_agent replay runs/first-legendre
python3 -m special_function_agent verify examples/legendre-adjacent-integral.txt --route steps --output runs/first-adjacent
python3 -m special_function_agent replay runs/first-adjacent
python3 -m special_function_agent verify examples/yhalf-derivative.txt --route steps --output runs/first-yhalf
python3 -m special_function_agent replay runs/first-yhalf
```

Legendre漸化式は自然数n≥1と実数x、隣接直交積分は全自然数nと区間[-1,1]、Yの例は固定半整数次数とx>0を明示しています。[多項式の規約](orthogonal-polynomials.md)と[Yの対応範囲](bessel-y-formalization.md)を参照してください。

整数Yの新しい4式をdirect/steps両経路で確認する場合：

```sh
for example in integer-y-zero-derivative integer-y-one-derivative integer-y-wronskian integer-y-cross-same-point; do
  for route in direct steps; do
    python3 -m special_function_agent verify "examples/$example.txt" --route "$route" --output "runs/first-$example-$route"
    python3 -m special_function_agent replay "runs/first-$example-$route"
  done
done
```

2つの微分公式と同点交差積はx>0、一般Wronskianは `n integer,x>0` を条件とします。Wronskianは `J_{n+1}Y_n-J_nY_{n+1}=2/(pi*x)`、同点交差積は `X_01(x,x)=-2/(pi*x)` の符号で検証します。同名の `.target.json` も配布しています。微分交換と定数2/πの規格化は証明済みで、上記の4例はそれぞれの元の型・正性条件から検査します。

二点の根条件付き交差積 `examples/cross-product-root.txt` は、元の `z>0`、`0<lambda<1`、根条件から正エネルギー積分と両分母の非零性を導き、完全Lean証明へ接続します。

```sh
python3 -m special_function_agent verify examples/cross-product-root.txt --route direct --output runs/first-cross-root-direct
python3 -m special_function_agent replay runs/first-cross-root-direct
python3 -m special_function_agent verify examples/cross-product-root.txt --route steps --output runs/first-cross-root-steps
python3 -m special_function_agent replay runs/first-cross-root-steps
```

正常な完全証明の結果は `proved`、`full_bessel_proof: true` です。旧整数Y・交差積の条件付き経路を使う場合は `--route diagnostic` を指定します。この経路と旧診断記録は `unresolved`、`full_bessel_proof: false`、元の条件付きscopeを保持します。旧記録を完全証明として再評価するときは、保存requestからproofを除いた同じtargetをdirect/stepsへ渡し、同じtarget IDに新しい履歴を追加します。整数Y・交差積の具体的手順は[保存仕様](archive.md#条件付き記録から完全証明へ)を参照してください。

全保存例とテストを実行する場合:

```sh
python3 scripts/replay_examples.py
python3 scripts/audit_special_functions.py
SF_RUN_LEAN_TESTS=1 BESSEL_RUN_LEAN_TESTS=1 python3 -m unittest discover -s tests -v
```

`runs/` は手動検証の一時出力先としてGit管理から除外しています。個人の蓄積記録の既定保存先はリポジトリ外の `~/SpecialFunctionProofAgentData/archive` です。共有・公開の対象は、記録を作成した利用者が選びます。アーカイブ操作はREADMEの対応節を参照してください。

検証した等式を別の命題に使う場合は、[研究補題の登録と再利用](research-lemmas.md)に従って `research add` で外部研究フォルダへ登録します。既存関数の有限合成による新しい研究関数は、[明示定義の登録](research-functions.md)から始めます。追加の依存導入は不要です。いずれもCodexへ定義・条件と登録の希望を伝えて依頼できます。

## 補助：独立したAI候補生成を明示的に選ぶ場合

独立した生成コマンドを利用者が選ぶ場合は、既存の本人のCodex CLI認証を使います。導入・サインインは[OpenAI公式のQuickstart](https://developers.openai.com/codex/quickstart)を参照してください。この経路は推論量Ultraで新しいAI呼出しを行い、利用枠を消費します。認証方法によってはAPI料金が発生します。通常の対話や初回セットアップでは入れ子に起動しません。認証情報の保存先は本人のCodex環境とします。

```sh
codex login
codex login status
python3 -m special_function_agent.generate demo/target.json --route direct --output runs/my-first-generation
```

モデル・推論量の条件と生成経路の指定はREADMEの「Codexへの依頼例」を参照してください。セットアップや環境診断がCodexをインストールしたりログインしたりすることはありません。

## 準備に失敗した場合

Codexへ「直前の診断を読み、止まった操作・原因・必要な次の操作を説明してください」と依頼できます。既存の研究ファイルは保持し、固定環境を最新版へ更新して切り抜けることはしません。サポートへ伝える場合は、OS・Python/Lean版、停止したコマンド、`doctor`の該当項目とエラーメッセージを抜き出してください。研究式・元入力・認証情報を含むログ全体を送る必要はありません。

- `python3`、`git`、`elan` が見つからない: それぞれを導入し、ターミナルを開き直してPATHを確認してください。
- 固定版Leanが未導入: 上記の `elan toolchain install` を実行してください。doctorは自動ダウンロードを行いません。
- 依存が未取得・キャッシュが不足: ネット接続と空き容量を確認して `lake exe cache get`、`lake build` を実行してください。
- 依存コミットがlockfileと異なる: 利用中のソースと3つの固定環境ファイルを確認してください。新しいclone・ZIP展開先で手順をやり直すと、既存作業を保持して切り分けられます。
- 保存証明の再検査が環境差分を報告: 記録に対応する版のソース・固定環境を使ってください。現行版で再評価するときは、保存した `request.json` を `verify --archive` に渡して新しい出力先へ記録します。[環境更新時の再検査と再利用](archive.md#数学環境を更新したとき)を参照してください。

## 確認した環境と範囲

この独立版はmacOS arm64、Python 3.14、Lean 4.34.0で検査しています。固定コミットの依存・コンパイル済みmathlibキャッシュを再利用し、プロジェクトをビルドして元式の検証と保存証明の再検査を実行します。ネットからLean本体と全依存を取得する準備は、下記CIでも検査します。

[GitHub Actions](https://github.com/sann-ai/special-function-proof-agent/actions/workflows/verify.yml)は Ubuntu 24.04・Python 3.12で固定環境を準備し、入力境界・Lean検証・保存例の再検査を実行します。Windowsの実行確認は今後の対象です。

## ライセンスと依存の出典

配布本体、Lean証明、文書、同梱サンプルは [MIT License](../LICENSE) で提供します。利用者が外部保存先に蓄積する入力・生成候補・検査記録は、利用者本人が共有・公開の扱いを選びます。

Lean証明はmathlibのBessel・正則化超幾何関数・Gamma・微積分の定義と補題をimportして組み立てています。依存ソースはLakeが `.lake/packages/` に取得し、各依存のライセンスと著作権表記を維持します。リポジトリとソースZIPにはこの依存ディレクトリを同梱しません。

固定した依存のうち、mathlib、Batteries、Aesop、Qq、ProofWidgets、ImportGraph、LeanSearchClient、PlausibleはApache-2.0、Lean CLIライブラリ（`Cli`）はMITです。取得した各パッケージの `LICENSE` とソースの著作権表記を参照してください。Lean本体は[公式配布元のライセンス](https://github.com/leanprover/lean4/blob/v4.34.0/LICENSE)に従います。依存のファイルやコピー・改変したコードを再配布する場合は、元のライセンス、著作権表示、改変の表示、該当するNOTICEを含めてください。

一般直交性・規格化と整数Y漸化式の追加確認：

```sh
python3 -m special_function_agent verify examples/legendre-orthogonal.txt --route steps --output runs/orthogonal-check
python3 -m special_function_agent verify examples/legendre-norm.txt --route direct --output runs/norm-check
python3 -m special_function_agent verify examples/integer-y-complete.txt --route steps --output runs/integer-y-check
python3 -m special_function_agent replay runs/integer-y-check
```

条件は順に自然数m≠n、全自然数n、任意整数nかつx>0です。各出力先は未使用のディレクトリを指定します。

幾何級数、exp/sin/cos積分、指定クラスの非線形・二階初期値問題は[追加の解析定義](research-advanced-analytic-definitions.md)を参照してください。
