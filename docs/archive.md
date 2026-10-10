# 独立archiveとBessel記録の取り込み

既定保存先は `~/SpecialFunctionProofAgentData/archive`、環境変数は `SPECIAL_FUNCTION_ARCHIVE_DIR` です。Bessel側の既定保存先と環境変数は独立しています。

```sh
python3 -m special_function_agent archive import-bessel /path/to/bessel/verification-run
```

この明示操作は元のrequestとcertificateの一致・ハッシュを確認し、新環境で同じ固定入力を検査して新しい記録を保存します。元環境、元request/resultのハッシュ、元状態、上流リポジトリをprovenanceへ残します。元記録のファイルは変更しません。Bessel archiveのentryディレクトリを指定するとmanifestも検査します。

v2の同一性には自由変数名・型・積分の束縛名、全仮定、両辺、関数規約の版を含みます。仮定の順序だけは正規化し、式の変形や変数名の付け替えは別の命題として保存します。環境はLean/toolchain/lockfile/全数学モジュール/関数登録表のハッシュで確認します。

完全Leanの proved/refuted 記録は登録前と再利用前に再検査します。成功した条件付きLean証拠も登録前に再検査し、元request・環境・再生成テンプレート・analysis.json・定理本文・scope・全前提の一致を確認します。各記録のdetail.mdにも、条件付き定理の前提と残る形式化義務を表示します。固定半整数 `YNoninteger` の完全証明は `full_bessel_proof:true`、従来Y・交差積の条件付き記録のreplayは `conditional_replayed` と `full_bessel_proof:false` を返します。後者の元命題は未解決状態を保持します。数値診断は独立の `numerical.json` に保存します。

## 記録操作の詳細

# 個人用の検証記録

利用者の記録は、既定で `~/SpecialFunctionProofAgentData/archive` に保存します。
本体の `demo/` は配布する共通例、`runs/` は検証中の作業場所です。
保存を指示した試行は、結果が証明済み・反証済み・未解決・条件確認待ちのいずれでも残せます。
アーカイブの作成・検索・再検査からGitのcommitやpushは実行しません。

## 保存と検索

リポジトリのディレクトリで実行します。

```sh
mkdir -p runs
bessel_run=$(mktemp -d "$PWD/runs/session.XXXXXX")
python3 -m special_function_agent verify examples/recurrence.txt --recipe recurrence \
  --output "$bessel_run/recurrence" --archive
python3 -m special_function_agent archive list
python3 -m special_function_agent archive search 'J'
```

`verify` の出力には `archive_id` が加わります。その値を次の `RECORD_ID` に指定します。

```sh
python3 -m special_function_agent archive show RECORD_ID
python3 -m special_function_agent archive replay RECORD_ID
```

人が読む入口は保存先の `catalog.md`、各試行の説明は
`entries/RECORD_ID/detail.md` です。`archive show` は元入力、全条件、候補、
環境と結果の情報をJSONで返し、`verification_dir` から保存証拠を取り出せます。
`parse --archive` は構造化した入力だけを未解決として保存し、入力エラー時には
元のテキストと条件指定、エラー理由を保存します。

以前の検証結果や配布例も取り込めます。

```sh
python3 -m special_function_agent archive add demo/direct
python3 -m special_function_agent archive add "$bessel_run/recurrence"
```

元のテキストファイルが別にある場合は `--original-input FILE` を指定します。
取り込み元のファイルは変更しません。証明済み・反証済みの記録は、コピーした証拠を
Leanで再検査してから登録します。

## AI生成と完全一致の再利用

```sh
python3 -m special_function_agent.generate demo/target.json --route direct \
  --output "$bessel_run/agent" --archive
```

生成器は、条件を含む同じ命題・同じ直接または段階経路の記録を探します。
証明済み・反証済みの証拠が現在の環境で再検査を通れば、元の入力にその証明計画を
付けて再度Lean検証し、新しい履歴として保存します。この経路はAIを呼び出さず、
結果に `reuse.ai_called: false` と元記録のIDを記録します。
再利用時の作業証拠は `agent/reuse/verification/` にあります。

該当記録がなければ、本人のCodex CLI認証を使って新しい候補を生成します。
各試行を個別に登録し、`--attempts 2` などで再試行しても前の失敗は保持します。
環境の違いで既存証拠を再検査できなかった場合は、
`archive-reuse-skipped.json` に理由を残して新規生成へ進みます。
新規生成の作業証拠は `agent/attempt-1/verification/` などにあります。

ここで再利用するのは、固定された命題の証拠と許可された証明計画です。
異なる定理で補題として利用する機能は、宣言名の一意化や検証操作の追加を伴う今後の範囲です。

## 条件・履歴・保存場所

命題IDには、proofを除いた入力AST、型、全条件を正規化したSHA-256を使います。
条件の順序と旧 `x_gt` 表記は正規化し、式の左右・ASTの演算順序は保持します。
条件を変更した命題や、数学的変形で同値になる別の式は、それぞれの入力として扱います。
同一命題の再試行には毎回新しい記録IDを付けます。

従来Y・交差積のschema version 2でも、変数、スカラー条件、関数値の根・非零条件を
命題IDに含めます。診断結果、自然言語解析、条件付きLean証明、数値結果を保存し、
元命題は `unresolved`、定義域条件の確認が必要な入力は `needs_conditions` として記録します。条件付き証明の再検査結果も、元命題の
完全なLean証明の再検査と区別して返します。条件付きLeanの再検査が通った場合は
`conditional_replayed: true`、`full_bessel_proof: false`、`replayed: false` を返し、
CLIの終了コードは `1` です。

保存先はコマンドごとの `--archive-dir PATH`、環境変数 `SPECIAL_FUNCTION_ARCHIVE_DIR`、
既定の保存先の順で選びます。`verify`・`parse`・`generate` では
`--archive-dir` と `--archive` を併用します。

```sh
python3 -m special_function_agent archive list --archive-dir "$HOME/BesselProjectData/archive"
```

本体リポジトリ内の保存先は拒否します。利用者や研究テーマごとに別の保存先を
指定すると、索引・履歴・証拠が分離されます。共有する記録と共有先は利用者が選びます。

各記録にはファイルのハッシュ一覧があり、登録は一時コピーを検査した後に原子的に確定します。
JSON索引とMarkdown目録は記録本体から再構成します。索引の破損は再構成し、
証拠本体の改変・不正なパス・シンボリックリンクはエラーとして停止します。
数学環境が変わった記録を現在の環境で調べ直すには、その `request.json` を新しい
出力先で `verify --archive` に渡し、新しい検査履歴を作ります。


## 数学環境を更新したとき

数学モジュールや関数登録表の更新で、保存証拠の環境ハッシュが変わります。Legendre/Laguerre/Jacobiと非整数Yを追加した版でも、以前のGamma/Beta/Hermite/erf記録を `archive replay` すると環境差を検出します。既存関数の命題IDに用いる規約の版は維持し、元記録を残して同じ証明計画を新環境で検査します。

```sh
python3 -m special_function_agent archive show RECORD_ID
# 上のverification_dirに表示されたディレクトリを指定する
python3 -m special_function_agent verify /path/to/verification/request.json --output runs/rechecked --archive
python3 -m special_function_agent archive replay NEW_RECORD_ID
```

その後、同じtargetと同じrouteで生成器を実行すると、新環境の証拠を再検査して再利用できます。結果の `reuse.ai_called: false` と元記録IDで再利用を確認します。公開済みGamma/Beta、Hermite/erf、Legendreと半整数Yの保存証拠を一時archiveへ複製し、環境差の検出、同じrequestの明示再検証、新証拠のreplay、AIを呼ばない再利用、旧記録のバイト列保持を確認しています。

対象の型・全条件・関数規約は毎回一致を確認します。多項式の自然数次数とBesselの整数次数、物理学規約Hと確率論規約He、一般化Laguerre/Jacobiのパラメータ、明示した `YNoninteger` と従来Yは、それぞれのASTと規約を保存します。新しい多項式族と非整数Yは規約version 3、Hermite/erfはversion 2、従来Gamma/Betaはversion 1を使います。
