# Special Function Proof Agent

特殊関数の入力を固定した命題へ変換し、制限された証明候補をLeanで検査・保存する独立ツールです。Codexからの依頼とターミナルの両方で利用できます。[Bessel Proof Agentの固定版](UPSTREAM.md)を基盤に、Gamma/Betaの実積分へ拡張しました。ライセンスは[MIT](LICENSE)です。

## 初期版で使えるもの

- **完全Lean証明**：正の引数で `Gamma(x+1)=x*Gamma(x)`、正の `a,b` でEulerのBeta積分、正の `a,r` でscaled Gamma積分。直接証明と、理由を添えた等式ステップ証明の両経路があります。
- **Bessel J**：引き継いだv1の符号・漸化式・微分・積分・有理数冪の閉じた証明レシピ。[詳しい対応式](docs/bessel-v1.md)。
- **実Bessel J/Y・交差積**：正の引数で構造化入力、数値診断、既知の根条件に対する解析テンプレートと条件付き代数Lean。元のY命題は `unresolved`、`full_bessel_proof: false` と保存します。
- **保存と再検査**：元式・変数型・束縛・全条件・関数規約・環境ハッシュ・証明を保持し、再利用前にLeanで再検査します。

登録表は `special_function_agent/registry.py`、関数別Lean基盤は `BesselProofAgent/` と `SpecialFunctionProofAgent/Gamma.lean`、`Beta.lean` にあります。

## 導入

Python 3.12以上、Git、elanを準備します。Leanは4.34.0、mathlibは固定コミットを使います。

```sh
git clone https://github.com/sann-ai/special-function-proof-agent.git
cd special-function-proof-agent
elan toolchain install leanprover/lean4:v4.34.0
lake exe cache get
lake build
python3 scripts/doctor.py
```

[Code → Download ZIP](https://github.com/sann-ai/special-function-proof-agent/archive/refs/heads/main.zip)から展開したディレクトリでも同じコマンドを利用できます。依存取得にGitが必要です。[初回セットアップと確認範囲](docs/setup.md)。

Python追加パッケージの自動導入はありません。数値診断は既存のmpmathを検出した場合に実行し、未導入時は `numerical.json` に `diagnostic: backend_unavailable` を残して、対応する解析・Lean・保存を続けます。

## すぐに検証する

出力先は未使用のディレクトリを指定します。

```sh
python3 -m special_function_agent verify examples/gamma-recurrence.txt --route direct --output runs/gamma-direct
python3 -m special_function_agent verify examples/gamma-recurrence.txt --route steps --output runs/gamma-steps
python3 -m special_function_agent verify examples/beta-integral.txt --route direct --output runs/beta-direct
python3 -m special_function_agent verify examples/scaled-gamma-integral.txt --route steps --output runs/scaled-steps
python3 -m special_function_agent replay runs/gamma-direct
```

直接経路は登録された補題を元の命題へ適用します。ステップ経路は各 `before = after` を同じ全条件で検査し、終点をつないで元の等式を証明します。自然言語の理由は候補として保存し、判定は構造化等式とLeanの結果に基づきます。

任意の名前を使う例：

```text
Gamma(shape+1) = shape*Gamma(shape); shape > 0
```

構造化入力だけを確認する場合：

```sh
python3 -m special_function_agent parse examples/beta-integral.txt --output runs/beta.target.json
```

## Codexへの依頼例

このリポジトリをCodexで開き、次のように依頼します。プロジェクトの [AGENTS.md](AGENTS.md) に検査の手順を記載しています。

> `examples/beta-integral.txt` の元式と全条件を確認し、直接証明と自然言語ステップ証明の両方を実行してください。各証明をreplayし、Leanの状態・数値診断・残る条件を区別して説明してください。

> 正の実数 shape, rate に対する `int(0,infinity,t^(shape-1)*exp(-rate*t),t)=rate^(-shape)*Gamma(shape)` を構造化してください。元の全条件を保持してLean検証し、成功した証明を外部archiveへ保存してください。

既存のCodex CLIで新たな候補を生成する場合は、本人のCLI認証を利用します。モデルはCLI設定を引き継ぎ、推論量はUltraです。

```sh
python3 -m special_function_agent.generate examples/beta-integral.target.json --route direct --output runs/beta-ai-direct
python3 -m special_function_agent.generate examples/beta-integral.target.json --route steps --output runs/beta-ai-steps
```

候補JSONは元命題を置き換えるフィールドや追加条件を受け付けません。数式と証明手順の閉じたスキーマからLeanを組み立て、`sorry` や標準公理以外への依存を監査します。

## 入力範囲と判定

v2は最大3個の自由実変数と整数次数 `n` に対応します。実変数名は予約語を除く `[A-Za-z][A-Za-z0-9_]{0,31}`、積分変数は別の束縛名として保持します。名前・型・自由変数と束縛変数の衝突を検査します。

- 実数の正性・比較は正確な有理数との比較で指定します。例：`shape > 0`、`0 < lambda < 1`。
- 関数値の零・非零は `X_01(z,lambda*z)=0`、`Gamma(shape)!=0` のように指定します。
- `Gamma`、`exp`、実数冪、有限区間積分、正の半直線上の積分を構造化できます。初期の完全証明レシピは上の3公式と実数の環計算です。
- `int(0,1,body,t)` と `int(0,infinity,body,t)`、対応するLaTeX記法を使用できます。詳細は[数理仕様](docs/mathematics.md)。
- 仮定不足は `needs_conditions`、対応レシピ・証明が未完成なら `unresolved`。既存v1で否定命題のLean証明が得られたときは `refuted`。v2の数値不一致は反例候補として保存します。

Yの交差積は `X_nm(s,t)=J_n(s)Y_m(t)-Y_n(s)J_m(t)`。固定mathlibにこの実Yの接続が揃っていないため、完全証明・条件付き代数証明・数値診断を別項目として扱います。根条件例：

```sh
python3 -m special_function_agent verify examples/cross-product-root.txt --output runs/cross-product
```

この例では左分母の末尾は `X_02`、右分子は微分を含まない `X_00` です。解析テンプレートは根条件・係数・次数・両辺の一致を検査して選択します。Yの定義、漸化式、Wronskian、ODEとエネルギー積分による分母非零性の形式化が後続の作業です。

## 外部archive

既定保存先は `~/SpecialFunctionProofAgentData/archive`、変更は `SPECIAL_FUNCTION_ARCHIVE_DIR` または `--archive-dir` で指定します。元Besselの個人archiveは独立しています。

```sh
python3 -m special_function_agent verify examples/gamma-recurrence.txt --route direct --output runs/gamma-saved --archive
python3 -m special_function_agent archive list
python3 -m special_function_agent archive replay RECORD_ID
python3 -m special_function_agent archive import-bessel /path/to/bessel/verification-run
```

Besselからの取り込みは明示した1記録を再検証し、出典と元環境を保存します。保存ファイルの改変・全条件や変数の相違・現在の数学環境との差異を検査します。[保存仕様](docs/archive.md)。

## 検証と今後の範囲

```sh
lake build
SF_RUN_LEAN_TESTS=1 BESSEL_RUN_LEAN_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/replay_examples.py
```

後続ロードマップは Hermite/erf → Legendre/Laguerre/Jacobi → hypergeometric/confluent/Airy → associated Legendre/spherical harmonics/elliptic の順です。一般複数根系、Yの微積分、複素枝、近似誤差と漸近剰余の保証も後続範囲です。現在は少数の関数族と閉じたレシピを登録し、必要な証明が完成したものから追加します。
