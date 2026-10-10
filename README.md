# Special Function Proof Agent

特殊関数の入力を固定した命題へ変換し、制限された証明候補をLeanで検査・保存する独立ツールです。Codexからの依頼とターミナルの両方で利用できます。[Bessel Proof Agentの固定版](UPSTREAM.md)を基盤に、Gamma/Betaの実積分、Hermite・Legendre・Laguerre・Jacobi多項式、誤差関数、正実軸のBessel Yへ拡張しました。ライセンスは[MIT](LICENSE)です。

## 対応する関数と公式

- **完全Lean証明**：正の引数で `Gamma(x+1)=x*Gamma(x)`、正の `a,b` でEulerのBeta積分、正の `a,r` でscaled Gamma積分。直接証明と、理由を添えた等式ステップ証明の両経路があります。
- **Hermite**：物理学規約 `H_n` と確率論規約 `He_n` を区別し、自然数 `n>=1` で両規約の微分公式と `H` の3項漸化式をLean証明します。両規約の0・1次の値にも対応します。
- **誤差関数**：Gaussian積分で定義した実 `erf` の微分、零点での値、奇関数性、任意の実端点間のGaussian積分をLean証明します。負の引数・逆向きの積分にも対応します。
- **Legendre・Laguerre・Jacobi**：自然数次数、実数の引数・パラメータで0〜2次の値をLean証明します。Legendreの偶奇性と両端値、正次数Laguerre/Jacobiの微分、JacobiからLegendreへの特殊化にも対応します。Legendre・一般化Laguerreの三項漸化式（n≥1）と、全自然数次数m≠nでのLegendre直交積分、規格化 `∫[-1,1]P_n(t)^2 dt=2/(2n+1)` にも対応します。[漸化式と直交・規格化](docs/polynomial-calculus.md)。パラメータは有限多項式の定義で全実数を扱います。[定義・公式・条件](docs/orthogonal-polynomials.md)。
- **Bessel J**：引き継いだv1の符号・漸化式・微分・積分・有理数冪の閉じた証明レシピ。[詳しい対応式](docs/bessel-v1.md)。
- **非整数Bessel Y**：明示名 `YNoninteger`、固定次数−1/2・1/2・3/2、正の実引数で、3項漸化式と1/2次の対称微分公式を直接・ステップ両経路でLean証明します。[標準定義との接続と形式化範囲](docs/bessel-y-formalization.md)。
- **整数Bessel Y**：任意整数n、x>0の三項漸化式と `J_{n+1}(x)*Y_n(x)-J_n(x)*Y_{n+1}(x)=2/(pi*x)` を両経路で完全Lean証明します。x>0での `Y_0'=-Y_1`、`Y_1'=Y_0-Y_1/x`、同点交差積 `X_01(x,x)=-2/(pi*x)` にも対応します。J級数の一様評価から次数・引数微分の交換を証明し、原点極限とGamma反射からWronskianの係数と符号を確定しています。
- **根条件付き交差積**：`examples/cross-product-root.txt` を、元の `0<lambda<1,z>0,X_01(z,lambda*z)=0` から完全Lean証明します。正エネルギー積分で両分母の非零性を導き、左末尾X₀₂・右分子X₀₀を保持します。直接・ステップ両経路に対応します。
- **実Bessel J/Y・交差積の診断**：対応する完全証明レシピ以外の入力は、正の引数で数値診断と解析テンプレートを実行します。従来の条件付き整数Y・cross証拠は、明示した `diagnostic` 経路と元の前提を保持して再検査できます。
- **保存と再検査**：元式・変数型・束縛・全条件・関数規約・環境ハッシュ・証明を保持し、再利用前にLeanで再検査します。
- **研究補題の再利用**：既存関数の検証済み等式を外部研究フォルダへ登録し、実変数を置換して別の命題へ適用できます。元補題の条件を新targetの元条件からLeanで確認し、依存証拠を保存します。[Gamma公式をつなぐ例・Codex依頼・選択共有](docs/research-lemmas.md)。

登録表は `special_function_agent/registry.py`、関数別Lean基盤は `BesselProofAgent/` と `SpecialFunctionProofAgent/` にあります。

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
python3 -m special_function_agent verify examples/hermite-h-derivative.txt --route direct --output runs/hermite-direct
python3 -m special_function_agent verify examples/erf-derivative.txt --route steps --output runs/erf-steps
python3 -m special_function_agent replay runs/erf-steps
python3 -m special_function_agent verify examples/jacobi-derivative.txt --route direct --output runs/jacobi-direct
python3 -m special_function_agent verify examples/yhalf-recurrence.txt --route steps --output runs/yhalf-steps
python3 -m special_function_agent verify examples/legendre-recurrence.txt --route direct --output runs/legendre-recurrence
python3 -m special_function_agent verify examples/legendre-adjacent-integral.txt --route steps --output runs/adjacent-integral
python3 -m special_function_agent verify examples/laguerre-recurrence.txt --route steps --output runs/laguerre-recurrence
python3 -m special_function_agent verify examples/legendre-orthogonal.txt --route steps --output runs/orthogonal
python3 -m special_function_agent verify examples/legendre-norm.txt --route direct --output runs/norm
python3 -m special_function_agent verify examples/integer-y-complete.txt --route direct --output runs/integer-y
python3 -m special_function_agent replay runs/integer-y
python3 -m special_function_agent verify examples/integer-y-zero-derivative.txt --route direct --output runs/y-zero-derivative
python3 -m special_function_agent verify examples/integer-y-one-derivative.txt --route steps --output runs/y-one-derivative
python3 -m special_function_agent verify examples/integer-y-wronskian.txt --route steps --output runs/y-wronskian
python3 -m special_function_agent verify examples/integer-y-cross-same-point.txt --route direct --output runs/cross-same-point
python3 -m special_function_agent verify examples/cross-product-root.txt --route steps --output runs/cross-root --archive
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

> 物理学規約の `D_x(H_n(x))=2*n*H_{n-1}(x); n natural,n>=1,x real` を直接・ステップ両経路で検証してください。確率論規約 `He_n` との定義の関係と、次数の全条件を保持し、成功した証拠を保存してください。

> 実数全域で `D_x(erf(x))=2*exp(-x^2)/sqrt(pi)` を積分定義から検証してください。自然言語ステップの各等式をLeanで検査し、負の引数を含む数値診断と保存証明のreplayも実行してください。

> `examples/jacobi-derivative.txt` を、自然数 `n>=1` と実数 `a,b,x` の全条件で検証してください。微分ではa,bを固定し、両経路の証明を保存してreplayしてください。

> `examples/yhalf-recurrence.txt` と `examples/yhalf-derivative.txt` の `YNoninteger` を正実軸で検証してください。各式の直接・ステップ両経路をLeanで検査し、保存証明をreplayしてください。

> `examples/legendre-adjacent-integral.txt` と `examples/laguerre-recurrence.txt` を直接・自然言語ステップ両経路で検査してください。隣接次数と積分区間、自然数次数の下限、Laguerreの実パラメータを保持し、成功した証明をarchiveへ保存して再利用してください。

> `examples/legendre-orthogonal.txt` と `examples/legendre-norm.txt` を直接・自然言語ステップの両経路で検証してください。自然数次数m,n、m≠n、区間[-1,1]を保持し、成功した証明をarchiveへ保存して再利用してください。

> `examples/integer-y-complete.txt` を任意整数n、x>0の元条件で検証してください。標準整数Yへの極限と漸化式の証明を確認し、両経路の証明を保存してreplayしてください。

> `examples/integer-y-zero-derivative.txt`、`integer-y-one-derivative.txt`、`integer-y-wronskian.txt`、`integer-y-cross-same-point.txt` を直接・自然言語ステップ両経路で検証してください。x>0、Wronskianの整数次数と符号、同点交差積の引数を保持し、証拠をarchiveへ保存して再利用してください。

> `examples/cross-product-root.txt` を元の3条件のまま直接・自然言語ステップ両経路で検証してください。左分母のX₀₂、右分子のX₀₀、正エネルギーから両分母の非零性へ進む証明を確認してください。旧条件付き記録を保持し、新しい完全証明をarchiveへ保存して再利用してください。

既存のCodex CLIで新たな候補を生成する場合は、本人のCLI認証を利用します。モデルはCLI設定を引き継ぎ、推論量はUltraです。

```sh
python3 -m special_function_agent.generate examples/beta-integral.target.json --route direct --output runs/beta-ai-direct
python3 -m special_function_agent.generate examples/beta-integral.target.json --route steps --output runs/beta-ai-steps
```

候補JSONは元命題を置き換えるフィールドや追加条件を受け付けません。数式と証明手順の閉じたスキーマからLeanを組み立て、`sorry` や標準公理以外への依存を監査します。

## 入力範囲と判定

v2は最大3個の自由実変数に対応します。次数変数 `n` はBesselでは整数、Hermite・Legendre・Laguerre・Jacobiでは自然数として宣言します。多項式では第2次数 `m natural` も宣言できます。同一名の型は固定し、自然数と実数の重複宣言を拒否します。`m real` は従来どおり実変数です。`YNoninteger` は上記3個の固定有理数次数を使います。実変数名は予約語を除く `[A-Za-z][A-Za-z0-9_]{0,31}`、積分変数は別の束縛名として保持します。名前・型・自由変数と束縛変数の衝突を検査します。

- 実数の正性・比較は正確な有理数との比較で指定します。例：`shape > 0`、`0 < lambda < 1`。
- 自然数次数間の比較は `m!=n`、`m<n`、`m<=n` 等で指定し、元の型と関係を保存します。一般Legendre直交性の条件はLeanで確認します。
- 関数値の零・非零は `X_01(z,lambda*z)=0`、`Gamma(shape)!=0` のように指定します。
- `Gamma`、`H_n`、`He_n`、`Legendre(n,x)`、`Laguerre(n,alpha,x)`、`Jacobi(n,alpha,beta,x)`、`erf`、`YNoninteger`、`exp`、`sqrt`、`pi`、実数冪、有限区間積分、正の半直線上の積分を構造化できます。通常のLaguerre `L_n(x)` は `alpha=0` です。完全証明は登録された公式と実数の環計算に対応します。
- `D_x(expr)` は明示した実変数で微分し、他の自由実変数を固定します。`D(expr)` は自由実変数が1個の場合に使用できます。多項式の次数は非負整数定数または自然数 `m` / `n` と小さい整数の加減算です。次数 `n-1` には `n>=1` 等の明示条件が必要です。`n>0`、`n>=1/2` 等の自然数の離散性を使う条件もLeanで検査します。
- `int(0,1,body,t)` と `int(0,infinity,body,t)`、対応するLaTeX記法を使用できます。詳細は[数理仕様](docs/mathematics.md)。
- 仮定不足は `needs_conditions`、対応レシピ・証明が未完成なら `unresolved`。既存v1で否定命題のLean証明が得られたときは `refuted`。v2の数値不一致は反例候補として保存します。

Yの交差積は `X_nm(s,t)=J_n(s)Y_m(t)-Y_n(s)J_m(t)`。次の固定された根条件付き恒等式は、標準J/Yの定義と積分正性から完全証明します。

```sh
python3 -m special_function_agent verify examples/cross-product-root.txt --route steps --output runs/cross-product
```

この例では左分母の末尾は `X_02`、右分子は微分を含まない `X_00` です。完全証明は根条件・係数・次数・両辺の一致を構造で検査して選択します。標準整数Yの定義から、次数微分可能性・整数極限・漸化式・Y₀とY₁の引数微分、全整数のWronskian係数2/π、正エネルギー積分と両分母の非零性まで接続しました。変数名を変えた同じ構造にも対応します。[数学的な接続](docs/bessel-y-formalization.md)。

旧条件付きcross証拠を明示的に作る場合は `--route diagnostic` を指定します。旧記録はそのscopeで再検査し、完全証明への更新は元のtargetから新しい記録を作成します。

従来と同じ条件付き整数Y証拠を明示的に作る例：

```sh
python3 -m special_function_agent verify examples/integer-y-recurrence.txt --route diagnostic --output runs/integer-y-conditional --archive
python3 -m special_function_agent replay runs/integer-y-conditional
```

このdiagnostic経路の記録は `unresolved` のため、この2コマンドの終了コードは `1` です。条件付き検査の成功は `conditional_lean.accepted: true`、再検査は `conditional_replayed: true` で確認します。`analysis.json`、Lean定理、報告、archive詳細に2前提と残る義務を保存します。

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
python3 scripts/audit_special_functions.py
SF_RUN_LEAN_TESTS=1 BESSEL_RUN_LEAN_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/replay_examples.py
```

Legendre/Laguerre/Jacobiの公開例は、偶奇性・低次数値・端点値・微分・特殊化の17式と、三項漸化式2式・隣接直交積分1式・一般直交積分と規格化の2式です。整数Yの完全証明例は `integer-y-complete`、`integer-y-zero-derivative`、`integer-y-one-derivative`、`integer-y-wronskian`、`integer-y-cross-same-point` です。根条件付き交差積の完全証明例は `cross-product-root` です。半整数Yは `yhalf-recurrence` と `yhalf-derivative` を公開しています。各例の `.txt` と `.target.json` は `examples/` にあります。

後続範囲は、Hermite/Laguerre/Jacobiの直交性・規格化・重み付き積分、Jacobiの一般漸化式、hypergeometric/confluent/Airy、associated Legendre/spherical harmonics/ellipticです。一般複数根系、一般整数次数のY引数微分を使う入力、複素枝、近似誤差と漸近剰余の評価も、それぞれ必要な定義・条件・証明を追加して扱います。研究拡張は自由次数を持つ補題と、新関数の定義・規約・Lean API登録を次段階とします。
