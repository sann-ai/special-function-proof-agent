# Codexからの共通操作

プロジェクト全体のルールは [AGENTS.md](../AGENTS.md) にあります。入力をparseし、全仮定・型・束縛を確認してから検証します。ユーザーが指定した全条件を保存し、証明候補で追加しません。

ローカルで登録済みのGamma/Beta/Hermite/erf、Legendre/Laguerre/Jacobi、固定半整数Y・整数Yレシピを使えます。例えばBeta積分は次のように検査します。

```sh
python3 -m special_function_agent verify examples/beta-integral.txt --route direct --output runs/beta-direct
python3 -m special_function_agent verify examples/beta-integral.txt --route steps --output runs/beta-steps
python3 -m special_function_agent replay runs/beta-steps
```

AIがレシピ/理由を選ぶ場合は `python3 -m special_function_agent.generate examples/beta-integral.target.json --route steps --output runs/beta-ai` を使います。既存Codex CLIのモデルと本人の認証を利用し、Ultraで候補を生成します。targetは生成側へ固定データとして渡し、応答はproofだけを受け取ります。

依頼例：「正のshape,rateについてGamma積分を検証し、元命題のLean状態・数値診断・残る定義域条件を確認してください。直接/ステップ両経路をreplayし、外部archiveに保存してください。」

## Hermiteと誤差関数

`H_n` は物理学規約、`He_n` は確率論規約です。Hermiteの次数は `n natural` と宣言し、微分の `H_{n-1}` / `He_{n-1}` に必要な `n>=1` を元条件に含めます。実数の引数には正値条件は不要です。誤差関数は `erf(x)=2/sqrt(pi)*int(0,x,exp(-t^2),t)` の定義を使います。

```sh
python3 -m special_function_agent verify examples/hermite-h-derivative.txt --route direct --output runs/hermite-direct
python3 -m special_function_agent verify examples/erf-derivative.txt --route steps --output runs/erf-steps
python3 -m special_function_agent verify examples/gaussian-finite-integral.txt --route steps --output runs/gaussian-steps
python3 -m special_function_agent.generate examples/hermite-h-derivative.target.json --route direct --output runs/hermite-ai --archive
python3 -m special_function_agent.generate examples/erf-derivative.target.json --route steps --output runs/erf-ai --archive
```

依頼例：「物理学規約のHermite微分公式を `n natural,n>0,x real` の全条件で検証してください。次に誤差関数の微分と、任意実端点のGaussian積分をステップ経路で検証してください。各段階で定義・規約・条件を保持し、証拠を保存してreplayしてください。」

## 多項式と固定半整数Y

Legendre/Laguerre/Jacobiは自然数次数を使い、引数とパラメータを実数として宣言します。微分では他のパラメータを固定し、次数 `n-1` の下限条件を元入力から確認します。Laguerreの通常規約はα=0です。[定義・対応公式](orthogonal-polynomials.md)を参照してください。

```sh
python3 -m special_function_agent verify examples/jacobi-derivative.txt --route direct --output runs/jacobi-direct
python3 -m special_function_agent verify examples/yhalf-derivative.txt --route steps --output runs/yhalf-steps
python3 -m special_function_agent replay runs/yhalf-steps
```

依頼例：「`examples/jacobi-derivative.txt` を、自然数n≥1、実数a,b,xの条件で検証してください。a,bを固定したx微分として、元式・全条件・規約を確認し、両経路の証明を保存してreplayしてください。」

依頼例：「`examples/yhalf-recurrence.txt` と `examples/yhalf-derivative.txt` を直接・ステップ両経路で検証してください。明示名 `YNoninteger` の固定次数−1/2・1/2・3/2と正の実引数を保持し、Leanの完全証明と保存証明のreplayを確認してください。」

`YNoninteger` は標準のJ接続式から定義した非整数Yへ接続します。整数Yは次数微分の定義に対して、次数方向の微分可能性と標準整数極限を証明しました。任意整数n、x>0の三項漸化式に加え、次の引数微分・Wronskianも完全証明できます。[Yの形式化範囲](bessel-y-formalization.md)に定義と各条件を記載しています。

## 整数Yの引数微分・Wronskian・同点交差積

`integer-y-zero-derivative` と `integer-y-one-derivative` はx>0での `Y_0'=-Y_1`、`Y_1'=Y_0-Y_1/x`、`integer-y-wronskian` は任意整数nとx>0での `J_{n+1}Y_n-J_nY_{n+1}=2/(pi*x)`、`integer-y-cross-same-point` はx>0での `X_01(x,x)=-2/(pi*x)` です。各例は `examples/` に `.txt` と `.target.json` があり、direct/steps両経路を使えます。次数・引数の微分交換とWronskianの定数2/πは既存の標準J/Y定義から証明済みです。

```sh
python3 -m special_function_agent verify examples/integer-y-zero-derivative.txt --route direct --output runs/y0-direct --archive
python3 -m special_function_agent verify examples/integer-y-wronskian.txt --route steps --output runs/y-wronskian-steps --archive
python3 -m special_function_agent replay runs/y-wronskian-steps
```

依頼例：「整数Yの4例を直接・自然言語ステップ両経路で検証してください。微分する実変数とx>0、Wronskianの `n integer`、同点交差積の2引数と負符号を保持し、元命題の完全証明を保存してreplayしてください。」

## 引き継いだBesselの操作例

# Codexから使う手順

このリポジトリで恒等式を調べる際は、[導入手順](setup.md)と[蓄積機能](archive.md)を参照し、
次の順で進めます。

1. 元の式と全条件を保存し、`parse` の正規化表示を確認する。対応する条件が不足する場合は
   `needs_conditions` と理由を保存して、必要な条件を利用者に確認する。
2. `archive search` / `archive show` で関連記録と条件を読む。文字列検索の一致は候補の選択に使い、
   実際の再利用には命題全体と条件の一致を確認する。
3. 新しい出力先で `python3 -m special_function_agent.generate TARGET.json --route direct --output DIR --archive`
   を実行する。段階経路には `--route steps` を使う。生成器自身が同一命題・同一経路の保存証拠を
   再検査し、利用可能ならAIを呼ばず再利用する。
4. 結果を `proved` / `refuted` / `unresolved` / `needs_conditions` で報告する。
   数値診断は反例候補として併記する。
5. 証拠と日本語レポートの保存場所、アーカイブ記録IDを示す。保存証拠の再検査が必要な場合は
   `archive replay RECORD_ID` を使う。

整数Yの登録漸化式・引数微分・Wronskian・同点交差積、および次の根条件付き分数式以外の `Y_n`・`Y(order,x)`・交差積を含むschema version 2の診断入力は、3のAI証明探索の代わりに
`python3 -m special_function_agent verify INPUT --output DIR --archive` で診断する。
生成器へ渡した場合も診断へ進み、元の式と全条件を保持する。

`examples/cross-product-root.txt` は、`z>0`、`0<lambda<1`、`X_01(z,lambda*z)=0` の元条件から完全証明する。
正エネルギー積分を通じて左分母の正値性と右分母の非零性を導き、X₀₂を含む左分母とX₀₀の右分子を保持する。

```sh
python3 -m special_function_agent verify examples/cross-product-root.txt --route direct --output runs/cross-root-direct --archive
python3 -m special_function_agent verify examples/cross-product-root.txt --route steps --output runs/cross-root-steps --archive
python3 -m special_function_agent replay runs/cross-root-steps
```

依頼例：「根条件付き交差積を元の3条件で両経路から検証してください。左分母のX₀₂、右分子のX₀₀、変数対応と両分母の非零証明を確認し、完全証明を保存してreplayしてください。」

旧 `proof.mode: diagnostic` の記録は元の条件付きscopeを保持する。新たに同じ診断経路を選ぶ場合は `--route diagnostic` を指定し、`unresolved`、`full_bessel_proof: false` と条件付き代数証明の結果を報告する。数値バックエンドの有無と有限標本の結果は、選んだLean検証経路と併せて記録する。

外部の個人用保存先は上流GitHubへのcommit対象に含めません。配布用の共通例へ追加する場合は、
利用者が公開対象として選んだ内容だけを別途レビューします。
生成器は空の一時ディレクトリで動くため、この使用文書の読み込みをAIへ暗黙には期待せず、
アーカイブの完全一致検索と再検査をPython側で実行します。

そのまま使える依頼例:

> このリポジトリで、J_{n-1}(x)+J_{n+1}(x)=2n J_n(x)/x を、nは整数・x>0の条件で検証してください。
> 元の命題と条件を固定し、個人用アーカイブを検索してください。既存証拠を再検査して再利用するか、
> AIで直接経路と段階経路を生成してLeanで検査し、すべての試行を保存してください。
> 4状態の判定、条件、レポートと証明の保存場所、記録IDを教えてください。

## 一般Legendre直交性・規格化と整数Y

依頼例：「`examples/legendre-orthogonal.txt` と `examples/legendre-norm.txt` を両経路で検証してください。自然数m,nの型、m≠n、区間[-1,1]を保持し、証明を保存して同じ命題に再利用してください。」

依頼例：「`examples/integer-y-complete.txt` を任意整数n、x>0で直接・自然言語ステップ両経路へ接続してください。標準整数Yの定義と極限、生成定理の全前提を確認し、完全証明をarchiveへ保存してください。」

古い整数Y・根条件付き交差積のdiagnostic記録は元ファイルと明示前提を保持します。同じ診断経路を選ぶには `--route diagnostic` を指定します。完全証明へ移す場合は、保存requestからproofを除いたtargetを `verify --route direct` または `--route steps` に渡し、同じtarget IDに新しい履歴を追加します。整数Y・交差積の具体的手順は[保存仕様](archive.md#条件付き記録から完全証明へ)を参照してください。
