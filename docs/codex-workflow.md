# Codexからの共通操作

プロジェクト全体のルールは [AGENTS.md](../AGENTS.md) にあります。入力をparseし、全仮定・型・束縛を確認してから検証します。ユーザーが指定した全条件を保存し、証明候補で追加しません。

ローカルで登録済みのGamma/Beta/Hermite/erf、Legendre/Laguerre/Jacobi、固定半整数Yレシピを使えます。例えばBeta積分は次のように検査します。

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

`YNoninteger` は標準のJ接続式から定義した非整数Yへ接続します。整数Yは次数微分の定義と、次数方向の微分可能性を明示前提に持つ極限補題まで実装しています。[Yの形式化範囲](bessel-y-formalization.md)に各条件と残る義務を記載しています。

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

従来の `Y_n`・`Y(order,x)`・交差積を含むschema version 2の診断入力は、3のAI証明探索の代わりに
`python3 -m special_function_agent verify INPUT --output DIR --archive` で診断する。
生成器へ渡した場合も診断へ進み、元の式と全条件を保持する。
今回の交差積の例には `examples/cross-product-root.txt` を使う。
報告では、元命題の `unresolved`、条件付き代数証明のLean検査、自然言語の解析、
数値診断の結果をそれぞれ示す。残る整数次数でのJの次数微分可能性、次数と引数の微分交換、
Wronskianの正規化、正エネルギー積分と分母非零性の形式化、および
数値バックエンド未導入などの実行状況も保存された結果に沿って説明する。

外部の個人用保存先は上流GitHubへのcommit対象に含めません。配布用の共通例へ追加する場合は、
利用者が公開対象として選んだ内容だけを別途レビューします。
生成器は空の一時ディレクトリで動くため、この使用文書の読み込みをAIへ暗黙には期待せず、
アーカイブの完全一致検索と再検査をPython側で実行します。

そのまま使える依頼例:

> このリポジトリで、J_{n-1}(x)+J_{n+1}(x)=2n J_n(x)/x を、nは整数・x>0の条件で検証してください。
> 元の命題と条件を固定し、個人用アーカイブを検索してください。既存証拠を再検査して再利用するか、
> AIで直接経路と段階経路を生成してLeanで検査し、すべての試行を保存してください。
> 4状態の判定、条件、レポートと証明の保存場所、記録IDを教えてください。
