# Special Function Proof Agent

((J_{(n+1)}(x)*Y_{n}(x))-(J_{n}(x)*Y_{(n+1)}(x))) = (2/(pi*x))

条件：n is int、x is real、x > 0

完全Lean証明：proved
数値診断：no_mismatch_found

整数Y規約：正実軸の標準次数微分式besselYIntを用います。J級数の局所一様収束から次数微分可能性と非整数Yの整数次数極限を証明しています。
正の実引数に対し、標準J・Yの原点極限とGamma反射から定数2/πを確定したWronskianを適用し、交差積の定義順序に対応する符号を保持する。
