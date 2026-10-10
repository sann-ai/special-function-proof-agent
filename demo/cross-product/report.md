# 正実数のBessel診断

((X_{0,0}(z,(lambda*z))^2)/((X_{0,1}(z,z)^2)+(((lambda^2)*X_{0,0}(z,(lambda*z)))*X_{0,2}(z,(lambda*z))))) = (((1/lambda)*X_{0,0}(z,(lambda*z)))/(X_{1,1}(z,(lambda*z))-(lambda*X_{0,0}(z,(lambda*z)))))

条件：lambda is real、z is real、lambda > 0、lambda < 1、z > 0、X_{0,1}(z,(lambda*z)) = 0

状態：unresolved。この記録は明示前提からの条件付き証拠を保持します。同じ元式の完全証明はdirect/steps経路で新しく保存できます。

数値診断：no_mismatch_found。有限標本の結果を numerical.json に保存しました。

## 解析テンプレート
次数2の漸化式と根条件より C=-A。
交差積の行列式とWronskianより lam*A*B=Q^2、Q=-2/(pi*z)。
u(t)=X_00(z,t) のBessel方程式を積分すると Q^2-lam^2*A^2=(2/z^2)*integral(lam*z,z,t*u(t)^2) > 0。
分母を lam*A*(B-lam*A) に因数分解し、非零性を用いて約分する。

## 条件付きLean
明示前提の下での検査：True。仮定：0 < lam、Q != 0、C = -A、lam*A*B = Q^2、0 < Q^2-lam^2*A^2
残る形式化：Bessel Y and X definitions、root recurrence、Wronskian scaling、positive energy integral
