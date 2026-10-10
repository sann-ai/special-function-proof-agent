# Special Function Proof Agent

((X_{0,0}(z,(lambda*z))^2)/((X_{0,1}(z,z)^2)+(((lambda^2)*X_{0,0}(z,(lambda*z)))*X_{0,2}(z,(lambda*z))))) = (((1/lambda)*X_{0,0}(z,(lambda*z)))/(X_{1,1}(z,(lambda*z))-(lambda*X_{0,0}(z,(lambda*z)))))

条件：lambda is real、z is real、lambda > 0、lambda < 1、z > 0、X_{0,1}(z,(lambda*z)) = 0

完全Lean証明：proved
数値診断：no_mismatch_found

交差積規約：X_nm(s,t)=J_n(s)*Y_m(t)-Y_n(s)*J_m(t)。
元の根条件と0<λ<1、z>0から標準J・Yの漸化式とWronskianを適用する。正エネルギー積分で左分母の正値性と右分母の非零性を証明し、元の分数等式へ接続する。
