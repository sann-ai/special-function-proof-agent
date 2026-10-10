import SpecialFunctionProofAgent.Laguerre

namespace SpecialFunctionProofAgent
private noncomputable def laguerreSeriesCoefficient (n : ℕ) (a : ℝ) (k : ℕ) : ℝ :=
  (ascPochhammer ℝ (n - k)).eval (a + k + 1) /
    ((n - k).factorial * k.factorial : ℝ)

private theorem laguerreSeriesCoefficient_raise (n k : ℕ) (a : ℝ) (hk : k ≤ n) :
    ((n : ℝ) + 1 - k) * laguerreSeriesCoefficient (n + 1) a k =
      (a + n + 1) * laguerreSeriesCoefficient n a k := by
  have he : n + 1 - k = (n - k) + 1 := by omega
  unfold laguerreSeriesCoefficient
  rw [he, ascPochhammer_succ_right, Nat.factorial_succ]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_natCast, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk]
  have hpos : (n : ℝ) - k + 1 ≠ 0 := by
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
    linarith
  field_simp
  ring

private theorem laguerreSeriesCoefficient_previous (n k : ℕ) (a : ℝ) (hk : k < n) :
    ((n : ℝ) - k) * laguerreSeriesCoefficient n a k =
      ((k : ℝ) + 1) * (a + k + 1) * laguerreSeriesCoefficient n a (k + 1) := by
  have he : n - k = (n - (k + 1)) + 1 := by omega
  unfold laguerreSeriesCoefficient
  rw [he, ascPochhammer_succ_left, Nat.factorial_succ, Nat.factorial_succ]
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_one, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Nat.cast_sub (show k + 1 ≤ n by omega)]
  have he' : a + (k : ℝ) + 1 + 1 = a + ((k : ℝ) + 1) + 1 := by ring
  rw [he']
  have hpos : (n : ℝ) - ((k : ℝ) + 1) + 1 ≠ 0 := by
    have hkn : (k : ℝ) < n := by exact_mod_cast hk
    linarith
  have hkpos : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The finite series has zero coefficients above its degree. -/
private noncomputable def laguerreSupportedCoefficient (n : ℕ) (a : ℝ) (k : ℕ) : ℝ :=
  if k ≤ n then laguerreSeriesCoefficient n a k else 0

private theorem laguerreSupportedCoefficient_lower (n k : ℕ) (a : ℝ) (hn : 1 ≤ n) (hk : k ≤ n) :
    ((n : ℝ) + a) * laguerreSupportedCoefficient (n - 1) a k =
      ((n : ℝ) - k) * laguerreSupportedCoefficient n a k := by
  by_cases hk' : k ≤ n - 1
  · have h := laguerreSeriesCoefficient_raise (n - 1) k a hk'
    rw [Nat.sub_add_cancel hn] at h
    simp only [Nat.cast_sub hn, Nat.cast_one] at h
    simp only [laguerreSupportedCoefficient, ite_eq_left hk, ite_eq_left hk']
    linear_combination -h
  · have he : k = n := by omega
    subst k
    simp [laguerreSupportedCoefficient, hk']

private theorem laguerreSupportedCoefficient_recurrence_zero (n : ℕ) (a : ℝ) (hn : 1 ≤ n) :
    ((n : ℝ) + 1) * laguerreSupportedCoefficient (n + 1) a 0 =
      (2 * (n : ℝ) + a + 1) * laguerreSupportedCoefficient n a 0 -
      ((n : ℝ) + a) * laguerreSupportedCoefficient (n - 1) a 0 := by
  have h₁ := laguerreSeriesCoefficient_raise n 0 a (by omega)
  have h₂ := laguerreSupportedCoefficient_lower n 0 a hn (by omega)
  simp only [laguerreSupportedCoefficient, Nat.zero_le, ite_true, Nat.cast_zero, sub_zero] at *
  linear_combination h₁ + h₂

private theorem laguerreSupportedCoefficient_recurrence (n k : ℕ) (a : ℝ) (hn : 1 ≤ n) :
    ((n : ℝ) + 1) * laguerreSupportedCoefficient (n + 1) a (k + 1) =
      (2 * (n : ℝ) + a + 1) * laguerreSupportedCoefficient n a (k + 1) + laguerreSupportedCoefficient n a k -
      ((n : ℝ) + a) * laguerreSupportedCoefficient (n - 1) a (k + 1) := by
  rcases lt_trichotomy k n with hk | heq | hk
  · have h₁ := laguerreSeriesCoefficient_raise n (k + 1) a (by omega)
    have h₂ := laguerreSupportedCoefficient_lower n (k + 1) a hn (by omega)
    have h₃ := laguerreSeriesCoefficient_previous n k a hk
    have hb : laguerreSupportedCoefficient n a (k + 1) = laguerreSeriesCoefficient n a (k + 1) :=
      ite_eq_left (by omega)
    have hb' : laguerreSupportedCoefficient n a k = laguerreSeriesCoefficient n a k := ite_eq_left (by omega)
    have ha : laguerreSupportedCoefficient (n + 1) a (k + 1) =
        laguerreSeriesCoefficient (n + 1) a (k + 1) := ite_eq_left (by omega)
    rw [hb] at h₂
    rw [ha, hb, hb']
    simp only [Nat.cast_add, Nat.cast_one] at h₁ h₂
    have hm : (n : ℝ) - k ≠ 0 := by
      have hkn : (k : ℝ) < n := by exact_mod_cast hk
      linarith
    apply mul_left_cancel₀ hm
    linear_combination ((n : ℝ) + 1) * h₁ + ((n : ℝ) - k) * h₂ - h₃
  · subst k
    have hn' : ¬ n + 1 ≤ n - 1 := by omega
    simp [laguerreSupportedCoefficient, laguerreSeriesCoefficient, hn', Nat.factorial_succ]
    field_simp
  · have h₁ : ¬ k + 1 ≤ n + 1 := by omega
    have h₂ : ¬ k + 1 ≤ n := by omega
    have h₃ : ¬ k + 1 ≤ n - 1 := by omega
    have h₄ : ¬ k ≤ n := by omega
    simp [laguerreSupportedCoefficient, h₁, h₂, h₃, h₄]

/-- A positive-power series whose value at `-x` is the existing standard Laguerre function. -/
private noncomputable def laguerreSeriesPolynomial (n : ℕ) (a : ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (laguerreSeriesCoefficient n a k) * Polynomial.X ^ k

private theorem laguerreSeriesPolynomial_coeff (n k : ℕ) (a : ℝ) :
    (laguerreSeriesPolynomial n a).coeff k = laguerreSupportedCoefficient n a k := by
  simp [laguerreSeriesPolynomial, laguerreSupportedCoefficient]

private theorem laguerreSeriesPolynomial_recurrence (n : ℕ) (a : ℝ) (hn : 1 ≤ n) :
    Polynomial.C ((n : ℝ) + 1) * laguerreSeriesPolynomial (n + 1) a =
      Polynomial.C (2 * (n : ℝ) + a + 1) * laguerreSeriesPolynomial n a +
      Polynomial.X * laguerreSeriesPolynomial n a -
      Polynomial.C ((n : ℝ) + a) * laguerreSeriesPolynomial (n - 1) a := by
  ext k
  cases k with
  | zero =>
    simpa [Polynomial.coeff_C_mul, laguerreSeriesPolynomial_coeff] using
      laguerreSupportedCoefficient_recurrence_zero n a hn
  | succ k =>
    simpa only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_mul, laguerreSeriesPolynomial_coeff] using
      laguerreSupportedCoefficient_recurrence n k a hn

/-- The standard generalized Laguerre recurrence for positive natural degree. -/
theorem laguerreL_recurrence (n : ℕ) (a x : ℝ) (hn : 1 ≤ n) :
    ((n : ℝ) + 1) * laguerreL (n + 1) a x =
      (2 * (n : ℝ) + a + 1 - x) * laguerreL n a x -
      ((n : ℝ) + a) * laguerreL (n - 1) a x := by
  have he (m : ℕ) : Polynomial.eval (-x) (laguerreSeriesPolynomial m a) = laguerreL m a x := by
    rw [laguerreSeriesPolynomial, laguerreL_finite_sum]
    simp [Polynomial.eval_finsetSum, laguerreSeriesCoefficient]
  have h := congrArg (Polynomial.eval (-x)) (laguerreSeriesPolynomial_recurrence n a hn)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, he] at h
  linear_combination h

end SpecialFunctionProofAgent
