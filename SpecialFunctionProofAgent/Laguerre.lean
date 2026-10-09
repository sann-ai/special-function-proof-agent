import SpecialFunctionProofAgent.PolynomialSeries

namespace SpecialFunctionProofAgent

private noncomputable def laguerreCoefficient (n : ℕ) (a : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * (ascPochhammer ℝ (n - k)).eval (a + k + 1) /
    ((n - k).factorial * k.factorial : ℝ)

/-- Generalized Laguerre polynomial, with its polynomial extension to all real parameters.
The defining finite sum is DLMF 18.5.12: https://dlmf.nist.gov/18.5.E12.
The ordinary Laguerre polynomial is `laguerreL n 0`. -/
noncomputable def laguerreL (n : ℕ) (a x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), laguerreCoefficient n a k * x ^ k

/-- The standard Pochhammer finite sum, with the sign in the power `(-x)^k`. -/
theorem laguerreL_finite_sum (n : ℕ) (a x : ℝ) :
    laguerreL n a x = ∑ k ∈ Finset.range (n + 1),
      (ascPochhammer ℝ (n - k)).eval (a + k + 1) /
        ((n - k).factorial * k.factorial : ℝ) * (-x) ^ k := by
  unfold laguerreL laguerreCoefficient
  apply Finset.sum_congr rfl
  intro k hk
  rw [neg_pow]
  ring

@[simp] theorem laguerreL_zero (a x : ℝ) : laguerreL 0 a x = 1 := by
  simp [laguerreL, laguerreCoefficient]

@[simp] theorem laguerreL_one (a x : ℝ) : laguerreL 1 a x = a + 1 - x := by
  simp [laguerreL, laguerreCoefficient, Finset.sum_range_succ]
  ring

@[simp] theorem laguerreL_two (a x : ℝ) :
    laguerreL 2 a x = (x ^ 2 - 2 * (a + 2) * x + (a + 1) * (a + 2)) / 2 := by
  norm_num [laguerreL, laguerreCoefficient, Finset.sum_range_succ,
    ascPochhammer_succ_left, Polynomial.eval_comp]
  ring

/-- Value at the origin for arbitrary natural degree. -/
theorem laguerreL_at_zero (n : ℕ) (a : ℝ) :
    laguerreL n a 0 = (ascPochhammer ℝ n).eval (a + 1) / (n.factorial : ℝ) := by
  rw [laguerreL, Finset.sum_range_succ']
  simp [laguerreCoefficient]

@[simp] theorem laguerreL_ordinary_at_zero (n : ℕ) : laguerreL n 0 0 = 1 := by
  rw [laguerreL_at_zero]
  simp [ascPochhammer_eval_one, Nat.factorial_ne_zero]

private theorem laguerreCoefficient_succ (n k : ℕ) (a : ℝ) :
    laguerreCoefficient (n + 1) a (k + 1) * ((k + 1 : ℕ) : ℝ) =
      -laguerreCoefficient n (a + 1) k := by
  simp only [laguerreCoefficient, Nat.add_sub_add_right, Nat.cast_add, Nat.cast_one,
    pow_succ, Nat.factorial_succ, Nat.cast_mul]
  have he : a + (k + 1 : ℝ) + 1 = a + 1 + k + 1 := by ring
  rw [he]
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- The derivative lowers the degree and raises the Laguerre parameter. -/
theorem hasDerivAt_laguerreL_succ (n : ℕ) (a x : ℝ) :
    HasDerivAt (laguerreL (n + 1) a) (-laguerreL n (a + 1) x) x := by
  have h := hasDerivAt_finitePowerSeries (laguerreCoefficient (n + 1) a) n x
  convert h using 1
  · rfl
  · rw [laguerreL, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [laguerreCoefficient_succ]
    ring

/-- DLMF 18.9.23, for natural degree at least one and all real parameter/argument values. -/
theorem laguerreL_derivative (n : ℕ) (a x : ℝ) (hn : 1 ≤ n) :
    deriv (laguerreL n a) x = -laguerreL (n - 1) (a + 1) x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa using (hasDerivAt_laguerreL_succ k a x).deriv

end SpecialFunctionProofAgent
