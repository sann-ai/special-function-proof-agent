import SpecialFunctionProofAgent.PolynomialSeries
import SpecialFunctionProofAgent.Legendre

namespace SpecialFunctionProofAgent

private noncomputable def jacobiCoefficient (n : ℕ) (a b : ℝ) (k : ℕ) : ℝ :=
  (ascPochhammer ℝ k).eval ((n : ℝ) + a + b + 1) *
    (ascPochhammer ℝ (n - k)).eval (a + k + 1) /
      (k.factorial * (n - k).factorial : ℝ)

/-- Jacobi polynomial with the DLMF 18.5.7 normalization, extended polynomially
in both real parameters: https://dlmf.nist.gov/18.5.E7. -/
noncomputable def jacobiP (n : ℕ) (a b x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), jacobiCoefficient n a b k * ((x - 1) / 2) ^ k

/-- The defining Pochhammer finite sum exposes the standard normalization. -/
theorem jacobiP_finite_sum (n : ℕ) (a b x : ℝ) :
    jacobiP n a b x = ∑ k ∈ Finset.range (n + 1),
      (ascPochhammer ℝ k).eval ((n : ℝ) + a + b + 1) *
        (ascPochhammer ℝ (n - k)).eval (a + k + 1) /
          (k.factorial * (n - k).factorial : ℝ) * ((x - 1) / 2) ^ k := rfl

@[simp] theorem jacobiP_zero (a b x : ℝ) : jacobiP 0 a b x = 1 := by
  simp [jacobiP, jacobiCoefficient]

@[simp] theorem jacobiP_one (a b x : ℝ) :
    jacobiP 1 a b x = ((a - b) + (a + b + 2) * x) / 2 := by
  norm_num [jacobiP, jacobiCoefficient, Finset.sum_range_succ]
  ring

/-- Degree two in a form that remains valid for all real parameters. -/
@[simp] theorem jacobiP_two (a b x : ℝ) :
    jacobiP 2 a b x = ((a + 1) * (a + 2)) / 2 +
      (a + b + 3) * (a + 2) * ((x - 1) / 2) +
      ((a + b + 3) * (a + b + 4)) / 2 * ((x - 1) / 2) ^ 2 := by
  norm_num [jacobiP, jacobiCoefficient, Finset.sum_range_succ,
    ascPochhammer_succ_left, Polynomial.eval_comp]
  ring

/-- The value at the right endpoint in the standard Jacobi normalization. -/
theorem jacobiP_at_one (n : ℕ) (a b : ℝ) :
    jacobiP n a b 1 = (ascPochhammer ℝ n).eval (a + 1) / (n.factorial : ℝ) := by
  rw [jacobiP, Finset.sum_range_succ']
  simp [jacobiCoefficient]

private theorem jacobiCoefficient_succ (n k : ℕ) (a b : ℝ) :
    jacobiCoefficient (n + 1) a b (k + 1) * ((k + 1 : ℕ) : ℝ) =
      ((n : ℝ) + a + b + 2) * jacobiCoefficient n (a + 1) (b + 1) k := by
  simp only [jacobiCoefficient, Nat.add_sub_add_right, Nat.cast_add, Nat.cast_one,
    Nat.factorial_succ, Nat.cast_mul]
  rw [ascPochhammer_succ_left]
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_one]
  have h₁ : ((n : ℝ) + 1 + a + b + 1) + 1 = (n : ℝ) + (a + 1) + (b + 1) + 1 := by ring
  have h₂ : a + ((k : ℝ) + 1) + 1 = a + 1 + k + 1 := by ring
  rw [h₁, h₂]
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Differentiation lowers degree and raises both Jacobi parameters. -/
theorem hasDerivAt_jacobiP_succ (n : ℕ) (a b x : ℝ) :
    HasDerivAt (jacobiP (n + 1) a b)
      (((n : ℝ) + a + b + 2) / 2 * jacobiP n (a + 1) (b + 1) x) x := by
  have h := (hasDerivAt_finitePowerSeries (jacobiCoefficient (n + 1) a b) n
      ((x - 1) / 2)).comp x (((hasDerivAt_id x).sub_const 1).div_const 2)
  convert h using 1
  · rfl
  · simp only [jacobiP, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [jacobiCoefficient_succ]
    ring

/-- DLMF 18.9.15 for positive natural degree and arbitrary real parameters. -/
theorem jacobiP_derivative (n : ℕ) (a b x : ℝ) (hn : 1 ≤ n) :
    deriv (jacobiP n a b) x =
      ((n : ℝ) + a + b + 1) / 2 * jacobiP (n - 1) (a + 1) (b + 1) x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [(hasDerivAt_jacobiP_succ k a b x).deriv]
  simp only [Nat.succ_sub_one, Nat.cast_succ]
  ring

/-- All natural degrees of Jacobi at `α = β = 0` agree with standard Legendre.
The proof identifies the Pochhammer coefficients with the two binomial coefficients. -/
theorem jacobiP_zero_zero (n : ℕ) (x : ℝ) :
    jacobiP n 0 0 x = legendreP n x := by
  rw [jacobiP, legendreP_finite_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hc : (ascPochhammer ℝ k).eval ((n : ℝ) + 1) *
      (ascPochhammer ℝ (n - k)).eval ((k : ℝ) + 1) /
        (k.factorial * (n - k).factorial : ℝ) =
          (n.choose k : ℝ) * ((n + k).choose n : ℝ) := by
    rw [← Nat.cast_add_one, ← Nat.cast_add_one,
      ascPochhammer_nat_eq_natCast_ascFactorial,
      ascPochhammer_nat_eq_natCast_ascFactorial,
      Nat.ascFactorial_eq_factorial_mul_choose,
      Nat.ascFactorial_eq_factorial_mul_choose,
      Nat.add_sub_of_le hkn, Nat.choose_symm hkn]
    rw [show (n + k).choose k = (n + k).choose n from Nat.choose_symm_add.symm]
    push_cast
    field_simp
  simp only [jacobiCoefficient, add_zero, zero_add, hc]

@[simp] theorem jacobiP_legendre_zero (x : ℝ) : jacobiP 0 0 0 x = legendreP 0 x := by
  simp

@[simp] theorem jacobiP_legendre_one (x : ℝ) : jacobiP 1 0 0 x = legendreP 1 x := by
  simp

@[simp] theorem jacobiP_legendre_two (x : ℝ) : jacobiP 2 0 0 x = legendreP 2 x := by
  rw [jacobiP_two, legendreP_two]
  ring

end SpecialFunctionProofAgent
