import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

namespace SpecialFunctionProofAgent

/-- Standard Legendre polynomial with `P₀ = 1` and `P₁ = x`.
Mathlib's shifted convention is `Pₙ(1 - 2x)`. -/
noncomputable def legendreP (n : ℕ) (x : ℝ) : ℝ :=
  Polynomial.aeval ((1 - x) / 2) (Polynomial.shiftedLegendre n)

/-- Exact change of variables from the standard to mathlib's shifted convention. -/
theorem legendreP_shifted (n : ℕ) (x : ℝ) :
    legendreP n (1 - 2 * x) = Polynomial.aeval x (Polynomial.shiftedLegendre n) := by
  unfold legendreP
  rw [show (1 - (1 - 2 * x)) / 2 = x by ring]

/-- Standard finite power series, equivalently the Jacobi `α = β = 0` series
in DLMF 18.5.7: https://dlmf.nist.gov/18.5.E7. -/
theorem legendreP_finite_sum (n : ℕ) (x : ℝ) :
    legendreP n x = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * ((n + k).choose n : ℝ) * ((x - 1) / 2) ^ k := by
  simp only [legendreP, Polynomial.shiftedLegendre, map_sum, map_mul, map_pow,
    Polynomial.aeval_X, map_neg, map_one, map_natCast]
  apply Finset.sum_congr rfl
  intro k hk
  have h : ((x - 1) / 2) ^ k = (-1 : ℝ) ^ k * ((1 - x) / 2) ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  rw [h]
  ring

@[simp] theorem legendreP_zero (x : ℝ) : legendreP 0 x = 1 := by
  simp [legendreP_finite_sum]

@[simp] theorem legendreP_one (x : ℝ) : legendreP 1 x = x := by
  simp [legendreP_finite_sum, Finset.sum_range_succ]
  ring

@[simp] theorem legendreP_two (x : ℝ) : legendreP 2 x = (3 * x ^ 2 - 1) / 2 := by
  norm_num [legendreP_finite_sum, Finset.sum_range_succ, Nat.choose]
  ring

/-- Parity for every natural degree and every real argument. -/
theorem legendreP_neg (n : ℕ) (x : ℝ) :
    legendreP n (-x) = (-1 : ℝ) ^ n * legendreP n x := by
  unfold legendreP
  rw [Polynomial.shiftedLegendre_eval_symm]
  rw [show 1 - (1 - -x) / 2 = (1 - x) / 2 by ring]

@[simp] theorem legendreP_at_one (n : ℕ) : legendreP n 1 = 1 := by
  rw [legendreP_finite_sum, Finset.sum_range_succ']
  simp

@[simp] theorem legendreP_at_neg_one (n : ℕ) : legendreP n (-1) = (-1 : ℝ) ^ n := by
  rw [legendreP_neg, legendreP_at_one, mul_one]

end SpecialFunctionProofAgent
