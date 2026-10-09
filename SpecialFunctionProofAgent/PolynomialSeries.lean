import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

namespace SpecialFunctionProofAgent

/-- Termwise differentiation of a finite real power series, with its constant term removed. -/
theorem hasDerivAt_finitePowerSeries (c : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => ∑ k ∈ Finset.range (n + 2), c k * y ^ k)
      (∑ k ∈ Finset.range (n + 1), c (k + 1) * ((k + 1 : ℕ) : ℝ) * x ^ k) x := by
  have h := HasDerivAt.fun_sum (u := Finset.range (n + 2))
    (fun k _ => (hasDerivAt_pow k x).const_mul (c k))
  convert h using 1
  conv_rhs => rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro k hk
  ring

end SpecialFunctionProofAgent
