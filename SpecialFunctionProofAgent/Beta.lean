import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

open MeasureTheory Set

namespace SpecialFunctionProofAgent

/-- Real powers in the beta integral agree with complex powers on the interval. -/
theorem beta_integral_ofReal (a b : ℝ) :
    ((∫ t in (0 : ℝ)..1, t ^ (a - 1) * (1 - t) ^ (b - 1) : ℝ) : ℂ) =
      Complex.betaIntegral (a : ℂ) (b : ℂ) := by
  rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro t ht
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.1.le,
    Complex.ofReal_cpow (sub_nonneg.mpr ht.2.le)]
  push_cast
  rfl

/-- Euler's beta integral for positive real parameters. -/
theorem beta_integral (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t in (0 : ℝ)..1, t ^ (a - 1) * (1 - t) ^ (b - 1)) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  apply Complex.ofReal_injective
  rw [beta_integral_ofReal,
    Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using ha) (by simpa using hb)]
  rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal]
  push_cast
  rfl

end SpecialFunctionProofAgent
