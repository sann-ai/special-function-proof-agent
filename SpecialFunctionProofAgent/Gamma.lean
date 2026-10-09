import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

open MeasureTheory Set

namespace SpecialFunctionProofAgent

/-- The Gamma recurrence on the positive real axis. -/
theorem gamma_recurrence (x : ℝ) (hx : 0 < x) :
    Real.Gamma (x + 1) = x * Real.Gamma x :=
  Real.Gamma_add_one (ne_of_gt hx)

/-- The Gamma integral with a positive exponential scale. -/
theorem gamma_scaled_integral (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    (∫ t in Ioi (0 : ℝ), t ^ (a - 1) * Real.exp (-r * t)) =
      r ^ (-a) * Real.Gamma a := by
  simpa only [neg_mul, one_div, Real.rpow_neg_eq_inv_rpow] using
    Real.integral_rpow_mul_exp_neg_mul_Ioi ha hr

end SpecialFunctionProofAgent
