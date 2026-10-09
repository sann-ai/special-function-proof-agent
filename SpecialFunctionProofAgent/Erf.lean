import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory

namespace SpecialFunctionProofAgent

/-- The real error function, with the standard Gaussian normalization. -/
noncomputable def erf (x : ℝ) : ℝ :=
  2 / Real.sqrt Real.pi * ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2))

private theorem continuous_gaussian : Continuous (fun t : ℝ => Real.exp (-(t ^ 2))) := by
  fun_prop

/-- The error function is differentiable at every real argument. -/
theorem hasDerivAt_erf (x : ℝ) :
    HasDerivAt erf (2 / Real.sqrt Real.pi * Real.exp (-(x ^ 2))) x := by
  exact (intervalIntegral.integral_hasDerivAt_right
    (continuous_gaussian.intervalIntegrable 0 x)
    continuous_gaussian.aestronglyMeasurable.stronglyMeasurableAtFilter
    continuous_gaussian.continuousAt).const_mul _

/-- The derivative of the standard real error function. -/
theorem deriv_erf (x : ℝ) :
    deriv erf x = 2 / Real.sqrt Real.pi * Real.exp (-(x ^ 2)) :=
  (hasDerivAt_erf x).deriv

@[simp] theorem erf_zero : erf 0 = 0 := by
  simp [erf]

/-- The error function is odd on the whole real line. -/
theorem erf_neg (x : ℝ) : erf (-x) = -erf x := by
  have h := intervalIntegral.integral_comp_neg
    (f := fun t : ℝ => Real.exp (-(t ^ 2))) (a := (0 : ℝ)) (b := x)
  simp only [neg_sq, neg_zero] at h
  simp only [erf]
  rw [intervalIntegral.integral_symm (a := -x) (b := (0 : ℝ)), ← h]
  ring

/-- The Gaussian integral over any oriented finite real interval. -/
theorem gaussian_integral (a b : ℝ) :
    (∫ t in a..b, Real.exp (-(t ^ 2))) =
      Real.sqrt Real.pi / 2 * (erf b - erf a) := by
  have hs : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have h := intervalIntegral.integral_interval_sub_left (μ := volume)
    (continuous_gaussian.intervalIntegrable 0 b)
    (continuous_gaussian.intervalIntegrable 0 a)
  rw [← h]
  simp only [erf]
  field_simp

end SpecialFunctionProofAgent
