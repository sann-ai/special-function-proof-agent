import SpecialFunctionProofAgent.Erf
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory

namespace SpecialFunctionProofAgent

/-- The real exponential defined by its factorial power series. -/
noncomputable def exponentialSeries (x : ℝ) : ℝ :=
  ∑' n : ℕ, x ^ n / (n.factorial : ℝ)

/-- The factorial power series has sum `Real.exp x` for every real `x`. -/
theorem hasSum_exponentialSeries (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x

/-- The defining series converges at every real argument. -/
theorem summable_exponentialSeries (x : ℝ) :
    Summable (fun n : ℕ => x ^ n / (n.factorial : ℝ)) :=
  (hasSum_exponentialSeries x).summable

/-- The convergent series agrees with the standard real exponential. -/
theorem exponentialSeries_eq_exp (x : ℝ) : exponentialSeries x = Real.exp x :=
  (hasSum_exponentialSeries x).tsum_eq

/-- The oriented Gaussian integral from zero to a real endpoint. -/
noncomputable def gaussianPrimitive (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2))

/-- The Gaussian integrand is integrable over every oriented finite real interval. -/
theorem intervalIntegrable_gaussian (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.exp (-(t ^ 2))) volume a b := by
  have hc : Continuous (fun t : ℝ => Real.exp (-(t ^ 2))) := by fun_prop
  exact hc.intervalIntegrable a b

/-- The primitive uses the standard real error-function normalization. -/
theorem gaussianPrimitive_eq_erf (x : ℝ) :
    gaussianPrimitive x = Real.sqrt Real.pi / 2 * erf x := by
  simpa only [gaussianPrimitive, erf_zero, sub_zero] using gaussian_integral 0 x

/-- The fundamental theorem of calculus holds at every real endpoint. -/
theorem hasDerivAt_gaussianPrimitive (x : ℝ) :
    HasDerivAt gaussianPrimitive (Real.exp (-(x ^ 2))) x := by
  have hc : Continuous (fun t : ℝ => Real.exp (-(t ^ 2))) := by fun_prop
  exact intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_gaussian 0 x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- The solution at all real times of `y' = rate * y`, with initial time zero. -/
noncomputable def homogeneousIVPSolution (rate initial x : ℝ) : ℝ :=
  initial * Real.exp (rate * x)

/-- The explicit exponential representation of the homogeneous IVP solution. -/
theorem homogeneousIVPSolution_eq_exp (rate initial x : ℝ) :
    homogeneousIVPSolution rate initial x = initial * Real.exp (rate * x) := rfl

/-- The explicit solution satisfies the differential equation at every real time. -/
theorem hasDerivAt_homogeneousIVPSolution (rate initial x : ℝ) :
    HasDerivAt (homogeneousIVPSolution rate initial)
      (rate * homogeneousIVPSolution rate initial x) x := by
  unfold homogeneousIVPSolution
  convert (((hasDerivAt_id x).const_mul rate).exp.const_mul initial) using 1 <;>
    first | rfl | (simp only [id_eq]; ring)

/-- The initial value is taken at time zero. -/
@[simp] theorem homogeneousIVPSolution_zero (rate initial : ℝ) :
    homogeneousIVPSolution rate initial 0 = initial := by
  simp [homogeneousIVPSolution]

/-- Every everywhere-differentiable solution with the given initial value is this solution. -/
theorem homogeneousIVPSolution_unique (rate initial : ℝ) (y : ℝ → ℝ)
    (hy : ∀ x, HasDerivAt y (rate * y x) x) (h0 : y 0 = initial) :
    y = homogeneousIVPSolution rate initial := by
  have hfactor (x : ℝ) :
      HasDerivAt (fun t => y t * Real.exp (-rate * t)) 0 x := by
    convert (hy x).mul (((hasDerivAt_id x).const_mul (-rate)).exp) using 1 <;>
      first | rfl | ring
  have hconst (x : ℝ) : y x * Real.exp (-rate * x) = initial := by
    have hc := is_const_of_deriv_eq_zero
      (fun t => (hfactor t).differentiableAt) (fun t => (hfactor t).deriv) x 0
    simpa only [mul_zero, Real.exp_zero, mul_one, h0] using hc
  funext x
  have hx := congrArg (fun value : ℝ => value * Real.exp (rate * x)) (hconst x)
  simpa only [mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero,
    mul_one, homogeneousIVPSolution] using hx

/-- The global real homogeneous IVP has exactly one solution for every real rate and initial value. -/
theorem existsUnique_homogeneousIVPSolution (rate initial : ℝ) :
    ∃! y : ℝ → ℝ, (∀ x, HasDerivAt y (rate * y x) x) ∧ y 0 = initial := by
  refine ⟨homogeneousIVPSolution rate initial, ⟨?_, homogeneousIVPSolution_zero rate initial⟩, ?_⟩
  · exact hasDerivAt_homogeneousIVPSolution rate initial
  · intro y hy
    exact homogeneousIVPSolution_unique rate initial y hy.1 hy.2

end SpecialFunctionProofAgent
