import SpecialFunctionProofAgent.BesselYInteger
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Order analyticity of the normalized Bessel series

The reciprocal Gamma functional equation gives a uniform exponential bound
on a complex neighborhood of orders zero and one. The factorial in the
regularized hypergeometric coefficients then supplies a summable majorant.
All statements use the existing definitions of J and integer Y.
-/

noncomputable section
namespace SpecialFunctionProofAgent

open Complex Filter
open scoped Topology

/-- A reciprocal-Gamma bound uniform in the number of forward shifts. -/
theorem norm_gamma_inv_order_shift (a : ℂ) (ha : -(1 / 2 : ℝ) ≤ a.re) (k : ℕ) :
    ‖(Gamma (a + 1 + k))⁻¹‖ ≤ ‖(Gamma (a + 1))⁻¹‖ * 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hreal : (1 / 2 : ℝ) ≤ (a + 1 + k).re := by
      simp only [add_re, one_re, natCast_re]
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have hnorm : (1 / 2 : ℝ) ≤ ‖a + 1 + k‖ := hreal.trans (re_le_norm _)
    have hne : a + 1 + (k : ℂ) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnorm
      norm_num at hnorm
    have hinv : ‖(a + 1 + (k : ℂ))⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      apply (inv_le_comm₀ (norm_pos_iff.mpr hne) (by norm_num : (0 : ℝ) < 2)).2
      norm_num
      exact hnorm
    have hshift : a + 1 + (↑(k + 1) : ℂ) = (a + 1 + k) + 1 := by
      push_cast
      ring
    rw [hshift, Gamma_add_one _ hne, mul_inv, norm_mul]
    calc
      ‖(a + 1 + (k : ℂ))⁻¹‖ * ‖(Gamma (a + 1 + k))⁻¹‖
          ≤ 2 * (‖(Gamma (a + 1))⁻¹‖ * 2 ^ k) :=
        mul_le_mul hinv ih (norm_nonneg _) (by norm_num)
      _ = ‖(Gamma (a + 1))⁻¹‖ * 2 ^ (k + 1) := by rw [pow_succ]; ring

/-- The regularized hypergeometric sum is differentiable in its order parameter
on a fixed complex neighborhood containing orders zero and one. -/
theorem differentiableOn_hg_order_zero_one (z : ℂ) :
    DifferentiableOn ℂ (fun a : ℂ => regularizedHGFun 0 {a + 1} z)
      (Metric.ball (1 / 2 : ℂ) 1) := by
  have hc : Continuous (fun a : ℂ => (Gamma (a + 1))⁻¹) := by
    simpa only [one_div, Function.comp_def, id_eq] using
      (differentiable_one_div_Gamma.comp (differentiable_id.add_const 1)).continuous
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (1 / 2 : ℂ) 1).exists_bound_of_continuousOn hc.continuousOn
  have hsum := Complex.differentiableOn_tsum_of_summable_norm
    ((Real.summable_pow_div_factorial (2 * ‖z‖)).mul_left C)
    (F := fun k a => z ^ k * regularizedHGFunCoeff 0 {a + 1} k)
    (U := Metric.ball (1 / 2 : ℂ) 1)
    (fun k => ((differentiable_const _).mul
      ((differentiable_hgCoeff_order k).comp (differentiable_id.add_const 1))).differentiableOn)
    Metric.isOpen_ball ?_
  · apply hsum.congr
    intro a _
    exact (BesselProofAgent.hg_hasSum (a + 1) z).tsum_eq.symm
  · intro k a ha
    have hb : ‖a - (1 / 2 : ℂ)‖ < 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using ha
    have hre := re_le_norm (-(a - (1 / 2 : ℂ)))
    norm_num at hre
    rw [norm_sub_rev] at hre
    have ha' : -(1 / 2 : ℝ) ≤ a.re := by linarith
    have hbound : ‖(Gamma (a + 1 + k))⁻¹‖ ≤ C * 2 ^ k :=
      (norm_gamma_inv_order_shift a ha' k).trans
        (mul_le_mul_of_nonneg_right (hC a (Metric.ball_subset_closedBall ha)) (by positivity))
    simp only [BesselProofAgent.hg_coeff, norm_mul, norm_pow, norm_inv, Complex.norm_natCast]
    calc
      ‖z‖ ^ k * ((↑k.factorial)⁻¹ * ‖Gamma (a + 1 + k)‖⁻¹)
          ≤ ‖z‖ ^ k * ((↑k.factorial)⁻¹ * (C * 2 ^ k)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [norm_inv] using hbound
      _ = C * ((2 * ‖z‖) ^ k / ↑k.factorial) := by rw [mul_pow]; ring

/-- Complex order differentiability of the existing J on a neighborhood of 0 and 1. -/
theorem differentiableOn_besselJ_order_zero_one (x : ℝ) (hx : 0 < x) :
    DifferentiableOn ℂ (fun a : ℂ => Complex.besselJ a (x : ℂ))
      (Metric.ball (1 / 2 : ℂ) 1) := by
  have hp : Differentiable ℂ (fun a : ℂ => ((x : ℂ) / 2) ^ a) :=
    differentiable_id.const_cpow (.inl (div_ne_zero
      (by exact_mod_cast ne_of_gt hx) (by norm_num)))
  exact hp.differentiableOn.mul (differentiableOn_hg_order_zero_one (-((x : ℂ) / 2) ^ 2))

/-- On the positive real axis, J has real order derivatives at both 0 and 1. -/
theorem differentiableAt_realBesselJ_order_zero_one (x : ℝ) (hx : 0 < x) :
    DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 0 ∧
    DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 1 := by
  have h (a : ℝ) (ha : (a : ℂ) ∈ Metric.ball (1 / 2 : ℂ) 1) :
      DifferentiableAt ℝ (fun v : ℝ => realBesselJ v x) a := by
    have hc := (differentiableOn_besselJ_order_zero_one x hx).differentiableAt
      (Metric.isOpen_ball.mem_nhds ha)
    have hr := (hc.restrictScalars ℝ).comp a Complex.differentiable_ofReal.differentiableAt
    exact Complex.reCLM.differentiableAt.comp a hr
  constructor
  · apply h
    norm_num [Metric.mem_ball, dist_eq_norm]
  · apply h
    norm_num [Metric.mem_ball, dist_eq_norm]

/-- The real order derivative exists at every integer order on the positive real axis. -/
theorem differentiableAt_realBesselJ_int_order (n : ℤ) (x : ℝ) (hx : 0 < x) :
    DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) (n : ℝ) := by
  obtain ⟨h0, h1⟩ := differentiableAt_realBesselJ_order_zero_one x hx
  exact differentiableAt_realBesselJ_int_order_of_zero_one n x hx h0 h1

/-- The normalized integer Y satisfies the three-term recurrence on the positive axis. -/
theorem besselYInt_recurrence (n : ℤ) (x : ℝ) (hx : 0 < x) :
    besselYInt (n - 1) x + besselYInt (n + 1) x =
      (2 * (n : ℝ) / x) * besselYInt n x := by
  obtain ⟨h0, h1⟩ := differentiableAt_realBesselJ_order_zero_one x hx
  exact besselYInt_recurrence_of_order_differentiable_zero_one n x hx h0 h1

/-- The standard noninteger connection formula converges to the existing integer Y. -/
theorem tendsto_besselYNoninteger_int (n : ℤ) (x : ℝ) (hx : 0 < x) :
    Tendsto (fun a : ℝ => besselYNoninteger a x) (𝓝[≠] (n : ℝ))
      (𝓝 (besselYInt n x)) := by
  obtain ⟨h0, h1⟩ := differentiableAt_realBesselJ_order_zero_one x hx
  exact tendsto_besselYNoninteger_int_of_order_differentiable_zero_one n x hx h0 h1

#print axioms norm_gamma_inv_order_shift
#print axioms differentiableOn_hg_order_zero_one
#print axioms differentiableOn_besselJ_order_zero_one
#print axioms differentiableAt_realBesselJ_order_zero_one
#print axioms differentiableAt_realBesselJ_int_order
#print axioms besselYInt_recurrence
#print axioms tendsto_besselYNoninteger_int

end SpecialFunctionProofAgent
