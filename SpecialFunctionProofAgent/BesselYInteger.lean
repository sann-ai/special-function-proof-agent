import SpecialFunctionProofAgent.BesselY
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Integer-order Bessel Y: explicit order-differentiability bridges

The definitions of J and integer Y are imported unchanged from `BesselY`.
The analytic hypotheses below concern differentiation in the order, with the
positive real argument fixed. They remain explicit premises of the integer-Y
results. Coefficient differentiation and propagation along integer orders are
proved here; differentiability of the full order-dependent sum at orders zero
and one remains a separate analytic obligation.
-/

noncomputable section

namespace SpecialFunctionProofAgent

open Complex Filter
open scoped Topology

/-- Every regularized `₀F₁` coefficient is entire in its denominator parameter. -/
theorem differentiable_hgCoeff_order (k : ℕ) :
    Differentiable ℂ (fun a : ℂ => regularizedHGFunCoeff 0 {a} k) := by
  simp_rw [BesselProofAgent.hg_coeff]
  exact (differentiable_const _).mul
    (Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const _))

/-- Each full J-series term is entire in the order on the positive real axis. -/
theorem differentiable_besselJ_series_term_order (x : ℝ) (hx : 0 < x) (k : ℕ) :
    Differentiable ℂ (fun a : ℂ => ((x : ℂ) / 2) ^ a *
      ((-((x : ℂ) / 2) ^ 2) ^ k * regularizedHGFunCoeff 0 {a + 1} k)) := by
  apply Differentiable.mul
  · exact differentiable_id.const_cpow (.inl (div_ne_zero
      (by exact_mod_cast ne_of_gt hx) (by norm_num)))
  · exact (differentiable_const _).mul
      ((differentiable_hgCoeff_order k).comp (differentiable_id.add_const 1))

/-- The order-dependent series terms sum to the existing normalized J. -/
theorem hasSum_besselJ_order_series (a : ℂ) (x : ℝ) :
    HasSum (fun k : ℕ => ((x : ℂ) / 2) ^ a *
      ((-((x : ℂ) / 2) ^ 2) ^ k * regularizedHGFunCoeff 0 {a + 1} k))
      (Complex.besselJ a (x : ℂ)) := by
  simpa only [Complex.besselJ] using
    (BesselProofAgent.hg_hasSum (a + 1) (-((x : ℂ) / 2) ^ 2)).mul_left
      (((x : ℂ) / 2) ^ a)

/-- Differentiating the J recurrence in the order uses exactly three points. -/
theorem realBesselJ_order_deriv_recurrence (a x : ℝ) (hx : 0 < x)
    (hm : DifferentiableAt ℝ (fun v : ℝ => realBesselJ v x) (a - 1))
    (h0 : DifferentiableAt ℝ (fun v : ℝ => realBesselJ v x) a)
    (hp : DifferentiableAt ℝ (fun v : ℝ => realBesselJ v x) (a + 1)) :
    deriv (fun v : ℝ => realBesselJ v x) (a - 1) +
        deriv (fun v : ℝ => realBesselJ v x) (a + 1) =
      (2 / x) * realBesselJ a x +
        (2 * a / x) * deriv (fun v : ℝ => realBesselJ v x) a := by
  have hminus := hm.hasDerivAt.comp a ((hasDerivAt_id a).sub_const 1)
  have hplus := hp.hasDerivAt.comp a ((hasDerivAt_id a).add_const 1)
  have hleft := hminus.add hplus
  have hright := (((hasDerivAt_id a).const_mul 2).div_const x).mul h0.hasDerivAt
  have heq : (fun v : ℝ => realBesselJ (v - 1) x + realBesselJ (v + 1) x) =
      (fun v : ℝ => (2 * v / x) * realBesselJ v x) := by
    funext v
    exact realBesselJ_recurrence v x hx
  simp only [Function.comp_def, id_eq, mul_one] at hleft
  change HasDerivAt (fun v : ℝ => realBesselJ (v - 1) x + realBesselJ (v + 1) x) _ a at hleft
  rw [heq] at hleft
  simpa only [mul_one, id_eq] using hleft.unique hright

/-- Integer Y recurrence from the explicitly stated six order derivatives. -/
theorem besselYInt_recurrence_of_differentiable_order (n : ℤ) (x : ℝ) (hx : 0 < x)
    (hpm : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) ((n : ℝ) - 1))
    (hp0 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) (n : ℝ))
    (hpp : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) ((n : ℝ) + 1))
    (hnm : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) (-(n : ℝ) - 1))
    (hn0 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) (-(n : ℝ)))
    (hnp : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) (-(n : ℝ) + 1)) :
    besselYInt (n - 1) x + besselYInt (n + 1) x =
      (2 * (n : ℝ) / x) * besselYInt n x := by
  have hp := realBesselJ_order_deriv_recurrence (n : ℝ) x hx hpm hp0 hpp
  have hn := realBesselJ_order_deriv_recurrence (-(n : ℝ)) x hx hnm hn0 hnp
  have hs : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← mul_zpow]
    norm_num
  have hsm : (-1 : ℝ) ^ (n - 1) = -((-1 : ℝ) ^ n) := by
    rw [zpow_sub₀ (by norm_num)]
    norm_num [div_eq_mul_inv]
  have hsp : (-1 : ℝ) ^ (n + 1) = -((-1 : ℝ) ^ n) := by
    rw [zpow_add₀ (by norm_num)]
    simp
  have hm : -((n : ℝ) - 1) = -(n : ℝ) + 1 := by ring
  have hp' : -((n : ℝ) + 1) = -(n : ℝ) - 1 := by ring
  simp only [besselYInt, Int.cast_sub, Int.cast_add, Int.cast_one, hsm, hsp, hm, hp']
  rw [realBesselJ_neg_int] at hn
  field_simp at hp hn ⊢
  linear_combination hp - (-1 : ℝ) ^ n * hn - 2 * realBesselJ (n : ℝ) x * hs

/-- The J recurrence propagates order differentiability one step down. -/
theorem differentiableAt_realBesselJ_order_sub_one (a x : ℝ) (hx : 0 < x)
    (h0 : DifferentiableAt ℝ (fun v : ℝ => realBesselJ v x) a)
    (hp : DifferentiableAt ℝ (fun v : ℝ => realBesselJ v x) (a + 1)) :
    DifferentiableAt ℝ (fun v : ℝ => realBesselJ v x) (a - 1) := by
  apply differentiableAt_comp_sub_const.mp
  have heq : (fun v : ℝ => realBesselJ (v - 1) x) =
      (fun v : ℝ => (2 * v / x) * realBesselJ v x - realBesselJ (v + 1) x) := by
    funext v
    linear_combination realBesselJ_recurrence v x hx
  rw [heq]
  exact (((differentiableAt_id.const_mul 2).div_const x).mul h0).sub
    (differentiableAt_comp_add_const.mpr hp)

/-- The J recurrence propagates order differentiability one step up. -/
theorem differentiableAt_realBesselJ_order_add_one (a x : ℝ) (hx : 0 < x)
    (hm : DifferentiableAt ℝ (fun v : ℝ => realBesselJ v x) (a - 1))
    (h0 : DifferentiableAt ℝ (fun v : ℝ => realBesselJ v x) a) :
    DifferentiableAt ℝ (fun v : ℝ => realBesselJ v x) (a + 1) := by
  apply differentiableAt_comp_add_const.mp
  have heq : (fun v : ℝ => realBesselJ (v + 1) x) =
      (fun v : ℝ => (2 * v / x) * realBesselJ v x - realBesselJ (v - 1) x) := by
    funext v
    linear_combination realBesselJ_recurrence v x hx
  rw [heq]
  exact (((differentiableAt_id.const_mul 2).div_const x).mul h0).sub
    (differentiableAt_comp_sub_const.mpr hm)

/-- Two explicit base-order hypotheses imply order differentiability at every integer. -/
theorem differentiableAt_realBesselJ_int_order_of_zero_one (n : ℤ) (x : ℝ) (hx : 0 < x)
    (h0 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 0)
    (h1 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 1) :
    DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) (n : ℝ) := by
  have hn : ∀ k : ℕ,
      DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) (k : ℝ) ∧
      DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) ((k : ℝ) + 1) := by
    intro k
    induction k with
    | zero => simpa using And.intro h0 h1
    | succ k ih =>
      constructor
      · simpa only [Nat.cast_succ] using ih.2
      · have h := differentiableAt_realBesselJ_order_add_one ((k : ℝ) + 1) x hx
          (by simpa using ih.1) ih.2
        simpa only [Nat.cast_succ] using h
  have hm : ∀ k : ℕ,
      DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) (-(k : ℝ)) ∧
      DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) (-(k : ℝ) + 1) := by
    intro k
    induction k with
    | zero => simpa using And.intro h0 h1
    | succ k ih =>
      constructor
      · have h := differentiableAt_realBesselJ_order_sub_one (-(k : ℝ)) x hx ih.1 ih.2
        simpa only [Nat.cast_succ, neg_add, sub_eq_add_neg] using h
      · simpa using ih.1
  cases n with
  | ofNat k => exact (hn k).1
  | negSucc k => simpa only [Int.cast_negSucc, Nat.cast_succ] using (hm (k + 1)).1

/-- Standard integer-Y recurrence with only the two unresolved base-order hypotheses. -/
theorem besselYInt_recurrence_of_order_differentiable_zero_one
    (n : ℤ) (x : ℝ) (hx : 0 < x)
    (h0 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 0)
    (h1 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 1) :
    besselYInt (n - 1) x + besselYInt (n + 1) x =
      (2 * (n : ℝ) / x) * besselYInt n x := by
  have h := fun k => differentiableAt_realBesselJ_int_order_of_zero_one k x hx h0 h1
  exact besselYInt_recurrence_of_differentiable_order n x hx
    (by simpa using h (n - 1)) (h n) (by simpa using h (n + 1))
    (by simpa using h (-n - 1)) (by simpa using h (-n)) (by simpa using h (-n + 1))

/-- The integer limit bridge has the same two explicit base-order obligations. -/
theorem tendsto_besselYNoninteger_int_of_order_differentiable_zero_one
    (n : ℤ) (x : ℝ) (hx : 0 < x)
    (h0 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 0)
    (h1 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 1) :
    Tendsto (fun a : ℝ => besselYNoninteger a x) (𝓝[≠] (n : ℝ))
      (𝓝 (besselYInt n x)) := by
  apply tendsto_besselYNoninteger_int_of_differentiable_order
  · exact differentiableAt_realBesselJ_int_order_of_zero_one n x hx h0 h1
  · simpa using differentiableAt_realBesselJ_int_order_of_zero_one (-n) x hx h0 h1

/-- The order derivative of the known J argument derivative, at two adjacent orders. -/
theorem realBesselJ_order_deriv_argument_deriv (a x : ℝ) (hx : 0 < x)
    (h0 : DifferentiableAt ℝ (fun v : ℝ => realBesselJ v x) a)
    (hp : DifferentiableAt ℝ (fun v : ℝ => realBesselJ v x) (a + 1)) :
    deriv (fun v : ℝ => deriv (realBesselJ v) x) a =
      (1 / x) * realBesselJ a x +
        (a / x) * deriv (fun v : ℝ => realBesselJ v x) a -
        deriv (fun v : ℝ => realBesselJ v x) (a + 1) := by
  have heq : (fun v : ℝ => deriv (realBesselJ v) x) =
      (fun v : ℝ => (v / x) * realBesselJ v x - realBesselJ (v + 1) x) := by
    funext v
    exact (hasDerivAt_realBesselJ v x hx).deriv
  rw [heq]
  have hplus := hp.hasDerivAt.comp a ((hasDerivAt_id a).add_const 1)
  have h := (((hasDerivAt_id a).div_const x).mul h0.hasDerivAt).sub hplus
  change HasDerivAt (fun v : ℝ => (v / x) * realBesselJ v x - realBesselJ (v + 1) x) _ a at h
  simpa only [id_eq, mul_one] using h.deriv

/-- Argument differentiation of Y₀ with an explicit order/argument exchange premise.
`hexchange` includes existence of the argument derivative of the order derivative. -/
theorem hasDerivAt_besselYInt_zero_of_order_derivative_exchange
    (x : ℝ) (hx : 0 < x)
    (h0 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 0)
    (h1 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 1)
    (hexchange : HasDerivAt
      (fun t : ℝ => deriv (fun a : ℝ => realBesselJ a t) 0)
      (deriv (fun a : ℝ => deriv (realBesselJ a) x) 0) x) :
    HasDerivAt (besselYInt 0) (-besselYInt 1 x) x := by
  have hd := hexchange.const_mul (2 / Real.pi)
  have heq : (fun t : ℝ => 2 / Real.pi * deriv (fun a : ℝ => realBesselJ a t) 0) =
      besselYInt 0 := by
    funext t
    exact (besselYInt_zero t).symm
  change HasDerivAt (fun t : ℝ => 2 / Real.pi * deriv (fun a : ℝ => realBesselJ a t) 0) _ x at hd
  rw [heq] at hd
  have hm := differentiableAt_realBesselJ_order_sub_one 0 x hx h0 (by simpa using h1)
  have hr := realBesselJ_order_deriv_recurrence 0 x hx hm h0 (by simpa using h1)
  have harg := realBesselJ_order_deriv_argument_deriv 0 x hx h0 (by simpa using h1)
  norm_num at hr harg
  convert hd using 1
  rw [harg, besselYInt_one]
  field_simp at hr ⊢
  linear_combination hr

/-- The derivative-value form of the same explicitly conditional Y₀ identity. -/
theorem deriv_besselYInt_zero_of_order_derivative_exchange
    (x : ℝ) (hx : 0 < x)
    (h0 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 0)
    (h1 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 1)
    (hexchange : HasDerivAt
      (fun t : ℝ => deriv (fun a : ℝ => realBesselJ a t) 0)
      (deriv (fun a : ℝ => deriv (realBesselJ a) x) 0) x) :
    deriv (besselYInt 0) x = -besselYInt 1 x :=
  (hasDerivAt_besselYInt_zero_of_order_derivative_exchange x hx h0 h1 hexchange).deriv

/-- Argument differentiation of Y₁ with exchanges at orders 1 and -1 explicit. -/
theorem hasDerivAt_besselYInt_one_of_order_derivative_exchange
    (x : ℝ) (hx : 0 < x)
    (h0 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 0)
    (h1 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 1)
    (hexchangeP : HasDerivAt
      (fun t : ℝ => deriv (fun a : ℝ => realBesselJ a t) 1)
      (deriv (fun a : ℝ => deriv (realBesselJ a) x) 1) x)
    (hexchangeN : HasDerivAt
      (fun t : ℝ => deriv (fun a : ℝ => realBesselJ a t) (-1))
      (deriv (fun a : ℝ => deriv (realBesselJ a) x) (-1)) x) :
    HasDerivAt (besselYInt 1) (besselYInt 0 x - besselYInt 1 x / x) x := by
  have hd := (hexchangeP.sub hexchangeN).div_const Real.pi
  have heq : (fun t : ℝ => (deriv (fun a : ℝ => realBesselJ a t) 1 -
      deriv (fun a : ℝ => realBesselJ a t) (-1)) / Real.pi) = besselYInt 1 := by
    funext t
    exact (besselYInt_one t).symm
  change HasDerivAt (fun t : ℝ => (deriv (fun a : ℝ => realBesselJ a t) 1 -
      deriv (fun a : ℝ => realBesselJ a t) (-1)) / Real.pi) _ x at hd
  rw [heq] at hd
  have h2 := differentiableAt_realBesselJ_order_add_one 1 x hx (by simpa using h0) h1
  have hm := differentiableAt_realBesselJ_order_sub_one 0 x hx h0 (by simpa using h1)
  have hr := realBesselJ_order_deriv_recurrence 1 x hx (by simpa using h0) h1 h2
  have hargP := realBesselJ_order_deriv_argument_deriv 1 x hx h1 h2
  have hargN := realBesselJ_order_deriv_argument_deriv (-1) x hx
    (by simpa using hm) (by simpa using h0)
  have hneg := realBesselJ_neg_int 1 x
  norm_num at hr hargP hargN hneg
  rw [hneg] at hargN
  convert hd using 1
  rw [hargP, hargN, besselYInt_zero, besselYInt_one]
  field_simp at hr ⊢
  linear_combination hr

/-- The derivative-value form of the same explicitly conditional Y₁ identity. -/
theorem deriv_besselYInt_one_of_order_derivative_exchange
    (x : ℝ) (hx : 0 < x)
    (h0 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 0)
    (h1 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 1)
    (hexchangeP : HasDerivAt
      (fun t : ℝ => deriv (fun a : ℝ => realBesselJ a t) 1)
      (deriv (fun a : ℝ => deriv (realBesselJ a) x) 1) x)
    (hexchangeN : HasDerivAt
      (fun t : ℝ => deriv (fun a : ℝ => realBesselJ a t) (-1))
      (deriv (fun a : ℝ => deriv (realBesselJ a) x) (-1)) x) :
    deriv (besselYInt 1) x = besselYInt 0 x - besselYInt 1 x / x :=
  (hasDerivAt_besselYInt_one_of_order_derivative_exchange x hx h0 h1
    hexchangeP hexchangeN).deriv

/-- The order-zero J/Y Wronskian in terms of adjacent integer orders. -/
theorem besselYInt_wronskian_zero_of_order_derivative_exchange
    (x : ℝ) (hx : 0 < x)
    (h0 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 0)
    (h1 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 1)
    (hexchange : HasDerivAt
      (fun t : ℝ => deriv (fun a : ℝ => realBesselJ a t) 0)
      (deriv (fun a : ℝ => deriv (realBesselJ a) x) 0) x) :
    realBesselJ 0 x * deriv (besselYInt 0) x -
        deriv (realBesselJ 0) x * besselYInt 0 x =
      realBesselJ 1 x * besselYInt 0 x - realBesselJ 0 x * besselYInt 1 x := by
  rw [deriv_besselYInt_zero_of_order_derivative_exchange x hx h0 h1 hexchange,
    (hasDerivAt_realBesselJ 0 x hx).deriv]
  norm_num
  ring

/-- The scaled adjacent-order Wronskian has derivative zero under explicit exchanges.
Its value `2 / pi` is a remaining normalization obligation. -/
theorem hasDerivAt_besselYInt_scaled_wronskian_of_order_derivative_exchange
    (x : ℝ) (hx : 0 < x)
    (h0 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 0)
    (h1 : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 1)
    (hexchange0 : HasDerivAt
      (fun t : ℝ => deriv (fun a : ℝ => realBesselJ a t) 0)
      (deriv (fun a : ℝ => deriv (realBesselJ a) x) 0) x)
    (hexchangeP : HasDerivAt
      (fun t : ℝ => deriv (fun a : ℝ => realBesselJ a t) 1)
      (deriv (fun a : ℝ => deriv (realBesselJ a) x) 1) x)
    (hexchangeN : HasDerivAt
      (fun t : ℝ => deriv (fun a : ℝ => realBesselJ a t) (-1))
      (deriv (fun a : ℝ => deriv (realBesselJ a) x) (-1)) x) :
    HasDerivAt (fun t : ℝ => t *
      (realBesselJ 1 t * besselYInt 0 t - realBesselJ 0 t * besselYInt 1 t)) 0 x := by
  have hJ0 : HasDerivAt (realBesselJ 0) (-realBesselJ 1 x) x := by
    simpa using hasDerivAt_realBesselJ 0 x hx
  have hJ1 : HasDerivAt (realBesselJ 1)
      (realBesselJ 0 x - realBesselJ 1 x / x) x := by
    convert hasDerivAt_realBesselJ 1 x hx using 1
    have hr := realBesselJ_recurrence 1 x hx
    norm_num at hr ⊢
    field_simp at hr ⊢
    linear_combination hr
  have hY0 := hasDerivAt_besselYInt_zero_of_order_derivative_exchange x hx h0 h1 hexchange0
  have hY1 := hasDerivAt_besselYInt_one_of_order_derivative_exchange x hx h0 h1
    hexchangeP hexchangeN
  have hd := (hasDerivAt_id x).mul ((hJ1.mul hY0).sub (hJ0.mul hY1))
  change HasDerivAt (fun t : ℝ => t *
    (realBesselJ 1 t * besselYInt 0 t - realBesselJ 0 t * besselYInt 1 t)) _ x at hd
  convert hd using 1
  dsimp
  field_simp
  ring

#print axioms differentiable_hgCoeff_order
#print axioms differentiable_besselJ_series_term_order
#print axioms hasSum_besselJ_order_series
#print axioms realBesselJ_order_deriv_recurrence
#print axioms besselYInt_recurrence_of_differentiable_order
#print axioms differentiableAt_realBesselJ_order_sub_one
#print axioms differentiableAt_realBesselJ_order_add_one
#print axioms differentiableAt_realBesselJ_int_order_of_zero_one
#print axioms besselYInt_recurrence_of_order_differentiable_zero_one
#print axioms tendsto_besselYNoninteger_int_of_order_differentiable_zero_one
#print axioms realBesselJ_order_deriv_argument_deriv
#print axioms hasDerivAt_besselYInt_zero_of_order_derivative_exchange
#print axioms deriv_besselYInt_zero_of_order_derivative_exchange
#print axioms hasDerivAt_besselYInt_one_of_order_derivative_exchange
#print axioms deriv_besselYInt_one_of_order_derivative_exchange
#print axioms besselYInt_wronskian_zero_of_order_derivative_exchange
#print axioms hasDerivAt_besselYInt_scaled_wronskian_of_order_derivative_exchange

end SpecialFunctionProofAgent
