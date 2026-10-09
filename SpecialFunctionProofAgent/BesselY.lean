import BesselProofAgent.RealCalculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Standard positive-axis Bessel Y definitions

`besselYNoninteger` uses the connection formula DLMF 10.2.3 with the existing
`Complex.besselJ`. Its documented domain is `0 < x` and `sin (a * pi) ≠ 0`.
`besselYInt` uses the order-derivative formula DLMF 10.2.4. The analytic bridge
from the noninteger formula to an integer order is stated with explicit
order-differentiability hypotheses; these hypotheses are separate obligations.

References: https://dlmf.nist.gov/10.2.E3 and https://dlmf.nist.gov/10.2.E4.

The unconditional analytic results below concern noninteger order and positive
argument. Remaining integer-order obligations are order differentiability of
the regularized hypergeometric series at both signed integer orders, exchange
of order/argument derivatives, and the normalized Wronskian. The cross-product
application additionally needs its positive energy integral and nonzero
denominators.
-/

noncomputable section

namespace SpecialFunctionProofAgent

open Complex Filter
open scoped Topology

/-- Real restriction of mathlib's first-kind Bessel function. -/
def realBesselJ (a x : ℝ) : ℝ := (Complex.besselJ (a : ℂ) (x : ℂ)).re

/-- DLMF 10.2.3, on positive arguments and noninteger real orders. -/
def besselYNoninteger (a x : ℝ) : ℝ :=
  (realBesselJ a x * Real.cos (a * Real.pi) - realBesselJ (-a) x) /
    Real.sin (a * Real.pi)

/-- DLMF 10.2.4. Its limit interpretation requires order differentiability. -/
def besselYInt (n : ℤ) (x : ℝ) : ℝ :=
  (deriv (fun a : ℝ => realBesselJ a x) n +
    (-1 : ℝ) ^ n * deriv (fun a : ℝ => realBesselJ a x) (-n)) / Real.pi

theorem sin_order_pi_ne_zero_iff (a : ℝ) :
    Real.sin (a * Real.pi) ≠ 0 ↔ ∀ n : ℤ, a ≠ (n : ℝ) := by
  rw [Real.sin_ne_zero_iff]
  constructor
  · intro h n heq
    apply h n
    rw [heq]
  · intro h n heq
    exact h n (mul_right_cancel₀ Real.pi_ne_zero heq).symm

private theorem hg_conj_real (a z : ℝ) :
    (starRingEnd ℂ) (regularizedHGFun 0 {(a : ℂ)} (z : ℂ)) =
      regularizedHGFun 0 {(a : ℂ)} (z : ℂ) := by
  rw [← (BesselProofAgent.hg_hasSum (a : ℂ) (z : ℂ)).tsum_eq, Complex.conj_tsum]
  apply tsum_congr
  intro k
  simp [BesselProofAgent.hg_coeff, ← Complex.Gamma_conj]

/-- The real restriction retains the complete complex value on the positive axis. -/
theorem ofReal_realBesselJ (a x : ℝ) (hx : 0 < x) :
    (realBesselJ a x : ℂ) = Complex.besselJ (a : ℂ) (x : ℂ) := by
  apply Complex.conj_eq_iff_re.mp
  unfold Complex.besselJ
  have hp : (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hp, ← Complex.ofReal_cpow (by positivity)]
  simp only [map_mul, Complex.conj_ofReal]
  congr 1
  convert hg_conj_real (a + 1) (-(x / 2) ^ 2) using 1 <;> push_cast <;> rfl

/-- The order reflection is inherited from the existing complex J normalization. -/
theorem realBesselJ_neg_int (n : ℤ) (x : ℝ) :
    realBesselJ (-n) x = (-1 : ℝ) ^ n * realBesselJ n x := by
  have h := congrArg Complex.re (Complex.besselJ_neg_int n (x : ℂ))
  have hp : (-1 : ℂ) ^ n = (((-1 : ℝ) ^ n : ℝ) : ℂ) := by push_cast; rfl
  rw [hp, Complex.re_ofReal_mul] at h
  simpa [realBesselJ] using h

/-- The standard noninteger connection formula with the original complex J. -/
theorem ofReal_besselYNoninteger (a x : ℝ) (hx : 0 < x) :
    (besselYNoninteger a x : ℂ) =
      (Complex.besselJ (a : ℂ) (x : ℂ) * (Real.cos (a * Real.pi) : ℂ) -
        Complex.besselJ (-a : ℂ) (x : ℂ)) / (Real.sin (a * Real.pi) : ℂ) := by
  unfold besselYNoninteger
  push_cast
  rw [ofReal_realBesselJ a x hx, ofReal_realBesselJ (-a) x hx]
  simp only [Complex.ofReal_neg]

theorem besselYNoninteger_connection (a x : ℝ) (ha : Real.sin (a * Real.pi) ≠ 0) :
    Real.sin (a * Real.pi) * besselYNoninteger a x =
      realBesselJ a x * Real.cos (a * Real.pi) - realBesselJ (-a) x := by
  unfold besselYNoninteger
  field_simp

theorem realBesselJ_recurrence (a x : ℝ) (hx : 0 < x) :
    realBesselJ (a - 1) x + realBesselJ (a + 1) x =
      (2 * a / x) * realBesselJ a x := by
  apply Complex.ofReal_injective
  push_cast
  rw [ofReal_realBesselJ (a - 1) x hx, ofReal_realBesselJ (a + 1) x hx,
    ofReal_realBesselJ a x hx]
  simpa using BesselProofAgent.bessel_recurrence (a : ℂ) (x : ℂ)
    (by exact_mod_cast (ne_of_gt hx))

theorem hasDerivAt_realBesselJ (a x : ℝ) (hx : 0 < x) :
    HasDerivAt (realBesselJ a)
      ((a / x) * realBesselJ a x - realBesselJ (a + 1) x) x := by
  have h := (BesselProofAgent.bessel_hasDerivAt (a : ℂ) (x : ℂ)
    (Complex.ofReal_mem_slitPlane.mpr hx)).real_of_complex
  have hc : (a : ℂ) / (x : ℂ) = ((a / x : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.sub_re, Complex.re_ofReal_mul] at h
  change HasDerivAt (fun t : ℝ => (Complex.besselJ (a : ℂ) (t : ℂ)).re) _ x
  simpa [realBesselJ] using h

/-- Noninteger order reflection, with the standard J/Y normalization. -/
theorem besselYNoninteger_neg (a x : ℝ) (ha : Real.sin (a * Real.pi) ≠ 0) :
    besselYNoninteger (-a) x = Real.cos (a * Real.pi) * besselYNoninteger a x +
      Real.sin (a * Real.pi) * realBesselJ a x := by
  simp only [besselYNoninteger, neg_mul, Real.sin_neg, Real.cos_neg, neg_neg]
  field_simp
  linear_combination -(realBesselJ a x) * Real.cos_sq_add_sin_sq (a * Real.pi)

/-- Three-term Y recurrence on the positive axis at noninteger orders. -/
theorem besselYNoninteger_recurrence (a x : ℝ) (hx : 0 < x)
    (ha : Real.sin (a * Real.pi) ≠ 0) :
    besselYNoninteger (a - 1) x + besselYNoninteger (a + 1) x =
      (2 * a / x) * besselYNoninteger a x := by
  have hp := realBesselJ_recurrence a x hx
  have hn := realBesselJ_recurrence (-a) x hx
  have hm : -(a - 1) = -a + 1 := by ring
  have hp' : -(a + 1) = -a - 1 := by ring
  simp only [besselYNoninteger, sub_mul, add_mul, one_mul, Real.cos_sub_pi,
    Real.cos_add_pi, Real.sin_sub_pi, Real.sin_add_pi, hm, hp']
  field_simp
  field_simp at hp hn
  linear_combination Real.cos (a * Real.pi) * hp + hn

/-- Argument differentiation of Y, derived from the two connected J functions. -/
theorem hasDerivAt_besselYNoninteger (a x : ℝ) (hx : 0 < x)
    (ha : Real.sin (a * Real.pi) ≠ 0) :
    HasDerivAt (besselYNoninteger a)
      ((a / x) * besselYNoninteger a x - besselYNoninteger (a + 1) x) x := by
  have hp := hasDerivAt_realBesselJ a x hx
  have hn := hasDerivAt_realBesselJ (-a) x hx
  have hd := ((hp.mul_const (Real.cos (a * Real.pi))).sub hn).div_const
    (Real.sin (a * Real.pi))
  convert! hd using 1
  simp only [besselYNoninteger]
  have hr := realBesselJ_recurrence (-a) x hx
  have hs : -(a + 1) = -a - 1 := by ring
  simp only [add_mul, one_mul, Real.cos_add_pi, Real.sin_add_pi, hs]
  field_simp
  field_simp at hr
  linear_combination -hr

theorem deriv_besselYNoninteger (a x : ℝ) (hx : 0 < x)
    (ha : Real.sin (a * Real.pi) ≠ 0) :
    deriv (besselYNoninteger a) x =
      (a / x) * besselYNoninteger a x - besselYNoninteger (a + 1) x :=
  (hasDerivAt_besselYNoninteger a x hx ha).deriv

/-- Bessel's differential equation for the standard noninteger Y on `x > 0`. -/
theorem besselYNoninteger_ode (a x : ℝ) (hx : 0 < x)
    (ha : Real.sin (a * Real.pi) ≠ 0) :
    x ^ 2 * deriv (deriv (besselYNoninteger a)) x +
      x * deriv (besselYNoninteger a) x +
      (x ^ 2 - a ^ 2) * besselYNoninteger a x = 0 := by
  have hx0 := ne_of_gt hx
  have ha1 : Real.sin ((a + 1) * Real.pi) ≠ 0 := by
    simpa only [add_mul, one_mul, Real.sin_add_pi, neg_ne_zero] using ha
  have h0 := hasDerivAt_besselYNoninteger a x hx ha
  have h1 := hasDerivAt_besselYNoninteger (a + 1) x hx ha1
  have hc := (hasDerivAt_const x a).div (hasDerivAt_id x) hx0
  have hd := ((hc.mul h0).sub h1).congr_of_eventuallyEq
    ((eventually_gt_nhds hx).mono (fun y hy => deriv_besselYNoninteger a y hy ha))
  have hr := besselYNoninteger_recurrence (a + 1) x hx ha1
  rw [hd.deriv, h0.deriv]
  have hs : a + 1 - 1 = a := by ring
  rw [hs] at hr
  simp only [Pi.div_apply, id_eq, zero_mul, zero_sub, mul_one]
  field_simp
  field_simp at hr
  linear_combination x * hr

theorem besselYInt_zero (x : ℝ) :
    besselYInt 0 x = 2 / Real.pi * deriv (fun a : ℝ => realBesselJ a x) 0 := by
  simp [besselYInt]
  ring

theorem besselYInt_one (x : ℝ) :
    besselYInt 1 x =
      (deriv (fun a : ℝ => realBesselJ a x) 1 -
        deriv (fun a : ℝ => realBesselJ a x) (-1)) / Real.pi := by
  simp [besselYInt, sub_eq_add_neg]

theorem besselYInt_two (x : ℝ) :
    besselYInt 2 x =
      (deriv (fun a : ℝ => realBesselJ a x) 2 +
        deriv (fun a : ℝ => realBesselJ a x) (-2)) / Real.pi := by
  norm_num [besselYInt]

theorem besselYInt_neg (n : ℤ) (x : ℝ) :
    besselYInt (-n) x = (-1 : ℝ) ^ n * besselYInt n x := by
  have hs : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← mul_zpow]
    norm_num
  have hi : ((-1 : ℝ) ^ n)⁻¹ = (-1 : ℝ) ^ n := inv_eq_of_mul_eq_one_left hs
  simp only [besselYInt, Int.cast_neg, neg_neg, zpow_neg, hi]
  field_simp
  linear_combination -(deriv (fun a : ℝ => realBesselJ a x) (-n)) * hs

/-- The half-order value follows directly from the standard connection formula. -/
theorem besselYNoninteger_half (x : ℝ) :
    besselYNoninteger (1 / 2) x = -realBesselJ (-(1 / 2)) x := by
  norm_num [besselYNoninteger, div_mul_eq_mul_div, Real.cos_pi_div_two,
    Real.sin_pi_div_two]

theorem sin_half_order_pi_ne_zero : Real.sin ((1 / 2 : ℝ) * Real.pi) ≠ 0 := by
  norm_num [div_mul_eq_mul_div, Real.sin_pi_div_two]

/-- A fixed half-integer recurrence with only the positive-argument condition. -/
theorem Yhalf_recurrence (x : ℝ) (hx : 0 < x) :
    besselYNoninteger (-(1 / 2)) x + besselYNoninteger (3 / 2) x =
      besselYNoninteger (1 / 2) x / x := by
  have h := besselYNoninteger_recurrence (1 / 2) x hx sin_half_order_pi_ne_zero
  convert h using 1 <;> norm_num
  ring

/-- The symmetric argument derivative at order one half. -/
theorem hasDerivAt_Yhalf (x : ℝ) (hx : 0 < x) :
    HasDerivAt (besselYNoninteger (1 / 2))
      ((besselYNoninteger (-(1 / 2)) x - besselYNoninteger (3 / 2) x) / 2) x := by
  convert! hasDerivAt_besselYNoninteger (1 / 2) x hx sin_half_order_pi_ne_zero using 1
  norm_num
  linear_combination (1 / 2 : ℝ) * Yhalf_recurrence x hx

theorem Yhalf_derivative (x : ℝ) (hx : 0 < x) :
    deriv (besselYNoninteger (1 / 2)) x =
      (besselYNoninteger (-(1 / 2)) x - besselYNoninteger (3 / 2) x) / 2 :=
  (hasDerivAt_Yhalf x hx).deriv

/-- Integer-order limiting value. The two order-differentiability assumptions
are the remaining analytic bridge, supplied explicitly by the caller. -/
theorem tendsto_besselYNoninteger_int_of_differentiable_order (n : ℤ) (x : ℝ)
    (hp : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) (n : ℝ))
    (hn : DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) (-n : ℝ)) :
    Tendsto (fun a : ℝ => besselYNoninteger a x) (𝓝[≠] (n : ℝ))
      (𝓝 (besselYInt n x)) := by
  let f : ℝ → ℝ := fun a => realBesselJ a x * Real.cos (a * Real.pi) - realBesselJ (-a) x
  let g : ℝ → ℝ := fun a => Real.sin (a * Real.pi)
  let p := deriv (fun a : ℝ => realBesselJ a x) (n : ℝ)
  let q := deriv (fun a : ℝ => realBesselJ a x) (-n : ℝ)
  let c := (-1 : ℝ) ^ n
  have hc : c * c = 1 := by dsimp [c]; rw [← mul_zpow]; norm_num
  have hc0 : c ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hf0 : f n = 0 := by
    simp only [f, Real.cos_int_mul_pi, realBesselJ_neg_int]
    ring
  have hg0 : g n = 0 := Real.sin_int_mul_pi n
  have hcos : HasDerivAt (fun a : ℝ => Real.cos (a * Real.pi)) 0 (n : ℝ) := by
    simpa using ((hasDerivAt_id (n : ℝ)).mul_const Real.pi).cos
  have hneg : HasDerivAt (fun a : ℝ => realBesselJ (-a) x) (-q) (n : ℝ) := by
    simpa [q, Function.comp_def] using! hn.hasDerivAt.comp (n : ℝ) (hasDerivAt_neg (n : ℝ))
  have hf : HasDerivAt f (p * c + q) (n : ℝ) := by
    simpa [f, p, c, Real.cos_int_mul_pi, Pi.mul_apply, Pi.sub_apply] using!
      (hp.hasDerivAt.mul hcos).sub hneg
  have hg : HasDerivAt g (c * Real.pi) (n : ℝ) := by
    simpa [g, c, Real.cos_int_mul_pi] using
      ((hasDerivAt_id (n : ℝ)).mul_const Real.pi).sin
  have hlim := hf.tendsto_slope.div hg.tendsto_slope (mul_ne_zero hc0 Real.pi_ne_zero)
  have hvalue : (p * c + q) / (c * Real.pi) = besselYInt n x := by
    change (p * c + q) / (c * Real.pi) = (p + c * q) / Real.pi
    field_simp
    linear_combination -q * hc
  rw [hvalue] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ha' : a - (n : ℝ) ≠ 0 := sub_ne_zero.mpr ha
  simp only [Pi.div_apply, slope_def_field, hf0, hg0, sub_zero]
  dsimp [f, g, besselYNoninteger]
  field_simp

#print axioms realBesselJ
#print axioms besselYNoninteger
#print axioms besselYInt
#print axioms sin_order_pi_ne_zero_iff
#print axioms ofReal_realBesselJ
#print axioms realBesselJ_neg_int
#print axioms ofReal_besselYNoninteger
#print axioms besselYNoninteger_connection
#print axioms realBesselJ_recurrence
#print axioms hasDerivAt_realBesselJ
#print axioms besselYNoninteger_neg
#print axioms besselYNoninteger_recurrence
#print axioms hasDerivAt_besselYNoninteger
#print axioms deriv_besselYNoninteger
#print axioms besselYNoninteger_ode
#print axioms besselYInt_zero
#print axioms besselYInt_one
#print axioms besselYInt_two
#print axioms besselYInt_neg
#print axioms besselYNoninteger_half
#print axioms sin_half_order_pi_ne_zero
#print axioms Yhalf_recurrence
#print axioms hasDerivAt_Yhalf
#print axioms Yhalf_derivative
#print axioms tendsto_besselYNoninteger_int_of_differentiable_order

end SpecialFunctionProofAgent
