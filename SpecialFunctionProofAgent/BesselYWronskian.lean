import SpecialFunctionProofAgent.BesselYAnalytic
import BesselProofAgent.OriginSingularBessel
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Positive-axis Bessel Y Wronskian normalization

All J and Y definitions are imported unchanged. The opposite-order J product
has a constant scaled value on the positive real axis. Its hypergeometric
factorization extends continuously to zero, where Gamma reflection determines
the constant. The noninteger J/Y connection formula then gives `2 / (pi * x)`.
Taking the existing integer-order limits proves the degree-zero/one identity;
the integer recurrences propagate it to every integer degree.

The determinant `J₁ Y₀ - J₀ Y₁` has positive sign. The explicit diagonal cross
product `J₀ Y₁ - Y₀ J₁`, corresponding to `X₀₁(x,x)`, has negative sign.
-/

set_option autoImplicit false

noncomputable section
namespace SpecialFunctionProofAgent
open Complex Filter Set
open scoped Topology

private theorem pair_hasDerivAt_zero (a x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => t * (realBesselJ (a + 1) t * realBesselJ (-a) t +
      realBesselJ a t * realBesselJ (-a - 1) t)) 0 x := by
  have hA : HasDerivAt (realBesselJ (a + 1))
      (realBesselJ a x - ((a + 1) / x) * realBesselJ (a + 1) x) x := by
    convert hasDerivAt_realBesselJ (a + 1) x hx using 1
    have hr := realBesselJ_recurrence (a + 1) x hx
    rw [show a + 1 - 1 = a by ring] at hr
    linear_combination hr
  have hB : HasDerivAt (realBesselJ (-a))
      (realBesselJ (-a - 1) x + (a / x) * realBesselJ (-a) x) x := by
    convert hasDerivAt_realBesselJ (-a) x hx using 1
    have hr := realBesselJ_recurrence (-a) x hx
    linear_combination hr
  have hJ := hasDerivAt_realBesselJ a x hx
  have hC := hasDerivAt_realBesselJ (-a - 1) x hx
  rw [show -a - 1 + 1 = -a by ring] at hC
  have hd := (hasDerivAt_id x).mul ((hA.mul hB).add (hJ.mul hC))
  change HasDerivAt (fun t : ℝ => t * (realBesselJ (a + 1) t * realBesselJ (-a) t +
    realBesselJ a t * realBesselJ (-a - 1) t)) _ x at hd
  convert hd using 1
  dsimp
  field_simp
  ring

private theorem pair_constant (a x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x * (realBesselJ (a + 1) x * realBesselJ (-a) x +
      realBesselJ a x * realBesselJ (-a - 1) x) =
    y * (realBesselJ (a + 1) y * realBesselJ (-a) y +
      realBesselJ a y * realBesselJ (-a - 1) y) := by
  apply isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected
    (fun t ht => (pair_hasDerivAt_zero a t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (pair_hasDerivAt_zero a t ht).deriv) hx hy

private theorem bessel_pair_factor (a z : ℂ) (hz : z ≠ 0) :
    z * (besselJ (a + 1) z * besselJ (-a) z + besselJ a z * besselJ (-a - 1) z) =
      z ^ 2 / 2 * (regularizedHGFun 0 {a + 2} (- (z / 2) ^ 2) *
        regularizedHGFun 0 {-a + 1} (- (z / 2) ^ 2)) +
      2 * (regularizedHGFun 0 {a + 1} (- (z / 2) ^ 2) *
        regularizedHGFun 0 {-a} (- (z / 2) ^ 2)) := by
  have ht : z / 2 ≠ 0 := div_ne_zero hz (by norm_num)
  have hp : (z / 2) ^ (a + 1) * (z / 2) ^ (-a) = z / 2 := by
    rw [← cpow_add _ _ ht, show a + 1 + -a = 1 by ring, cpow_one]
  have hm : (z / 2) ^ a * (z / 2) ^ (-a - 1) = (z / 2)⁻¹ := by
    rw [← cpow_add _ _ ht, show a + (-a - 1) = -1 by ring, cpow_neg_one]
  simp only [besselJ, show a + 1 + 1 = a + 2 by ring,
    show -a - 1 + 1 = -a by ring]
  calc
    _ = z * ((z / 2) ^ (a + 1) * (z / 2) ^ (-a) *
        (regularizedHGFun 0 {a + 2} (- (z / 2) ^ 2) * regularizedHGFun 0 {-a + 1} (- (z / 2) ^ 2)) +
      (z / 2) ^ a * (z / 2) ^ (-a - 1) *
        (regularizedHGFun 0 {a + 1} (- (z / 2) ^ 2) * regularizedHGFun 0 {-a} (- (z / 2) ^ 2))) := by ring
    _ = _ := by rw [hp, hm]; field_simp

private theorem pair_limit (a : ℝ) :
    Tendsto (fun x : ℝ => ((x * (realBesselJ (a + 1) x * realBesselJ (-a) x +
      realBesselJ a x * realBesselJ (-a - 1) x) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 (2 * ((Gamma ((a : ℂ) + 1))⁻¹ * (Gamma (-(a : ℂ)))⁻¹))) := by
  have hc : Continuous (fun t : ℝ => (t : ℂ) ^ 2 / 2 *
      (regularizedHGFun 0 {(a : ℂ) + 2} (- ((t : ℂ) / 2) ^ 2) *
       regularizedHGFun 0 {-(a : ℂ) + 1} (- ((t : ℂ) / 2) ^ 2)) +
      2 * (regularizedHGFun 0 {(a : ℂ) + 1} (- ((t : ℂ) / 2) ^ 2) *
       regularizedHGFun 0 {-(a : ℂ)} (- ((t : ℂ) / 2) ^ 2))) := by
    exact ((Complex.continuous_ofReal.pow 2).div_const 2).mul
      ((BesselProofAgent.continuous_bessel_hg_factor _).mul
        (BesselProofAgent.continuous_bessel_hg_factor _)) |>.add
      (continuous_const.mul ((BesselProofAgent.continuous_bessel_hg_factor _).mul
        (BesselProofAgent.continuous_bessel_hg_factor _)))
  have ht := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  norm_num [regularizedHGFun_zero, BesselProofAgent.hg_coeff] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  push_cast
  rw [ofReal_realBesselJ (a + 1) x hx, ofReal_realBesselJ (-a) x hx,
    ofReal_realBesselJ a x hx, ofReal_realBesselJ (-a - 1) x hx]
  push_cast
  exact (bessel_pair_factor (a : ℂ) (x : ℂ) (by exact_mod_cast ne_of_gt hx)).symm

private theorem gamma_pair_inverse (a : ℂ) :
    (Gamma (a + 1))⁻¹ * (Gamma (-a))⁻¹ = -sin ((Real.pi : ℂ) * a) / (Real.pi : ℂ) := by
  have h := Gamma_mul_Gamma_one_sub (a + 1)
  rw [show 1 - (a + 1) = -a by ring] at h
  rw [← mul_inv, h]
  simp only [mul_add, mul_one, sin_add_pi, inv_div]

/-- The normalized opposite-order J product, derived from its regular origin factor. -/
theorem realBesselJ_opposite_order_product (a x : ℝ) (hx : 0 < x) :
    x * (realBesselJ (a + 1) x * realBesselJ (-a) x +
      realBesselJ a x * realBesselJ (-a - 1) x) = -2 * Real.sin (a * Real.pi) / Real.pi := by
  have ht := pair_limit a
  have he : (fun t : ℝ => ((t * (realBesselJ (a + 1) t * realBesselJ (-a) t +
      realBesselJ a t * realBesselJ (-a - 1) t) : ℝ) : ℂ)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun _ => ((x * (realBesselJ (a + 1) x * realBesselJ (-a) x +
        realBesselJ a x * realBesselJ (-a - 1) x) : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact congrArg (fun r : ℝ => (r : ℂ)) (pair_constant a t x ht hx)
  have h := tendsto_nhds_unique (ht.congr' he) tendsto_const_nhds
  rw [gamma_pair_inverse] at h
  apply Complex.ofReal_injective
  push_cast at h ⊢
  rw [← h, mul_comm (Real.pi : ℂ) (a : ℂ)]
  ring

/-- Standard noninteger Y has the positive normalized adjacent-order Wronskian. -/
theorem besselYNoninteger_wronskian (a x : ℝ) (hx : 0 < x)
    (ha : Real.sin (a * Real.pi) ≠ 0) :
    realBesselJ (a + 1) x * besselYNoninteger a x -
      realBesselJ a x * besselYNoninteger (a + 1) x = 2 / (Real.pi * x) := by
  have h := realBesselJ_opposite_order_product a x hx
  simp only [besselYNoninteger, add_mul, one_mul, Real.cos_add_pi, Real.sin_add_pi,
    show -(a + 1) = -a - 1 by ring]
  field_simp at h ⊢
  linear_combination -h

/-- Integer orders zero and one have the standard positive-axis Wronskian normalization. -/
theorem besselYInt_wronskian_zero (x : ℝ) (hx : 0 < x) :
    realBesselJ 1 x * besselYInt 0 x - realBesselJ 0 x * besselYInt 1 x =
      2 / (Real.pi * x) := by
  have hj0 : Tendsto (fun a : ℝ => realBesselJ a x) (𝓝[>] 0)
      (𝓝 (realBesselJ 0 x)) :=
    (differentiableAt_realBesselJ_order_zero_one x hx).1.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have ha : Tendsto (fun a : ℝ => a + 1) (𝓝[>] 0) (𝓝[≠] 1) := by
    have h := ((hasDerivAt_id (0 : ℝ)).add_const 1).tendsto_nhdsNE (by norm_num)
    simpa using h.mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  have hj1 : Tendsto (fun a : ℝ => realBesselJ (a + 1) x) (𝓝[>] 0)
      (𝓝 (realBesselJ 1 x)) :=
    (differentiableAt_realBesselJ_order_zero_one x hx).2.continuousAt.tendsto.comp
      (ha.mono_right nhdsWithin_le_nhds)
  have hy0 : Tendsto (fun a : ℝ => besselYNoninteger a x) (𝓝[>] 0)
      (𝓝 (besselYInt 0 x)) := by
    have h := tendsto_besselYNoninteger_int 0 x hx
    simp only [Int.cast_zero] at h
    exact h.mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  have hy1 : Tendsto (fun a : ℝ => besselYNoninteger (a + 1) x) (𝓝[>] 0)
      (𝓝 (besselYInt 1 x)) := by
    have h := tendsto_besselYNoninteger_int 1 x hx
    simp only [Int.cast_one] at h
    exact h.comp ha
  have hlim := (hj1.mul hy0).sub (hj0.mul hy1)
  have he : (fun a : ℝ => realBesselJ (a + 1) x * besselYNoninteger a x -
      realBesselJ a x * besselYNoninteger (a + 1) x) =ᶠ[𝓝[>] 0]
      (fun _ => 2 / (Real.pi * x)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with a ha0 ha1
    apply besselYNoninteger_wronskian a x hx
    apply ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (mul_pos ha0 Real.pi_pos) ?_)
    nlinarith [Real.pi_pos]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' he.symm)

/-- The explicit product corresponding to X₀₁(x,x) has the opposite sign. -/
theorem besselYInt_cross_zero_one (x : ℝ) (hx : 0 < x) :
    realBesselJ 0 x * besselYInt 1 x - besselYInt 0 x * realBesselJ 1 x =
      -2 / (Real.pi * x) := by
  linear_combination -besselYInt_wronskian_zero x hx

private theorem integer_wronskian_step (n : ℤ) (x : ℝ) (hx : 0 < x) :
    realBesselJ ((n : ℝ) + 1) x * besselYInt n x -
        realBesselJ n x * besselYInt (n + 1) x =
      realBesselJ (((n - 1 : ℤ) : ℝ) + 1) x * besselYInt (n - 1) x -
        realBesselJ (n - 1 : ℤ) x * besselYInt (n - 1 + 1) x := by
  have hJ := realBesselJ_recurrence (n : ℝ) x hx
  have hY := besselYInt_recurrence n x hx
  simp only [Int.cast_sub, Int.cast_one, sub_add_cancel]
  linear_combination besselYInt n x * hJ - realBesselJ n x * hY

/-- The normalized adjacent-order Wronskian holds at every integer degree. -/
theorem besselYInt_wronskian (n : ℤ) (x : ℝ) (hx : 0 < x) :
    realBesselJ ((n : ℝ) + 1) x * besselYInt n x -
      realBesselJ n x * besselYInt (n + 1) x = 2 / (Real.pi * x) := by
  induction n using Int.induction_on with
  | zero => simpa using besselYInt_wronskian_zero x hx
  | succ k ih =>
    rw [integer_wronskian_step _ x hx]
    simpa using ih
  | pred k ih =>
    rw [← integer_wronskian_step _ x hx]
    exact ih

/-- The diagonal order-zero/one cross product is strictly negative on the positive axis. -/
theorem besselYInt_cross_zero_one_neg (x : ℝ) (hx : 0 < x) :
    realBesselJ 0 x * besselYInt 1 x - besselYInt 0 x * realBesselJ 1 x < 0 := by
  rw [besselYInt_cross_zero_one x hx]
  exact div_neg_of_neg_of_pos (by norm_num) (mul_pos Real.pi_pos hx)

end SpecialFunctionProofAgent
