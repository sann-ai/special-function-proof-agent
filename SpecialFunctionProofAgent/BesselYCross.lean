import SpecialFunctionProofAgent.BesselYWronskian
import SpecialFunctionProofAgent.BesselYArgument
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Standard Bessel cross products at a positive scaled root

The order convention is `X_nm(s,t) = J_n(s) Y_m(t) - Y_n(s) J_m(t)`.
The recurrence and normalized Wronskian prove the identities used by the fixed
root problem. The argument derivatives and a positive energy integral prove that
both displayed denominators are nonzero when `0 < lambda < 1` and `0 < z`.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SpecialFunctionProofAgent

/-- The standard real Bessel cross product, with the CLI's fixed order convention. -/
def besselCross (n m : ℤ) (s t : ℝ) : ℝ :=
  realBesselJ n s * besselYInt m t - besselYInt n s * realBesselJ m t

/-- The diagonal order-zero/one cross product uses the negative Wronskian sign. -/
theorem besselCross_zero_one_self (x : ℝ) (hx : 0 < x) :
    besselCross 0 1 x x = -2 / (Real.pi * x) := by
  simpa [besselCross] using besselYInt_cross_zero_one x hx

/-- This diagonal cross product never vanishes on the positive axis. -/
theorem besselCross_zero_one_self_ne_zero (x : ℝ) (hx : 0 < x) :
    besselCross 0 1 x x ≠ 0 := by
  rw [besselCross_zero_one_self x hx]
  exact div_ne_zero (by norm_num) (mul_ne_zero Real.pi_ne_zero (ne_of_gt hx))

/-- The two-by-two cross-product determinant factors into diagonal determinants. -/
theorem besselCross_determinant (s t : ℝ) :
    besselCross 0 0 s t * besselCross 1 1 s t -
      besselCross 0 1 s t * besselCross 1 0 s t =
      besselCross 0 1 s s * besselCross 0 1 t t := by
  unfold besselCross
  ring

/-- Under the specified root condition, the second adjacent order is minus order zero. -/
theorem besselCross_root_zero_two (z lambda : ℝ) (hz : 0 < z) (hl : 0 < lambda)
    (hroot : besselCross 0 1 z (lambda * z) = 0) :
    besselCross 0 2 z (lambda * z) = -besselCross 0 0 z (lambda * z) := by
  have ht : 0 < lambda * z := mul_pos hl hz
  have hJ := realBesselJ_recurrence 1 (lambda * z) ht
  have hY := besselYInt_recurrence 1 (lambda * z) ht
  norm_num at hJ hY
  unfold besselCross at hroot ⊢
  norm_num at hroot ⊢
  linear_combination realBesselJ 0 z * hY - besselYInt 0 z * hJ +
    (2 / (lambda * z)) * hroot

/-- The fixed root condition gives the scaled product required by the public denominator. -/
theorem besselCross_root_product (z lambda : ℝ) (hz : 0 < z) (hl : 0 < lambda)
    (hroot : besselCross 0 1 z (lambda * z) = 0) :
    lambda * besselCross 0 0 z (lambda * z) * besselCross 1 1 z (lambda * z) =
      (besselCross 0 1 z z) ^ 2 := by
  have hd := besselCross_determinant z (lambda * z)
  rw [hroot, zero_mul, sub_zero] at hd
  have hs : lambda * besselCross 0 1 (lambda * z) (lambda * z) =
      besselCross 0 1 z z := by
    rw [besselCross_zero_one_self _ (mul_pos hl hz), besselCross_zero_one_self _ hz]
    field_simp
  linear_combination lambda * hd + besselCross 0 1 z z * hs

/-- The order-zero cross product is nonzero at every positive scaled root. -/
theorem besselCross_root_zero_zero_ne_zero (z lambda : ℝ) (hz : 0 < z) (hl : 0 < lambda)
    (hroot : besselCross 0 1 z (lambda * z) = 0) :
    besselCross 0 0 z (lambda * z) ≠ 0 := by
  have hp := besselCross_root_product z lambda hz hl hroot
  have hn := pow_ne_zero 2 (besselCross_zero_one_self_ne_zero z hz)
  intro he
  rw [he, mul_zero, zero_mul] at hp
  exact hn hp.symm

/-- The left denominator factors without any division or denominator assumption. -/
theorem besselCross_root_denominator_factor (z lambda : ℝ) (hz : 0 < z) (hl : 0 < lambda)
    (hroot : besselCross 0 1 z (lambda * z) = 0) :
    (besselCross 0 1 z z) ^ 2 +
      lambda ^ 2 * besselCross 0 0 z (lambda * z) * besselCross 0 2 z (lambda * z) =
      lambda * besselCross 0 0 z (lambda * z) *
        (besselCross 1 1 z (lambda * z) - lambda * besselCross 0 0 z (lambda * z)) := by
  rw [besselCross_root_zero_two z lambda hz hl hroot,
    ← besselCross_root_product z lambda hz hl hroot]
  ring

/-- At a positive scaled root, the two displayed denominators vanish together. -/
theorem besselCross_root_denominator_ne_zero_iff (z lambda : ℝ) (hz : 0 < z)
    (hl : 0 < lambda) (hroot : besselCross 0 1 z (lambda * z) = 0) :
    (besselCross 0 1 z z) ^ 2 +
        lambda ^ 2 * besselCross 0 0 z (lambda * z) * besselCross 0 2 z (lambda * z) ≠ 0 ↔
      besselCross 1 1 z (lambda * z) - lambda * besselCross 0 0 z (lambda * z) ≠ 0 := by
  rw [besselCross_root_denominator_factor z lambda hz hl hroot]
  constructor
  · intro h hn
    exact h (by rw [hn, mul_zero])
  · intro h
    exact mul_ne_zero (mul_ne_zero (ne_of_gt hl)
      (besselCross_root_zero_zero_ne_zero z lambda hz hl hroot)) h


/-- The derivative in the second argument of the order-zero cross product. -/
theorem hasDerivAt_besselCross_zero_zero (z t : ℝ) (ht : 0 < t) :
    HasDerivAt (besselCross 0 0 z) (-besselCross 0 1 z t) t := by
  have hJ : HasDerivAt (realBesselJ 0) (-realBesselJ 1 t) t := by
    simpa using hasDerivAt_realBesselJ 0 t ht
  have hd := ((hasDerivAt_besselYInt_zero t ht).const_mul (realBesselJ 0 z)).sub
    (hJ.const_mul (besselYInt 0 z))
  convert hd using 1
  · ext u
    simp [besselCross]
  · simp only [besselCross, Int.cast_zero, Int.cast_one]
    ring

/-- The derivative in the second argument of the order-zero/one cross product. -/
theorem hasDerivAt_besselCross_zero_one (z t : ℝ) (ht : 0 < t) :
    HasDerivAt (besselCross 0 1 z)
      (besselCross 0 0 z t - besselCross 0 1 z t / t) t := by
  have hJ : HasDerivAt (realBesselJ 1) (realBesselJ 0 t - realBesselJ 1 t / t) t := by
    convert hasDerivAt_realBesselJ 1 t ht using 1
    have hr := realBesselJ_recurrence 1 t ht
    norm_num at hr ⊢
    linear_combination hr
  have hd := ((hasDerivAt_besselYInt_one t ht).const_mul (realBesselJ 0 z)).sub
    (hJ.const_mul (besselYInt 0 z))
  convert hd using 1
  · ext u
    simp [besselCross]
  · simp only [besselCross, Int.cast_zero, Int.cast_one]
    ring

/-- The radial energy primitive has derivative `t * X00(z,t)^2` on the positive axis. -/
theorem hasDerivAt_besselCross_energy (z t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => u ^ 2 / 2 *
      ((besselCross 0 0 z u) ^ 2 + (besselCross 0 1 z u) ^ 2))
      (t * (besselCross 0 0 z t) ^ 2) t := by
  have hd := (((hasDerivAt_id t).pow 2).div_const 2).mul
    (((hasDerivAt_besselCross_zero_zero z t ht).pow 2).add
      ((hasDerivAt_besselCross_zero_one z t ht).pow 2))
  change HasDerivAt (fun u : ℝ => u ^ 2 / 2 *
    ((besselCross 0 0 z u) ^ 2 + (besselCross 0 1 z u) ^ 2)) _ t at hd
  convert hd using 1
  dsimp
  field_simp
  ring

private theorem continuousOn_besselCross_energy_integrand (z lambda : ℝ)
    (hz : 0 < z) (hl : 0 < lambda) :
    ContinuousOn (fun t : ℝ => t * (besselCross 0 0 z t) ^ 2) (Icc (lambda * z) z) := by
  apply continuousOn_id.mul
  apply ContinuousOn.pow
  intro t ht
  exact (hasDerivAt_besselCross_zero_zero z t
    (lt_of_lt_of_le (mul_pos hl hz) ht.1)).continuousAt.continuousWithinAt

/-- The energy integral equals the original left denominator times `z^2 / 2`. -/
theorem besselCross_root_energy (z lambda : ℝ) (hz : 0 < z)
    (hl : 0 < lambda) (hl1 : lambda < 1)
    (hroot : besselCross 0 1 z (lambda * z) = 0) :
    z ^ 2 / 2 * ((besselCross 0 1 z z) ^ 2 +
      lambda ^ 2 * besselCross 0 0 z (lambda * z) * besselCross 0 2 z (lambda * z)) =
      ∫ t in (lambda * z)..z, t * (besselCross 0 0 z t) ^ 2 := by
  have hlt : lambda * z < z := by nlinarith
  have hc := continuousOn_besselCross_energy_integrand z lambda hz hl
  have hi : IntervalIntegrable (fun t : ℝ => t * (besselCross 0 0 z t) ^ 2) volume
      (lambda * z) z := hc.intervalIntegrable_of_Icc hlt.le
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := lambda * z) (b := z)
    (fun t ht => hasDerivAt_besselCross_energy z t (by
      rw [uIcc_of_le hlt.le] at ht
      exact lt_of_lt_of_le (mul_pos hl hz) ht.1)) hi
  have hself : besselCross 0 0 z z = 0 := by
    unfold besselCross
    ring
  rw [hf, hself, hroot, besselCross_root_zero_two z lambda hz hl hroot]
  ring

/-- The root condition and a nonzero lower endpoint make the energy integral positive. -/
theorem besselCross_root_energy_pos (z lambda : ℝ) (hz : 0 < z)
    (hl : 0 < lambda) (hl1 : lambda < 1)
    (hroot : besselCross 0 1 z (lambda * z) = 0) :
    0 < ∫ t in (lambda * z)..z, t * (besselCross 0 0 z t) ^ 2 := by
  have hlt : lambda * z < z := by nlinarith
  apply intervalIntegral.integral_pos hlt
    (continuousOn_besselCross_energy_integrand z lambda hz hl)
  · intro t ht
    exact mul_nonneg (le_of_lt (lt_trans (mul_pos hl hz) ht.1)) (sq_nonneg _)
  · refine ⟨lambda * z, ⟨le_rfl, hlt.le⟩, ?_⟩
    exact mul_pos (mul_pos hl hz)
      (sq_pos_of_ne_zero (besselCross_root_zero_zero_ne_zero z lambda hz hl hroot))

/-- The original left denominator is positive at a scaled root with `0 < lambda < 1`. -/
theorem besselCross_root_left_denominator_pos (z lambda : ℝ) (hz : 0 < z)
    (hl : 0 < lambda) (hl1 : lambda < 1)
    (hroot : besselCross 0 1 z (lambda * z) = 0) :
    0 < (besselCross 0 1 z z) ^ 2 +
      lambda ^ 2 * besselCross 0 0 z (lambda * z) * besselCross 0 2 z (lambda * z) := by
  have hp := besselCross_root_energy_pos z lambda hz hl hl1 hroot
  rw [← besselCross_root_energy z lambda hz hl hl1 hroot] at hp
  exact (mul_pos_iff_of_pos_left (div_pos (sq_pos_of_pos hz) (by norm_num))).mp hp

/-- The original right denominator is nonzero at a scaled root with `0 < lambda < 1`. -/
theorem besselCross_root_right_denominator_ne_zero (z lambda : ℝ) (hz : 0 < z)
    (hl : 0 < lambda) (hl1 : lambda < 1)
    (hroot : besselCross 0 1 z (lambda * z) = 0) :
    besselCross 1 1 z (lambda * z) - lambda * besselCross 0 0 z (lambda * z) ≠ 0 := by
  exact (besselCross_root_denominator_ne_zero_iff z lambda hz hl hroot).mp
    (ne_of_gt (besselCross_root_left_denominator_pos z lambda hz hl hl1 hroot))

/-- The original cross-product root identity, with both denominators proved nonzero. -/
theorem besselCross_root_identity (z lambda : ℝ) (hz : 0 < z)
    (hl : 0 < lambda) (hl1 : lambda < 1)
    (hroot : besselCross 0 1 z (lambda * z) = 0) :
    (besselCross 0 0 z (lambda * z)) ^ 2 /
      ((besselCross 0 1 z z) ^ 2 +
        lambda ^ 2 * besselCross 0 0 z (lambda * z) * besselCross 0 2 z (lambda * z)) =
      (1 / lambda) * besselCross 0 0 z (lambda * z) /
        (besselCross 1 1 z (lambda * z) - lambda * besselCross 0 0 z (lambda * z)) := by
  have ha := besselCross_root_zero_zero_ne_zero z lambda hz hl hroot
  have hb := besselCross_root_right_denominator_ne_zero z lambda hz hl hl1 hroot
  rw [besselCross_root_denominator_factor z lambda hz hl hroot]
  field_simp


end SpecialFunctionProofAgent
