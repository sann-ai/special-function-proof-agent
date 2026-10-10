import SpecialFunctionProofAgent.Legendre
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory

namespace SpecialFunctionProofAgent

/-- The standard Legendre polynomial is continuous on the real line. -/
theorem continuous_legendreP (n : ℕ) : Continuous (legendreP n) := by
  unfold legendreP
  fun_prop

/-- Consecutive degrees have an odd product, hence zero integral on `[-1, 1]`. -/
theorem legendreP_adjacent_integral (n : ℕ) :
    (∫ t in (-1 : ℝ)..1, legendreP n t * legendreP (n + 1) t) = 0 := by
  have hp (t : ℝ) : legendreP n (-t) * legendreP (n + 1) (-t) =
      -(legendreP n t * legendreP (n + 1) t) := by
    rw [legendreP_neg, legendreP_neg, pow_succ]
    have hs : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    linear_combination -(legendreP n t * legendreP (n + 1) t) * hs
  have hi := intervalIntegral.integral_comp_neg
    (f := fun t : ℝ => legendreP n t * legendreP (n + 1) t)
    (a := (-1 : ℝ)) (b := 1)
  simp only [hp, intervalIntegral.integral_neg, neg_neg] at hi
  linarith

private noncomputable def legendreSeriesCoefficient (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * ((n + k).choose n : ℝ)

private theorem legendreSeriesCoefficient_raise (n k : ℕ) (hk : k ≤ n + 1) :
    ((n : ℝ) + 1 - k) * legendreSeriesCoefficient (n + 1) k =
      ((n : ℝ) + k + 1) * legendreSeriesCoefficient n k := by
  have h₁ := congrArg (fun m : ℕ => (m : ℝ)) (Nat.choose_mul_succ_eq n k)
  have h₂ := congrArg (fun m : ℕ => (m : ℝ)) (Nat.add_one_mul_choose_eq (n + k) n)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk] at h₁ h₂
  have he : n + 1 + k = n + k + 1 := by omega
  dsimp [legendreSeriesCoefficient]
  rw [he]
  linear_combination -((n + k + 1).choose (n + 1) : ℝ) * h₁ - (n.choose k : ℝ) * h₂

private theorem legendreSeriesCoefficient_next (n k : ℕ) (hk : k ≤ n) :
    ((k : ℝ) + 1) ^ 2 * legendreSeriesCoefficient n (k + 1) =
      ((n : ℝ) - k) * ((n : ℝ) + k + 1) * legendreSeriesCoefficient n k := by
  have h₁ := congrArg (fun m : ℕ => (m : ℝ)) (Nat.choose_succ_right_eq n k)
  have h₂ := congrArg (fun m : ℕ => (m : ℝ)) (Nat.choose_mul_succ_eq (n + k) n)
  have he : n + k + 1 - n = k + 1 := by omega
  rw [he] at h₂
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk] at h₁ h₂
  dsimp [legendreSeriesCoefficient]
  rw [show n + (k + 1) = n + k + 1 by omega]
  linear_combination ((k : ℝ) + 1) * ((n + k + 1).choose n : ℝ) * h₁ -
    ((n : ℝ) - k) * (n.choose k : ℝ) * h₂

private theorem legendreSeriesCoefficient_recurrence (n k : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) + 1) * legendreSeriesCoefficient (n + 1) (k + 1) =
      (2 * (n : ℝ) + 1) * legendreSeriesCoefficient n (k + 1) +
      2 * (2 * (n : ℝ) + 1) * legendreSeriesCoefficient n k -
      (n : ℝ) * legendreSeriesCoefficient (n - 1) (k + 1) := by
  rcases lt_trichotomy k n with hk | heq | hk
  · have h₁ := legendreSeriesCoefficient_raise n (k + 1) (by omega)
    have h₂ := legendreSeriesCoefficient_raise (n - 1) (k + 1) (by omega)
    have h₃ := legendreSeriesCoefficient_next n k (by omega)
    rw [Nat.sub_add_cancel hn] at h₂
    simp only [Nat.cast_sub hn, Nat.cast_one, Nat.cast_add] at h₁ h₂ h₃
    have hm : ((n : ℝ) - k) * ((n : ℝ) + k + 1) ≠ 0 := by
      have hkn : (k : ℝ) < n := by exact_mod_cast hk
      positivity
    apply (mul_left_cancel₀ hm)
    linear_combination ((n : ℝ) + 1) * ((n : ℝ) + k + 1) * h₁ -
      (n : ℝ) * ((n : ℝ) - k) * h₂ + 2 * (2 * (n : ℝ) + 1) * h₃
  · subst k
    have h₁ := legendreSeriesCoefficient_raise n n (by omega)
    have h₂ := legendreSeriesCoefficient_next (n + 1) n (by omega)
    have hz : legendreSeriesCoefficient n (n + 1) = 0 := by simp [legendreSeriesCoefficient]
    have hz' : legendreSeriesCoefficient (n - 1) (n + 1) = 0 := by
      simp [legendreSeriesCoefficient, Nat.choose_eq_zero_of_lt (show n - 1 < n + 1 by omega)]
    rw [hz, hz']
    simp only [Nat.cast_add, Nat.cast_one] at h₁ h₂
    have hn' : (n : ℝ) + 1 ≠ 0 := by positivity
    apply (mul_left_cancel₀ hn')
    linear_combination h₂ + (2 * (n : ℝ) + 2) * h₁
  · have h₁ : n + 1 < k + 1 := by omega
    have h₂ : n < k + 1 := by omega
    have h₃ : n - 1 < k + 1 := by omega
    simp [legendreSeriesCoefficient, Nat.choose_eq_zero_of_lt hk, Nat.choose_eq_zero_of_lt h₁,
      Nat.choose_eq_zero_of_lt h₂, Nat.choose_eq_zero_of_lt h₃]

private noncomputable def shiftedLegendreReal (n : ℕ) : Polynomial ℝ :=
  (Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)

private theorem shiftedLegendreReal_coeff (n k : ℕ) :
    (shiftedLegendreReal n).coeff k = (-1 : ℝ) ^ k * legendreSeriesCoefficient n k := by
  simp [shiftedLegendreReal, legendreSeriesCoefficient, Polynomial.coeff_shiftedLegendre]
  ring

private theorem shiftedLegendreReal_recurrence (n : ℕ) (hn : 1 ≤ n) :
    Polynomial.C ((n : ℝ) + 1) * shiftedLegendreReal (n + 1) =
      Polynomial.C (2 * (n : ℝ) + 1) * shiftedLegendreReal n -
      Polynomial.C (2 * (2 * (n : ℝ) + 1)) * (Polynomial.X * shiftedLegendreReal n) -
      Polynomial.C (n : ℝ) * shiftedLegendreReal (n - 1) := by
  ext k
  cases k with
  | zero =>
    simp [shiftedLegendreReal_coeff, legendreSeriesCoefficient]
    ring
  | succ k =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_mul, shiftedLegendreReal_coeff, pow_succ]
    linear_combination -(-1 : ℝ) ^ k * legendreSeriesCoefficient_recurrence n k hn

/-- The standard three-term recurrence for every positive natural degree. -/
theorem legendreP_recurrence (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    ((n : ℝ) + 1) * legendreP (n + 1) x =
      (2 * (n : ℝ) + 1) * x * legendreP n x - (n : ℝ) * legendreP (n - 1) x := by
  have he (m : ℕ) : Polynomial.eval ((1 - x) / 2) (shiftedLegendreReal m) = legendreP m x := by
    simp [shiftedLegendreReal, legendreP, Polynomial.eval_map, Polynomial.aeval_def]
  have h := congrArg (Polynomial.eval ((1 - x) / 2)) (shiftedLegendreReal_recurrence n hn)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X, he] at h
  linear_combination h

end SpecialFunctionProofAgent
