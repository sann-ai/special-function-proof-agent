import SpecialFunctionProofAgent.LegendreCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Legendre orthogonality and squared norm

The shifted polynomial is the real coefficient image of mathlib's
`Polynomial.shiftedLegendre`, with the standard change of variables `(1 - x) / 2`.
Its finite coefficients give the self-adjoint differential equation
`(t * (1 - t) * qₙ′)′ = -n * (n + 1) * qₙ`.
Integrating the polynomial Wronskian proves orthogonality: the boundary weight
vanishes at both endpoints. The existing three-term recurrence then determines
successive squared norms from the degree-zero integral.
-/

open MeasureTheory Polynomial

namespace SpecialFunctionProofAgent

private noncomputable def seriesCoefficient (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * ((n + k).choose n : ℝ)

private theorem seriesCoefficient_next (n k : ℕ) :
    ((k : ℝ) + 1) ^ 2 * seriesCoefficient n (k + 1) =
      ((n : ℝ) - k) * ((n : ℝ) + k + 1) * seriesCoefficient n k := by
  by_cases hk : k ≤ n
  · have h₁ := congrArg (fun m : ℕ => (m : ℝ)) (Nat.choose_succ_right_eq n k)
    have h₂ := congrArg (fun m : ℕ => (m : ℝ)) (Nat.choose_mul_succ_eq (n + k) n)
    have he : n + k + 1 - n = k + 1 := by omega
    rw [he] at h₂
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk] at h₁ h₂
    dsimp [seriesCoefficient]
    rw [show n + (k + 1) = n + k + 1 by omega]
    linear_combination ((k : ℝ) + 1) * ((n + k + 1).choose n : ℝ) * h₁ -
      ((n : ℝ) - k) * (n.choose k : ℝ) * h₂
  · simp [seriesCoefficient, Nat.choose_eq_zero_of_lt (show n < k by omega),
      Nat.choose_eq_zero_of_lt (show n < k + 1 by omega)]

private noncomputable def shiftedP (n : ℕ) : Polynomial ℝ :=
  (Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)

private theorem shiftedP_coeff (n k : ℕ) :
    (shiftedP n).coeff k = (-1 : ℝ) ^ k * seriesCoefficient n k := by
  simp [shiftedP, seriesCoefficient, Polynomial.coeff_shiftedLegendre]
  ring

private theorem shiftedP_ode (n : ℕ) :
    derivative ((X - X ^ 2) * derivative (shiftedP n)) = -C ((n : ℝ) * (n + 1)) * shiftedP n := by
  ext k
  rw [coeff_derivative, sub_mul, pow_two, mul_assoc, coeff_sub, coeff_X_mul]
  cases k with
  | zero =>
    simp only [coeff_derivative, shiftedP_coeff, pow_zero,
      neg_mul, coeff_neg, coeff_C_mul, Nat.cast_zero]
    have h := seriesCoefficient_next n 0
    norm_num at h ⊢
    exact h
  | succ k =>
    simp only [coeff_X_mul, coeff_derivative, neg_mul, coeff_neg, coeff_C_mul, shiftedP_coeff,
      pow_succ, Nat.cast_add, Nat.cast_one]
    have h := seriesCoefficient_next n (k + 1)
    simp only [Nat.cast_add, Nat.cast_one] at h
    linear_combination (-1 : ℝ) ^ k * h

private theorem shiftedP_wronskian (m n : ℕ) :
    derivative ((X - X ^ 2) *
      (derivative (shiftedP m) * shiftedP n - shiftedP m * derivative (shiftedP n))) =
      C (((n : ℝ) * (n + 1)) - ((m : ℝ) * (m + 1))) * (shiftedP m * shiftedP n) := by
  have he : (X - X ^ 2) * (derivative (shiftedP m) * shiftedP n - shiftedP m * derivative (shiftedP n)) =
      ((X - X ^ 2) * derivative (shiftedP m)) * shiftedP n -
        shiftedP m * ((X - X ^ 2) * derivative (shiftedP n)) := by ring
  rw [he, derivative_sub, derivative_mul, shiftedP_ode m, derivative_mul, shiftedP_ode n, C_sub]
  ring

private theorem shiftedP_orthogonal (m n : ℕ) (hmn : m ≠ n) :
    (∫ t in (0 : ℝ)..1, (shiftedP m).eval t * (shiftedP n).eval t) = 0 := by
  let w : Polynomial ℝ :=
    (X - X ^ 2) * (derivative (shiftedP m) * shiftedP n - shiftedP m * derivative (shiftedP n))
  have hd : derivative w =
      C (((n : ℝ) * (n + 1)) - ((m : ℝ) * (m + 1))) * (shiftedP m * shiftedP n) :=
    shiftedP_wronskian m n
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ => w.hasDerivAt t)
    ((derivative w).continuous.intervalIntegrable 0 1)
  rw [hd] at hi
  norm_num [w, eval_mul, eval_sub, eval_pow, intervalIntegral.integral_const_mul] at hi
  have hc : ((n : ℝ) * (n + 1)) - ((m : ℝ) * (m + 1)) ≠ 0 := by
    intro he
    have hf : ((n : ℝ) - m) * ((n : ℝ) + m + 1) = 0 := by nlinarith
    have hp : (n : ℝ) + m + 1 ≠ 0 := by positivity
    have he' := (mul_eq_zero.mp hf).resolve_right hp
    apply hmn
    exact_mod_cast (show (m : ℝ) = n by linarith)
  exact hi.resolve_left hc

private theorem shiftedP_eval (n : ℕ) (x : ℝ) :
    (shiftedP n).eval ((1 - x) / 2) = legendreP n x := by
  simp [shiftedP, legendreP, eval_map, aeval_def]

/-- Distinct natural Legendre degrees are orthogonal on the standard interval. -/
theorem legendreP_orthogonal (m n : ℕ) (h : m ≠ n) :
    (∫ t in (-1 : ℝ)..1, legendreP m t * legendreP n t) = 0 := by
  have hs := shiftedP_orthogonal m n h
  have ht := intervalIntegral.integral_comp_mul_add
    (fun t : ℝ => (shiftedP m).eval t * (shiftedP n).eval t)
    (a := (-1 : ℝ)) (b := 1) (c := (-1 / 2 : ℝ)) (by norm_num) (1 / 2)
  have hsrev : (∫ t in (1 : ℝ)..0, (shiftedP m).eval t * (shiftedP n).eval t) = 0 := by
    rw [intervalIntegral.integral_symm, hs]
    simp
  norm_num [hsrev] at ht
  have he : (fun t : ℝ => (shiftedP m).eval (-(1 / 2 * t) + 1 / 2) *
      (shiftedP n).eval (-(1 / 2 * t) + 1 / 2)) =
      (fun t : ℝ => legendreP m t * legendreP n t) := by
    funext t
    rw [show -(1 / 2 * t) + (1 / 2 : ℝ) = (1 - t) / 2 by ring, shiftedP_eval, shiftedP_eval]
  rw [he] at ht
  exact ht

private theorem legendreP_recurrence_all (n : ℕ) (x : ℝ) :
    ((n : ℝ) + 1) * legendreP (n + 1) x =
      (2 * (n : ℝ) + 1) * x * legendreP n x - (n : ℝ) * legendreP (n - 1) x := by
  cases n with
  | zero => simp
  | succ n => exact legendreP_recurrence (n + 1) x (by omega)

private theorem legendreP_norm_step (n : ℕ) :
    (2 * (n : ℝ) + 3) * (∫ t in (-1 : ℝ)..1, (legendreP (n + 1) t) ^ 2) =
      (2 * (n : ℝ) + 1) * (∫ t in (-1 : ℝ)..1, (legendreP n t) ^ 2) := by
  let i (k : ℕ) := ∫ t in (-1 : ℝ)..1, (legendreP k t) ^ 2
  let k := ∫ t in (-1 : ℝ)..1, t * legendreP n t * legendreP (n + 1) t
  have hk : IntervalIntegrable (fun t : ℝ => t * legendreP n t * legendreP (n + 1) t)
      volume (-1) 1 :=
    ((continuous_id.mul (continuous_legendreP n)).mul
      (continuous_legendreP (n + 1))).intervalIntegrable _ _
  have hp : IntervalIntegrable (fun t : ℝ => legendreP (n - 1) t * legendreP (n + 1) t)
      volume (-1) 1 :=
    ((continuous_legendreP (n - 1)).mul (continuous_legendreP (n + 1))).intervalIntegrable _ _
  have hq : IntervalIntegrable (fun t : ℝ => legendreP (n + 1 + 1) t * legendreP n t)
      volume (-1) 1 :=
    ((continuous_legendreP (n + 1 + 1)).mul (continuous_legendreP n)).intervalIntegrable _ _
  have hleft : ((n : ℝ) + 1) * i (n + 1) = (2 * (n : ℝ) + 1) * k := by
    calc
      _ = ∫ t in (-1 : ℝ)..1, ((n : ℝ) + 1) * (legendreP (n + 1) t) ^ 2 :=
        (intervalIntegral.integral_const_mul _ _).symm
      _ = ∫ t in (-1 : ℝ)..1,
          (2 * (n : ℝ) + 1) * (t * legendreP n t * legendreP (n + 1) t) -
            (n : ℝ) * (legendreP (n - 1) t * legendreP (n + 1) t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        linear_combination legendreP (n + 1) t * legendreP_recurrence_all n t
      _ = _ := by
        rw [intervalIntegral.integral_sub (hk.const_mul _) (hp.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          legendreP_orthogonal (n - 1) (n + 1) (by omega)]
        simp [k]
  have hright : ((n : ℝ) + 1) * i n = (2 * (n : ℝ) + 3) * k := by
    calc
      _ = ∫ t in (-1 : ℝ)..1, ((n : ℝ) + 1) * (legendreP n t) ^ 2 :=
        (intervalIntegral.integral_const_mul _ _).symm
      _ = ∫ t in (-1 : ℝ)..1,
          (2 * (n : ℝ) + 3) * (t * legendreP n t * legendreP (n + 1) t) -
            ((n : ℝ) + 2) * (legendreP (n + 1 + 1) t * legendreP n t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have h := legendreP_recurrence_all (n + 1) t
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h
        linear_combination legendreP n t * h
      _ = _ := by
        rw [intervalIntegral.integral_sub (hk.const_mul _) (hq.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          legendreP_orthogonal (n + 1 + 1) n (by omega)]
        simp [k]
  change (2 * (n : ℝ) + 3) * i (n + 1) = (2 * (n : ℝ) + 1) * i n
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  apply mul_left_cancel₀ hn
  linear_combination (2 * (n : ℝ) + 3) * hleft - (2 * (n : ℝ) + 1) * hright

/-- The standard Legendre squared norm on `[-1, 1]`. -/
theorem legendreP_norm (n : ℕ) :
    (∫ t in (-1 : ℝ)..1, (legendreP n t) ^ 2) = 2 / (2 * (n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h := legendreP_norm_step n
    rw [ih] at h
    have hn : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    have he : (2 * (n : ℝ) + 1) * (2 / (2 * (n : ℝ) + 1)) = 2 := by field_simp
    rw [he] at h
    simp only [Nat.cast_add, Nat.cast_one]
    apply (eq_div_iff (by positivity)).mpr
    linear_combination h

end SpecialFunctionProofAgent
