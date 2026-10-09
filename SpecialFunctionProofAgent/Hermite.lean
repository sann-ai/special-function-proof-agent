import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace SpecialFunctionProofAgent

/-- Probabilists' Hermite polynomial, evaluated on the real line. -/
noncomputable def hermiteHe (n : ℕ) (x : ℝ) : ℝ :=
  Polynomial.aeval x (Polynomial.hermite n)

/-- Physicists' Hermite polynomial, scaled from mathlib's probabilists' convention. -/
noncomputable def hermiteH (n : ℕ) (x : ℝ) : ℝ :=
  (Real.sqrt 2) ^ n * hermiteHe n (Real.sqrt 2 * x)

/-- The precise conversion between physicists' and probabilists' conventions. -/
theorem hermiteH_eq_scaled_hermiteHe (n : ℕ) (x : ℝ) :
    hermiteH n x = (Real.sqrt 2) ^ n * hermiteHe n (Real.sqrt 2 * x) := rfl

private theorem derivative_hermite_succ (n : ℕ) :
    Polynomial.derivative (Polynomial.hermite (n + 1)) =
      Polynomial.C (n + 1 : ℤ) * Polynomial.hermite n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Polynomial.hermite_succ (n + 1), Polynomial.derivative_sub,
      Polynomial.derivative_mul, Polynomial.derivative_X, one_mul, ih,
      Polynomial.derivative_C_mul]
    rw [Polynomial.hermite_succ n]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

/-- Differentiation lowers the probabilists' degree by one. -/
theorem hasDerivAt_hermiteHe_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteHe (n + 1)) ((n + 1 : ℕ) * hermiteHe n x) x := by
  change HasDerivAt (fun y : ℝ => Polynomial.aeval y (Polynomial.hermite (n + 1)))
    ((n + 1 : ℕ) * Polynomial.aeval x (Polynomial.hermite n)) x
  have h := (Polynomial.hermite (n + 1)).hasDerivAt_aeval x
  rw [derivative_hermite_succ] at h
  simpa only [map_mul, Polynomial.aeval_C, map_add, map_natCast, map_one,
    Nat.cast_add, Nat.cast_one] using h

/-- Differentiation of the probabilists' Hermite polynomial of positive degree. -/
theorem hermiteHe_derivative (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    deriv (hermiteHe n) x = (n : ℝ) * hermiteHe (n - 1) x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa using (hasDerivAt_hermiteHe_succ k x).deriv

@[simp] theorem hermiteHe_zero (x : ℝ) : hermiteHe 0 x = 1 := by
  simp [hermiteHe]

@[simp] theorem hermiteHe_one (x : ℝ) : hermiteHe 1 x = x := by
  simp [hermiteHe]

@[simp] theorem hermiteH_zero (x : ℝ) : hermiteH 0 x = 1 := by
  simp [hermiteH]

@[simp] theorem hermiteH_one (x : ℝ) : hermiteH 1 x = 2 * x := by
  simp only [hermiteH, pow_one, hermiteHe_one, ← mul_assoc,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Differentiation lowers the physicists' degree by one. -/
theorem hasDerivAt_hermiteH_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteH (n + 1)) (2 * (n + 1 : ℕ) * hermiteH n x) x := by
  have h := ((hasDerivAt_hermiteHe_succ n (Real.sqrt 2 * x)).comp x
    ((hasDerivAt_id x).const_mul (Real.sqrt 2))).const_mul ((Real.sqrt 2) ^ (n + 1))
  convert h using 1
  · rfl
  · simp only [hermiteH, pow_succ]
    have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    linear_combination -(Real.sqrt 2 ^ n * (n + 1 : ℕ) *
      hermiteHe n (Real.sqrt 2 * x)) * hs

/-- The derivative formula for physicists' Hermite polynomials of positive degree. -/
theorem hermiteH_derivative (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    deriv (hermiteH n) x = 2 * (n : ℝ) * hermiteH (n - 1) x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa using (hasDerivAt_hermiteH_succ k x).deriv

/-- The probabilists' Hermite recurrence. -/
theorem hermiteHe_succ_succ (n : ℕ) (x : ℝ) :
    hermiteHe (n + 2) x = x * hermiteHe (n + 1) x - (n + 1 : ℕ) * hermiteHe n x := by
  simp only [hermiteHe, show n + 2 = (n + 1) + 1 from rfl,
    Polynomial.hermite_succ (n + 1), derivative_hermite_succ]
  simp

/-- The physicists' Hermite recurrence in successor form. -/
theorem hermiteH_succ_succ (n : ℕ) (x : ℝ) :
    hermiteH (n + 2) x = 2 * x * hermiteH (n + 1) x -
      2 * (n + 1 : ℕ) * hermiteH n x := by
  simp only [hermiteH, hermiteHe_succ_succ, pow_succ]
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  linear_combination (Real.sqrt 2 ^ n * (Real.sqrt 2 * x *
    hermiteHe (n + 1) (Real.sqrt 2 * x) - (n + 1 : ℕ) *
    hermiteHe n (Real.sqrt 2 * x))) * hs

/-- The physicists' three-term recurrence for positive degree. -/
theorem hermiteH_recurrence (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    hermiteH (n + 1) x = 2 * x * hermiteH n x -
      2 * (n : ℝ) * hermiteH (n - 1) x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa using hermiteH_succ_succ k x

end SpecialFunctionProofAgent
