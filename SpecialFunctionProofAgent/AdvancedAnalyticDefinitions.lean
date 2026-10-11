import SpecialFunctionProofAgent.UserAnalyticDefinitions
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open MeasureTheory

namespace SpecialFunctionProofAgent

/-- The finite closed form associated with real geometric kernels. -/
noncomputable def finiteGeometricCombination (terms : List (ℝ × ℝ)) : ℝ :=
  (terms.map (fun term => term.1 / (1 - term.2))).sum

/-- The actual infinite sum of a finite real combination of geometric kernels. -/
noncomputable def geometricCombination (terms : List (ℝ × ℝ)) : ℝ :=
  ∑' n : ℕ, (terms.map (fun term => term.1 * term.2 ^ n)).sum

/-- Absolute ratio bounds ensure convergence of every kernel in the finite combination. -/
theorem hasSum_geometricCombination (terms : List (ℝ × ℝ))
    (h : ∀ term ∈ terms, |term.2| < 1) :
    HasSum (fun n : ℕ => (terms.map (fun term => term.1 * term.2 ^ n)).sum)
      (finiteGeometricCombination terms) := by
  induction terms with
  | nil => simpa only [List.map_nil, List.sum_nil, finiteGeometricCombination] using
      (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  | cons term terms ih =>
      have ht : ‖term.2‖ < 1 := by simpa only [Real.norm_eq_abs] using h term (by simp)
      have hs := (hasSum_geometric_of_norm_lt_one ht).mul_left term.1
      have hi := ih (fun t ht => h t (by simp only [List.mem_cons]; exact Or.inr ht))
      simpa only [finiteGeometricCombination, List.map_cons, List.sum_cons, div_eq_mul_inv] using hs.add hi

/-- The geometric combination is summable under the explicit ratio bounds. -/
theorem summable_geometricCombination (terms : List (ℝ × ℝ))
    (h : ∀ term ∈ terms, |term.2| < 1) :
    Summable (fun n : ℕ => (terms.map (fun term => term.1 * term.2 ^ n)).sum) :=
  (hasSum_geometricCombination terms h).summable

/-- The convergent geometric combination equals the finite rational expression. -/
theorem geometricCombination_eq_finiteGeometricCombination (terms : List (ℝ × ℝ))
    (h : ∀ term ∈ terms, |term.2| < 1) :
    geometricCombination terms = finiteGeometricCombination terms :=
  (hasSum_geometricCombination terms h).tsum_eq

/-- This rational parametrization stays strictly inside the geometric convergence interval. -/
theorem abs_div_one_add_sq_lt_one (u : ℝ) : |u / (1 + u ^ 2)| < 1 := by
  have hd : 0 < 1 + u ^ 2 := by positivity
  rw [abs_div, abs_of_pos hd, div_lt_one hd]
  nlinarith [sq_abs u, sq_nonneg (|u| - 1 / 2)]

/-- A primitive of an affine exponential, including the zero-slope case. -/
noncomputable def affineExpPrimitive (a b x : ℝ) : ℝ :=
  if a = 0 then x * Real.exp b else Real.exp (a * x + b) / a

/-- A primitive of an affine sine, including the zero-slope case. -/
noncomputable def affineSinPrimitive (a b x : ℝ) : ℝ :=
  if a = 0 then x * Real.sin b else -Real.cos (a * x + b) / a

/-- A primitive of an affine cosine, including the zero-slope case. -/
noncomputable def affineCosPrimitive (a b x : ℝ) : ℝ :=
  if a = 0 then x * Real.cos b else Real.sin (a * x + b) / a

theorem hasDerivAt_affineExpPrimitive (a b x : ℝ) :
    HasDerivAt (affineExpPrimitive a b) (Real.exp (a * x + b)) x := by
  by_cases ha : a = 0
  · subst a
    convert (hasDerivAt_id x).mul_const (Real.exp b) using 1
    · funext y; simp [affineExpPrimitive]
    · simp
  · unfold affineExpPrimitive
    simp only [ha, ↓reduceIte]
    convert ((((hasDerivAt_id x).const_mul a).add_const b).exp.div_const a) using 1
    · rfl
    · change Real.exp (a * x + b) = Real.exp (a * x + b) * (a * 1) / a
      field_simp

theorem hasDerivAt_affineSinPrimitive (a b x : ℝ) :
    HasDerivAt (affineSinPrimitive a b) (Real.sin (a * x + b)) x := by
  by_cases ha : a = 0
  · subst a
    convert (hasDerivAt_id x).mul_const (Real.sin b) using 1
    · funext y; simp [affineSinPrimitive]
    · simp
  · unfold affineSinPrimitive
    simp only [ha, ↓reduceIte]
    convert ((((hasDerivAt_id x).const_mul a).add_const b).cos.neg.div_const a) using 1
    · rfl
    · change Real.sin (a * x + b) = -(-Real.sin (a * x + b) * (a * 1)) / a
      field_simp

theorem hasDerivAt_affineCosPrimitive (a b x : ℝ) :
    HasDerivAt (affineCosPrimitive a b) (Real.cos (a * x + b)) x := by
  by_cases ha : a = 0
  · subst a
    convert (hasDerivAt_id x).mul_const (Real.cos b) using 1
    · funext y; simp [affineCosPrimitive]
    · simp
  · unfold affineCosPrimitive
    simp only [ha, ↓reduceIte]
    convert ((((hasDerivAt_id x).const_mul a).add_const b).sin.div_const a) using 1
    · rfl
    · change Real.cos (a * x + b) = Real.cos (a * x + b) * (a * 1) / a
      field_simp

/-- Each term is `(coefficient, slope, intercept)`; the three lists select exp, sin, and cos. -/
noncomputable def elementaryCombination (exps sins coss : List (ℝ × ℝ × ℝ)) (x : ℝ) : ℝ :=
  (exps.map (fun term => term.1 * Real.exp (term.2.1 * x + term.2.2))).sum +
  (sins.map (fun term => term.1 * Real.sin (term.2.1 * x + term.2.2))).sum +
  (coss.map (fun term => term.1 * Real.cos (term.2.1 * x + term.2.2))).sum

/-- The finite termwise primitive retains the zero-slope branches. -/
noncomputable def elementaryPrimitive (exps sins coss : List (ℝ × ℝ × ℝ)) (x : ℝ) : ℝ :=
  (exps.map (fun term => term.1 * affineExpPrimitive term.2.1 term.2.2 x)).sum +
  (sins.map (fun term => term.1 * affineSinPrimitive term.2.1 term.2.2 x)).sum +
  (coss.map (fun term => term.1 * affineCosPrimitive term.2.1 term.2.2 x)).sum

private theorem hasDerivAt_list_sum {α : Type*} (terms : List α) (f g : α → ℝ → ℝ)
    (h : ∀ term x, HasDerivAt (f term) (g term x) x) (x : ℝ) :
    HasDerivAt (fun y => (terms.map (fun term => f term y)).sum)
      (terms.map (fun term => g term x)).sum x := by
  induction terms with
  | nil => simpa only [List.map_nil, List.sum_nil] using hasDerivAt_const x (0 : ℝ)
  | cons term terms ih =>
      convert (h term x).add ih using 1 <;> rfl

private theorem continuous_list_sum {α : Type*} (terms : List α) (f : α → ℝ → ℝ)
    (h : ∀ term, Continuous (f term)) :
    Continuous (fun x => (terms.map (fun term => f term x)).sum) := by
  induction terms with
  | nil => simpa only [List.map_nil, List.sum_nil] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  | cons term terms ih =>
      convert (h term).add ih using 1
      rfl

theorem hasDerivAt_elementaryPrimitive (exps sins coss : List (ℝ × ℝ × ℝ)) (x : ℝ) :
    HasDerivAt (elementaryPrimitive exps sins coss) (elementaryCombination exps sins coss x) x := by
  have he := hasDerivAt_list_sum exps
    (fun term x => term.1 * affineExpPrimitive term.2.1 term.2.2 x)
    (fun term x => term.1 * Real.exp (term.2.1 * x + term.2.2))
    (fun term x => (hasDerivAt_affineExpPrimitive term.2.1 term.2.2 x).const_mul term.1) x
  have hs := hasDerivAt_list_sum sins
    (fun term x => term.1 * affineSinPrimitive term.2.1 term.2.2 x)
    (fun term x => term.1 * Real.sin (term.2.1 * x + term.2.2))
    (fun term x => (hasDerivAt_affineSinPrimitive term.2.1 term.2.2 x).const_mul term.1) x
  have hc := hasDerivAt_list_sum coss
    (fun term x => term.1 * affineCosPrimitive term.2.1 term.2.2 x)
    (fun term x => term.1 * Real.cos (term.2.1 * x + term.2.2))
    (fun term x => (hasDerivAt_affineCosPrimitive term.2.1 term.2.2 x).const_mul term.1) x
  convert (he.add hs).add hc using 1 <;> rfl

theorem continuous_elementaryCombination (exps sins coss : List (ℝ × ℝ × ℝ)) :
    Continuous (elementaryCombination exps sins coss) := by
  have he := continuous_list_sum exps
    (fun term x => term.1 * Real.exp (term.2.1 * x + term.2.2)) (by intro term; fun_prop)
  have hs := continuous_list_sum sins
    (fun term x => term.1 * Real.sin (term.2.1 * x + term.2.2)) (by intro term; fun_prop)
  have hc := continuous_list_sum coss
    (fun term x => term.1 * Real.cos (term.2.1 * x + term.2.2)) (by intro term; fun_prop)
  exact (he.add hs).add hc

theorem intervalIntegrable_elementaryCombination (exps sins coss : List (ℝ × ℝ × ℝ)) (a b : ℝ) :
    IntervalIntegrable (elementaryCombination exps sins coss) volume a b :=
  (continuous_elementaryCombination exps sins coss).intervalIntegrable a b

/-- The actual oriented integral of the elementary combination. -/
noncomputable def elementaryIntegral (exps sins coss : List (ℝ × ℝ × ℝ)) (a b : ℝ) : ℝ :=
  ∫ t in a..b, elementaryCombination exps sins coss t

theorem elementaryIntegral_eq_primitive_sub (exps sins coss : List (ℝ × ℝ × ℝ)) (a b : ℝ) :
    elementaryIntegral exps sins coss a b =
      elementaryPrimitive exps sins coss b - elementaryPrimitive exps sins coss a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_elementaryPrimitive exps sins coss x)
    (intervalIntegrable_elementaryCombination exps sins coss a b)

private theorem eq_of_global_hasDerivAt_eq (f g f' : ℝ → ℝ) (t0 : ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (f' x) x)
    (h0 : f t0 = g t0) : f = g := by
  have hd (x : ℝ) : HasDerivAt (fun t => f t - g t) 0 x := by
    convert (hf x).sub (hg x) using 1
    ring
  funext x
  have hc := is_const_of_deriv_eq_zero
    (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) x t0
  exact sub_eq_zero.mp (hc.trans (sub_eq_zero.mpr h0))

/-- The global solution of `y' = p(t) * sqrt(1+y^2)`, with arbitrary real initial data. -/
noncomputable def nonlinearPolynomialIVPSolution (terms : List (ℝ × ℕ))
    (t0 initial x : ℝ) : ℝ :=
  Real.sinh (Real.arsinh initial + primitivePolynomial terms x - primitivePolynomial terms t0)

theorem nonlinearPolynomialIVPSolution_eq_sinh (terms : List (ℝ × ℕ)) (t0 initial x : ℝ) :
    nonlinearPolynomialIVPSolution terms t0 initial x =
      Real.sinh (Real.arsinh initial + primitivePolynomial terms x - primitivePolynomial terms t0) := rfl

theorem hasDerivAt_nonlinearPolynomialIVPSolution (terms : List (ℝ × ℕ)) (t0 initial x : ℝ) :
    HasDerivAt (nonlinearPolynomialIVPSolution terms t0 initial)
      (evalPolynomial terms x * Real.sqrt (1 + (nonlinearPolynomialIVPSolution terms t0 initial x) ^ 2)) x := by
  unfold nonlinearPolynomialIVPSolution
  convert (((hasDerivAt_primitivePolynomial terms x).const_add (Real.arsinh initial)).sub_const
    (primitivePolynomial terms t0)).sinh using 1
  have hc := Real.cosh_arsinh (Real.sinh
    (Real.arsinh initial + primitivePolynomial terms x - primitivePolynomial terms t0))
  simp only [Real.arsinh_sinh] at hc
  rw [hc]
  ring

@[simp] theorem nonlinearPolynomialIVPSolution_initial (terms : List (ℝ × ℕ)) (t0 initial : ℝ) :
    nonlinearPolynomialIVPSolution terms t0 initial t0 = initial := by
  simp only [nonlinearPolynomialIVPSolution, add_sub_cancel_right, Real.sinh_arsinh]

/-- The inverse-hyperbolic-sine transformation proves uniqueness among global differentiable solutions. -/
theorem nonlinearPolynomialIVPSolution_unique (terms : List (ℝ × ℕ)) (t0 initial : ℝ)
    (y : ℝ → ℝ)
    (hy : ∀ x, HasDerivAt y (evalPolynomial terms x * Real.sqrt (1 + (y x) ^ 2)) x)
    (h0 : y t0 = initial) : y = nonlinearPolynomialIVPSolution terms t0 initial := by
  have ht (x : ℝ) : HasDerivAt (fun t => Real.arsinh (y t)) (evalPolynomial terms x) x := by
    have hs : Real.sqrt (1 + (y x) ^ 2) ≠ 0 := by positivity
    convert (Real.hasDerivAt_arsinh (y x)).comp x (hy x) using 1
    · rfl
    · field_simp
  have hp (x : ℝ) : HasDerivAt
      (fun t => Real.arsinh initial + primitivePolynomial terms t - primitivePolynomial terms t0)
      (evalPolynomial terms x) x := by
    convert ((hasDerivAt_primitivePolynomial terms x).const_add (Real.arsinh initial)).sub_const
      (primitivePolynomial terms t0) using 1
  have he := eq_of_global_hasDerivAt_eq _ _ (evalPolynomial terms) t0 ht hp (by
    simp only [h0, add_sub_cancel_right])
  funext x
  have hx := congrArg Real.sinh (congrFun he x)
  simpa only [Real.sinh_arsinh, nonlinearPolynomialIVPSolution] using hx

theorem existsUnique_nonlinearPolynomialIVPSolution (terms : List (ℝ × ℕ)) (t0 initial : ℝ) :
    ∃! y : ℝ → ℝ,
      (∀ x, HasDerivAt y (evalPolynomial terms x * Real.sqrt (1 + (y x) ^ 2)) x) ∧ y t0 = initial := by
  refine ⟨nonlinearPolynomialIVPSolution terms t0 initial,
    ⟨hasDerivAt_nonlinearPolynomialIVPSolution terms t0 initial,
      nonlinearPolynomialIVPSolution_initial terms t0 initial⟩, ?_⟩
  intro y hy
  exact nonlinearPolynomialIVPSolution_unique terms t0 initial y hy.1 hy.2

/-- Integrate each polynomial term twice, with both integration constants zero. -/
noncomputable def secondPrimitivePolynomial (terms : List (ℝ × ℕ)) (x : ℝ) : ℝ :=
  primitivePolynomial (terms.map (fun term => (term.1 / ((term.2 + 1 : ℕ) : ℝ), term.2 + 1))) x

private theorem evalPolynomial_primitive_terms (terms : List (ℝ × ℕ)) (x : ℝ) :
    evalPolynomial (terms.map (fun term => (term.1 / ((term.2 + 1 : ℕ) : ℝ), term.2 + 1))) x =
      primitivePolynomial terms x := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      obtain ⟨c, n⟩ := term
      simp only [List.map_cons, evalPolynomial, primitivePolynomial, ih]
      ring

theorem hasDerivAt_secondPrimitivePolynomial (terms : List (ℝ × ℕ)) (x : ℝ) :
    HasDerivAt (secondPrimitivePolynomial terms) (primitivePolynomial terms x) x := by
  unfold secondPrimitivePolynomial
  convert hasDerivAt_primitivePolynomial
    (terms.map (fun term => (term.1 / ((term.2 + 1 : ℕ) : ℝ), term.2 + 1))) x using 1
  exact (evalPolynomial_primitive_terms terms x).symm

/-- Velocity for the polynomial-forced equation `y'' = p(t)`. -/
noncomputable def polynomialSecondOrderVelocity (terms : List (ℝ × ℕ)) (t0 velocity x : ℝ) : ℝ :=
  velocity + primitivePolynomial terms x - primitivePolynomial terms t0

/-- Position for the polynomial-forced equation with arbitrary initial position and velocity. -/
noncomputable def polynomialSecondOrderPosition (terms : List (ℝ × ℕ))
    (t0 initial velocity x : ℝ) : ℝ :=
  initial + velocity * (x - t0) + secondPrimitivePolynomial terms x - secondPrimitivePolynomial terms t0 -
    primitivePolynomial terms t0 * (x - t0)

theorem hasDerivAt_polynomialSecondOrderVelocity (terms : List (ℝ × ℕ)) (t0 velocity x : ℝ) :
    HasDerivAt (polynomialSecondOrderVelocity terms t0 velocity) (evalPolynomial terms x) x := by
  unfold polynomialSecondOrderVelocity
  convert ((hasDerivAt_primitivePolynomial terms x).const_add velocity).sub_const
    (primitivePolynomial terms t0) using 1

theorem hasDerivAt_polynomialSecondOrderPosition (terms : List (ℝ × ℕ))
    (t0 initial velocity x : ℝ) :
    HasDerivAt (polynomialSecondOrderPosition terms t0 initial velocity)
      (polynomialSecondOrderVelocity terms t0 velocity x) x := by
  unfold polynomialSecondOrderPosition polynomialSecondOrderVelocity
  have ht := (hasDerivAt_id x).sub_const t0
  convert ((((ht.const_mul velocity).const_add initial).add
    (hasDerivAt_secondPrimitivePolynomial terms x)).sub_const
    (secondPrimitivePolynomial terms t0)).sub (ht.const_mul (primitivePolynomial terms t0)) using 1
  · rfl
  · ring

@[simp] theorem polynomialSecondOrderVelocity_initial (terms : List (ℝ × ℕ)) (t0 velocity : ℝ) :
    polynomialSecondOrderVelocity terms t0 velocity t0 = velocity := by
  simp only [polynomialSecondOrderVelocity, add_sub_cancel_right]

@[simp] theorem polynomialSecondOrderPosition_initial (terms : List (ℝ × ℕ))
    (t0 initial velocity : ℝ) :
    polynomialSecondOrderPosition terms t0 initial velocity t0 = initial := by
  simp only [polynomialSecondOrderPosition, sub_self, mul_zero, add_zero, sub_zero, add_sub_cancel_right]

/-- The solution class consists of position/velocity pairs satisfying both first-order derivative identities. -/
theorem polynomialSecondOrderSolution_unique (terms : List (ℝ × ℕ)) (t0 initial velocity : ℝ)
    (state : (ℝ → ℝ) × (ℝ → ℝ))
    (hy : ∀ x, HasDerivAt state.1 (state.2 x) x)
    (hv : ∀ x, HasDerivAt state.2 (evalPolynomial terms x) x)
    (hy0 : state.1 t0 = initial) (hv0 : state.2 t0 = velocity) :
    state = (polynomialSecondOrderPosition terms t0 initial velocity,
      polynomialSecondOrderVelocity terms t0 velocity) := by
  have hveq := eq_of_global_hasDerivAt_eq state.2 (polynomialSecondOrderVelocity terms t0 velocity)
    (evalPolynomial terms) t0 hv (hasDerivAt_polynomialSecondOrderVelocity terms t0 velocity)
    (by simpa only [polynomialSecondOrderVelocity_initial] using hv0)
  have hy' (x : ℝ) : HasDerivAt state.1 (polynomialSecondOrderVelocity terms t0 velocity x) x := by
    simpa only [hveq] using hy x
  have hyeq := eq_of_global_hasDerivAt_eq state.1 (polynomialSecondOrderPosition terms t0 initial velocity)
    (polynomialSecondOrderVelocity terms t0 velocity) t0 hy'
    (hasDerivAt_polynomialSecondOrderPosition terms t0 initial velocity)
    (by simpa only [polynomialSecondOrderPosition_initial] using hy0)
  exact Prod.ext hyeq hveq

theorem existsUnique_polynomialSecondOrderSolution (terms : List (ℝ × ℕ)) (t0 initial velocity : ℝ) :
    ∃! state : (ℝ → ℝ) × (ℝ → ℝ),
      (∀ x, HasDerivAt state.1 (state.2 x) x) ∧
      (∀ x, HasDerivAt state.2 (evalPolynomial terms x) x) ∧
      state.1 t0 = initial ∧ state.2 t0 = velocity := by
  refine ⟨(polynomialSecondOrderPosition terms t0 initial velocity,
    polynomialSecondOrderVelocity terms t0 velocity), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hasDerivAt_polynomialSecondOrderPosition terms t0 initial velocity
  · exact hasDerivAt_polynomialSecondOrderVelocity terms t0 velocity
  · exact polynomialSecondOrderPosition_initial terms t0 initial velocity
  · exact polynomialSecondOrderVelocity_initial terms t0 velocity
  · intro state hs
    exact polynomialSecondOrderSolution_unique terms t0 initial velocity state
      hs.1 hs.2.1 hs.2.2.1 hs.2.2.2

end SpecialFunctionProofAgent
