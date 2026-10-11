import SpecialFunctionProofAgent.AnalyticDefinitions
import Mathlib.Analysis.Calculus.Deriv.Pow

open MeasureTheory

namespace SpecialFunctionProofAgent

/-- A sparse real polynomial: each pair records a coefficient and a natural degree. -/
noncomputable def evalPolynomial : List (ℝ × ℕ) → ℝ → ℝ
  | [], _ => 0
  | (c, n) :: terms, x => c * x ^ n + evalPolynomial terms x

/-- The termwise polynomial primitive, with value zero at the origin. -/
noncomputable def primitivePolynomial : List (ℝ × ℕ) → ℝ → ℝ
  | [], _ => 0
  | (c, n) :: terms, x => c * x ^ (n + 1) / ((n + 1 : ℕ) : ℝ) +
      primitivePolynomial terms x

/-- Termwise integration differentiates to the original sparse polynomial everywhere. -/
theorem hasDerivAt_primitivePolynomial (terms : List (ℝ × ℕ)) (x : ℝ) :
    HasDerivAt (primitivePolynomial terms) (evalPolynomial terms x) x := by
  induction terms with
  | nil => simpa only [primitivePolynomial, evalPolynomial] using hasDerivAt_const x (0 : ℝ)
  | cons term terms ih =>
      obtain ⟨c, n⟩ := term
      have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hm : HasDerivAt (fun t : ℝ => c * t ^ (n + 1) / ((n + 1 : ℕ) : ℝ))
          (c * x ^ n) x := by
        convert ((hasDerivAt_pow (n + 1) x).const_mul c).div_const
          (((n + 1 : ℕ) : ℝ)) using 1
        simp only [Nat.add_sub_cancel]
        field_simp
      convert hm.add ih using 1 <;> rfl

/-- Every sparse real polynomial is continuous on the full real line. -/
theorem continuous_evalPolynomial (terms : List (ℝ × ℕ)) :
    Continuous (evalPolynomial terms) := by
  induction terms with
  | nil => exact continuous_const
  | cons term terms ih =>
      obtain ⟨c, n⟩ := term
      exact (continuous_const.mul (continuous_id.pow n)).add ih

/-- Polynomial integration is defined on every oriented finite real interval. -/
theorem intervalIntegrable_evalPolynomial (terms : List (ℝ × ℕ)) (a b : ℝ) :
    IntervalIntegrable (evalPolynomial terms) volume a b :=
  (continuous_evalPolynomial terms).intervalIntegrable a b

/-- The actual oriented integral of the sparse polynomial. -/
noncomputable def polynomialIntegral (terms : List (ℝ × ℕ)) (a b : ℝ) : ℝ :=
  ∫ t in a..b, evalPolynomial terms t

/-- The fundamental theorem of calculus evaluates the integral in either orientation. -/
theorem polynomialIntegral_eq_primitive_sub (terms : List (ℝ × ℕ)) (a b : ℝ) :
    polynomialIntegral terms a b = primitivePolynomial terms b - primitivePolynomial terms a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_primitivePolynomial terms x)
    (intervalIntegrable_evalPolynomial terms a b)

/-- The global solution for the polynomial coefficient and an arbitrary real initial time. -/
noncomputable def polynomialIVPSolution (terms : List (ℝ × ℕ)) (t0 initial x : ℝ) : ℝ :=
  initial * Real.exp (primitivePolynomial terms x - primitivePolynomial terms t0)

/-- The explicit expression used by the polynomial-coefficient IVP solution. -/
theorem polynomialIVPSolution_eq_exp (terms : List (ℝ × ℕ)) (t0 initial x : ℝ) :
    polynomialIVPSolution terms t0 initial x =
      initial * Real.exp (primitivePolynomial terms x - primitivePolynomial terms t0) := rfl

/-- The explicit solution satisfies the polynomial-coefficient ODE at every real time. -/
theorem hasDerivAt_polynomialIVPSolution (terms : List (ℝ × ℕ)) (t0 initial x : ℝ) :
    HasDerivAt (polynomialIVPSolution terms t0 initial)
      (evalPolynomial terms x * polynomialIVPSolution terms t0 initial x) x := by
  unfold polynomialIVPSolution
  convert (((hasDerivAt_primitivePolynomial terms x).sub_const
    (primitivePolynomial terms t0)).exp.const_mul initial) using 1
  ring

/-- The solution attains its specified value at the specified real initial time. -/
@[simp] theorem polynomialIVPSolution_initial (terms : List (ℝ × ℕ)) (t0 initial : ℝ) :
    polynomialIVPSolution terms t0 initial t0 = initial := by
  simp only [polynomialIVPSolution, sub_self, Real.exp_zero, mul_one]

/-- Any global solution of this ODE and initial condition equals the explicit solution. -/
theorem polynomialIVPSolution_unique (terms : List (ℝ × ℕ)) (t0 initial : ℝ)
    (y : ℝ → ℝ) (hy : ∀ x, HasDerivAt y (evalPolynomial terms x * y x) x)
    (h0 : y t0 = initial) : y = polynomialIVPSolution terms t0 initial := by
  have hfactor (x : ℝ) :
      HasDerivAt (fun t => y t * Real.exp (-primitivePolynomial terms t)) 0 x := by
    convert (hy x).mul ((hasDerivAt_primitivePolynomial terms x).neg.exp) using 1
    ring
  have hconst (x : ℝ) :
      y x * Real.exp (-primitivePolynomial terms x) =
        initial * Real.exp (-primitivePolynomial terms t0) := by
    have hc := is_const_of_deriv_eq_zero
      (fun t => (hfactor t).differentiableAt) (fun t => (hfactor t).deriv) x t0
    simpa only [h0] using hc
  funext x
  have hx := congrArg (fun value : ℝ => value * Real.exp (primitivePolynomial terms x)) (hconst x)
  simpa only [mul_assoc, ← Real.exp_add, neg_add_cancel, add_neg_cancel, Real.exp_zero, mul_one,
    polynomialIVPSolution, sub_eq_add_neg, add_comm] using hx

/-- At every real initial time this polynomial-coefficient global IVP has exactly one solution. -/
theorem existsUnique_polynomialIVPSolution (terms : List (ℝ × ℕ)) (t0 initial : ℝ) :
    ∃! y : ℝ → ℝ, (∀ x, HasDerivAt y (evalPolynomial terms x * y x) x) ∧ y t0 = initial := by
  refine ⟨polynomialIVPSolution terms t0 initial,
    ⟨hasDerivAt_polynomialIVPSolution terms t0 initial,
      polynomialIVPSolution_initial terms t0 initial⟩, ?_⟩
  intro y hy
  exact polynomialIVPSolution_unique terms t0 initial y hy.1 hy.2

/-- The finite exponential combination paired with factorial power-series kernels. -/
noncomputable def finiteExponentialCombination (terms : List (ℝ × ℝ)) : ℝ :=
  (terms.map (fun term => term.1 * Real.exp term.2)).sum

/-- The actual infinite sum of the finite combination of factorial kernels. -/
noncomputable def factorialCombination (terms : List (ℝ × ℝ)) : ℝ :=
  ∑' n : ℕ, (terms.map (fun term => term.1 * (term.2 ^ n / (n.factorial : ℝ)))).sum

/-- Every finite real combination of factorial kernels has the stated exponential sum. -/
theorem hasSum_factorialCombination (terms : List (ℝ × ℝ)) :
    HasSum (fun n : ℕ => (terms.map
      (fun term => term.1 * (term.2 ^ n / (n.factorial : ℝ)))).sum)
      (finiteExponentialCombination terms) := by
  induction terms with
  | nil => simpa only [List.map_nil, List.sum_nil, finiteExponentialCombination] using
      (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  | cons term terms ih =>
      simpa only [List.map_cons, List.sum_cons, finiteExponentialCombination] using
        ((hasSum_exponentialSeries term.2).mul_left term.1).add ih

/-- The defining infinite sum converges for every finite real combination. -/
theorem summable_factorialCombination (terms : List (ℝ × ℝ)) :
    Summable (fun n : ℕ => (terms.map
      (fun term => term.1 * (term.2 ^ n / (n.factorial : ℝ)))).sum) :=
  (hasSum_factorialCombination terms).summable

/-- The convergent infinite combination agrees with its finite exponential expression. -/
theorem factorialCombination_eq_finiteExponentialCombination (terms : List (ℝ × ℝ)) :
    factorialCombination terms = finiteExponentialCombination terms :=
  (hasSum_factorialCombination terms).tsum_eq

end SpecialFunctionProofAgent
