import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℝ) (v1 : ℝ) (v2 : ℕ) (v3 : ℝ) (h0 : (v2 : ℝ) ≥ (1 / 1 : ℝ)) : (deriv (fun (d4 : ℝ) => (SpecialFunctionProofAgent.jacobiP v2 v0 v1 d4)) v3) = ((((((v2 : ℝ) + v0) + v1) + (1 : ℝ)) / (2 : ℝ)) * (SpecialFunctionProofAgent.jacobiP (v2 - (1 : ℕ)) (v0 + (1 : ℝ)) (v1 + (1 : ℝ)) v3)) := by
  have hn_condition_0 : (1 : ℤ) * (v2 : ℤ) ≥ (1 : ℤ) := by
    have hr : (1 : ℝ) * (v2 : ℝ) ≥ (1 : ℝ) := by
      linarith [h0]
    exact_mod_cast hr
  have step_1 : (deriv (fun (d4 : ℝ) => (SpecialFunctionProofAgent.jacobiP v2 v0 v1 d4)) v3) = ((((((v2 : ℝ) + v0) + v1) + (1 : ℝ)) / (2 : ℝ)) * (SpecialFunctionProofAgent.jacobiP (v2 - (1 : ℕ)) (v0 + (1 : ℝ)) (v1 + (1 : ℝ)) v3)) := by
    convert (SpecialFunctionProofAgent.jacobiP_derivative v2 v0 v1 v3 (by omega)) using 1 <;> ((try simp only [neg_mul, Real.rpow_eq_pow, Real.rpow_natCast, Nat.cast_add, Nat.cast_one]) <;> ring)
  exact step_1

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
