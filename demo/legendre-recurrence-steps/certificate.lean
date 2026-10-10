import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℕ) (v1 : ℝ) (h0 : (v0 : ℝ) ≥ (1 / 1 : ℝ)) : (((v0 : ℝ) + (1 : ℝ)) * (SpecialFunctionProofAgent.legendreP (v0 + (1 : ℕ)) v1)) = ((((((2 : ℝ) * (v0 : ℝ)) + (1 : ℝ)) * v1) * (SpecialFunctionProofAgent.legendreP v0 v1)) - ((v0 : ℝ) * (SpecialFunctionProofAgent.legendreP (v0 - (1 : ℕ)) v1))) := by
  have hn_condition_0 : (1 : ℤ) * (v0 : ℤ) ≥ (1 : ℤ) := by
    have hr : (1 : ℝ) * (v0 : ℝ) ≥ (1 : ℝ) := by
      linarith [h0]
    exact_mod_cast hr
  have step_1 : (((v0 : ℝ) + (1 : ℝ)) * (SpecialFunctionProofAgent.legendreP (v0 + (1 : ℕ)) v1)) = ((((((2 : ℝ) * (v0 : ℝ)) + (1 : ℝ)) * v1) * (SpecialFunctionProofAgent.legendreP v0 v1)) - ((v0 : ℝ) * (SpecialFunctionProofAgent.legendreP (v0 - (1 : ℕ)) v1))) := by
    convert (SpecialFunctionProofAgent.legendreP_recurrence v0 v1 (by omega)) using 1 <;> ((try simp only [neg_mul, Real.rpow_eq_pow, Real.rpow_natCast, Nat.cast_add, Nat.cast_one]) <;> ring)
  exact step_1

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
