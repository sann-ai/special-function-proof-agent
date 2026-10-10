import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℝ) (v1 : ℕ) (v2 : ℝ) (h0 : (v1 : ℝ) ≥ (1 / 1 : ℝ)) : (((v1 : ℝ) + (1 : ℝ)) * (SpecialFunctionProofAgent.laguerreL (v1 + (1 : ℕ)) v0 v2)) = (((((((2 : ℝ) * (v1 : ℝ)) + v0) + (1 : ℝ)) - v2) * (SpecialFunctionProofAgent.laguerreL v1 v0 v2)) - (((v1 : ℝ) + v0) * (SpecialFunctionProofAgent.laguerreL (v1 - (1 : ℕ)) v0 v2))) := by
  have hn_condition_0 : (1 : ℤ) * (v1 : ℤ) ≥ (1 : ℤ) := by
    have hr : (1 : ℝ) * (v1 : ℝ) ≥ (1 : ℝ) := by
      linarith [h0]
    exact_mod_cast hr
  have step_1 : (((v1 : ℝ) + (1 : ℝ)) * (SpecialFunctionProofAgent.laguerreL (v1 + (1 : ℕ)) v0 v2)) = (((((((2 : ℝ) * (v1 : ℝ)) + v0) + (1 : ℝ)) - v2) * (SpecialFunctionProofAgent.laguerreL v1 v0 v2)) - (((v1 : ℝ) + v0) * (SpecialFunctionProofAgent.laguerreL (v1 - (1 : ℕ)) v0 v2))) := by
    convert (SpecialFunctionProofAgent.laguerreL_recurrence v1 v0 v2 (by omega)) using 1 <;> ((try simp only [neg_mul, Real.rpow_eq_pow, Real.rpow_natCast, Nat.cast_add, Nat.cast_one]) <;> ring)
  exact step_1

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
