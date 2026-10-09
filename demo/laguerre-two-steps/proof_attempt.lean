import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℝ) (v1 : ℝ)  : (SpecialFunctionProofAgent.laguerreL (2 : ℕ) v0 v1) = ((((v1 ^ 2) - (((2 : ℝ) * (v0 + (2 : ℝ))) * v1)) + ((v0 + (1 : ℝ)) * (v0 + (2 : ℝ)))) / (2 : ℝ)) := by
  have step_1 : (SpecialFunctionProofAgent.laguerreL (2 : ℕ) v0 v1) = ((((v1 ^ 2) - (((2 : ℝ) * (v0 + (2 : ℝ))) * v1)) + ((v0 + (1 : ℝ)) * (v0 + (2 : ℝ)))) / (2 : ℝ)) := by
    convert (SpecialFunctionProofAgent.laguerreL_two v0 v1) using 1 <;> ((try simp only [neg_mul, Real.rpow_eq_pow, Real.rpow_natCast, Nat.cast_add, Nat.cast_one]) <;> ring)
  exact step_1

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
