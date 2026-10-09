import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : (SpecialFunctionProofAgent.jacobiP (2 : ℕ) v0 v1 v2) = (((((v0 + (1 : ℝ)) * (v0 + (2 : ℝ))) / (2 : ℝ)) + ((((v0 + v1) + (3 : ℝ)) * (v0 + (2 : ℝ))) * ((v2 - (1 : ℝ)) / (2 : ℝ)))) + (((((v0 + v1) + (3 : ℝ)) * ((v0 + v1) + (4 : ℝ))) / (2 : ℝ)) * (((v2 - (1 : ℝ)) / (2 : ℝ)) ^ 2))) := by
  have step_1 : (SpecialFunctionProofAgent.jacobiP (2 : ℕ) v0 v1 v2) = (((((v0 + (1 : ℝ)) * (v0 + (2 : ℝ))) / (2 : ℝ)) + ((((v0 + v1) + (3 : ℝ)) * (v0 + (2 : ℝ))) * ((v2 - (1 : ℝ)) / (2 : ℝ)))) + (((((v0 + v1) + (3 : ℝ)) * ((v0 + v1) + (4 : ℝ))) / (2 : ℝ)) * (((v2 - (1 : ℝ)) / (2 : ℝ)) ^ 2))) := by
    convert (SpecialFunctionProofAgent.jacobiP_two v0 v1 v2) using 1 <;> ((try simp only [neg_mul, Real.rpow_eq_pow, Real.rpow_natCast, Nat.cast_add, Nat.cast_one]) <;> ring)
  exact step_1

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
