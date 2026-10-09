import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : (SpecialFunctionProofAgent.jacobiP (1 : ℕ) v0 v1 v2) = (((v0 - v1) + (((v0 + v1) + (2 : ℝ)) * v2)) / (2 : ℝ)) := by
  convert (SpecialFunctionProofAgent.jacobiP_one v0 v1 v2) using 1 <;> ((try simp only [neg_mul, Real.rpow_eq_pow, Real.rpow_natCast, Nat.cast_add, Nat.cast_one]) <;> ring)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
