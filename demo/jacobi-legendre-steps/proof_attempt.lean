import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℕ) (v1 : ℝ)  : (SpecialFunctionProofAgent.jacobiP v0 (0 : ℝ) (0 : ℝ) v1) = (SpecialFunctionProofAgent.legendreP v0 v1) := by
  have step_1 : (SpecialFunctionProofAgent.jacobiP v0 (0 : ℝ) (0 : ℝ) v1) = (SpecialFunctionProofAgent.legendreP v0 v1) := by
    convert (SpecialFunctionProofAgent.jacobiP_zero_zero v0 v1) using 1 <;> ((try simp only [neg_mul, Real.rpow_eq_pow, Real.rpow_natCast, Nat.cast_add, Nat.cast_one]) <;> ring)
  exact step_1

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
