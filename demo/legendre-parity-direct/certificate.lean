import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℕ) (v1 : ℝ)  : (SpecialFunctionProofAgent.legendreP v0 (-v1)) = (Real.rpow (-1 : ℝ) (v0 : ℝ) * (SpecialFunctionProofAgent.legendreP v0 v1)) := by
  convert (SpecialFunctionProofAgent.legendreP_neg v0 v1) using 1 <;> ((try simp only [neg_mul, Real.rpow_eq_pow, Real.rpow_natCast, Nat.cast_add, Nat.cast_one]) <;> ring)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
