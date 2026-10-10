import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℕ)  : (∫ b1 in (-1 : ℝ)..(1 : ℝ), ((SpecialFunctionProofAgent.legendreP v0 b1) ^ 2)) = ((2 : ℝ) / (((2 : ℝ) * (v0 : ℝ)) + (1 : ℝ))) := by
  convert (SpecialFunctionProofAgent.legendreP_norm v0) using 1 <;> ((try simp only [neg_mul, Real.rpow_eq_pow, Real.rpow_natCast, Nat.cast_add, Nat.cast_one]) <;> ring)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
