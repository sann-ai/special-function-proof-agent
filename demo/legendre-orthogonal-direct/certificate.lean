import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℕ) (v1 : ℕ) (h0 : v0 ≠ v1) : (∫ b2 in (-1 : ℝ)..(1 : ℝ), ((SpecialFunctionProofAgent.legendreP v0 b2) * (SpecialFunctionProofAgent.legendreP v1 b2))) = (0 : ℝ) := by
  convert (SpecialFunctionProofAgent.legendreP_orthogonal v0 v1 (by omega)) using 1 <;> ((try simp only [neg_mul, Real.rpow_eq_pow, Real.rpow_natCast, Nat.cast_add, Nat.cast_one]) <;> ring)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
