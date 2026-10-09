import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℝ)  : (SpecialFunctionProofAgent.laguerreL (2 : ℕ) (0 : ℝ) v0) = ((((v0 ^ 2) - ((4 : ℝ) * v0)) + (2 : ℝ)) / (2 : ℝ)) := by
  have step_1 : (SpecialFunctionProofAgent.laguerreL (2 : ℕ) (0 : ℝ) v0) = ((((v0 ^ 2) - ((4 : ℝ) * v0)) + (2 : ℝ)) / (2 : ℝ)) := by
    convert (SpecialFunctionProofAgent.laguerreL_two (0 : ℝ) v0) using 1 <;> ((try simp only [neg_mul, Real.rpow_eq_pow, Real.rpow_natCast, Nat.cast_add, Nat.cast_one]) <;> ring)
  exact step_1

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
