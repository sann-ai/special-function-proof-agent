import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℝ)  : (SpecialFunctionProofAgent.hermiteH (0 : ℕ) v0) = (1 : ℝ) := by
  convert (SpecialFunctionProofAgent.hermiteH_zero v0) using 1 <;> (simp only [neg_mul, Real.rpow_eq_pow] <;> ring)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
