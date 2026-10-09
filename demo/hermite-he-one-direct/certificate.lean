import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℝ)  : (SpecialFunctionProofAgent.hermiteHe (1 : ℕ) v0) = v0 := by
  convert (SpecialFunctionProofAgent.hermiteHe_one v0) using 1 <;> (simp only [neg_mul, Real.rpow_eq_pow] <;> ring)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
