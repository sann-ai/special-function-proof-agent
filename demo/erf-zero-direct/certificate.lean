import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target   : (SpecialFunctionProofAgent.erf (0 : ℝ)) = (0 : ℝ) := by
  convert (SpecialFunctionProofAgent.erf_zero) using 1 <;> (simp only [neg_mul, Real.rpow_eq_pow] <;> ring)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
