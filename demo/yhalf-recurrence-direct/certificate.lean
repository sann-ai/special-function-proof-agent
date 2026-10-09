import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℝ) (h0 : v0 > (0 / 1 : ℝ)) : ((SpecialFunctionProofAgent.besselYNoninteger (-1 / 2 : ℝ) v0) + (SpecialFunctionProofAgent.besselYNoninteger (3 / 2 : ℝ) v0)) = ((SpecialFunctionProofAgent.besselYNoninteger (1 / 2 : ℝ) v0) / v0) := by
  convert (SpecialFunctionProofAgent.Yhalf_recurrence v0 (by linarith)) using 1 <;> norm_num <;> ring

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
