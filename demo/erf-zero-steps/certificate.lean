import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target   : (SpecialFunctionProofAgent.erf (0 : ℝ)) = (0 : ℝ) := by
  have step_1 : (SpecialFunctionProofAgent.erf (0 : ℝ)) = (0 : ℝ) := by
    convert (SpecialFunctionProofAgent.erf_zero) using 1 <;> (simp only [neg_mul, Real.rpow_eq_pow] <;> ring)
  exact step_1

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
