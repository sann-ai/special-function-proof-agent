import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℝ)  : (SpecialFunctionProofAgent.erf (-v0)) = (-(SpecialFunctionProofAgent.erf v0)) := by
  have step_1 : (SpecialFunctionProofAgent.erf (-v0)) = (-(SpecialFunctionProofAgent.erf v0)) := by
    convert (SpecialFunctionProofAgent.erf_neg v0) using 1 <;> (simp only [neg_mul, Real.rpow_eq_pow] <;> ring)
  exact step_1

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
