import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℝ) (h0 : v0 > (0 / 1 : ℝ)) : (deriv (fun (d1 : ℝ) => (SpecialFunctionProofAgent.besselYNoninteger (1 / 2 : ℝ) d1)) v0) = (((SpecialFunctionProofAgent.besselYNoninteger (-1 / 2 : ℝ) v0) - (SpecialFunctionProofAgent.besselYNoninteger (3 / 2 : ℝ) v0)) / (2 : ℝ)) := by
  have step_1 : (deriv (fun (d1 : ℝ) => (SpecialFunctionProofAgent.besselYNoninteger (1 / 2 : ℝ) d1)) v0) = (((SpecialFunctionProofAgent.besselYNoninteger (-1 / 2 : ℝ) v0) - (SpecialFunctionProofAgent.besselYNoninteger (3 / 2 : ℝ) v0)) / (2 : ℝ)) := by
    convert (SpecialFunctionProofAgent.Yhalf_derivative v0 (by linarith)) using 1 <;> norm_num <;> ring
  exact step_1

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
