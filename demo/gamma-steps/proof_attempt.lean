import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℝ) (h0 : v0 > (0 / 1 : ℝ)) : (Real.Gamma (v0 + (1 : ℝ))) = (v0 * (Real.Gamma v0)) := by
  have step_1 : (Real.Gamma (v0 + (1 : ℝ))) = (v0 * (Real.Gamma v0)) := by
    simpa only [neg_mul, Real.rpow_eq_pow] using (SpecialFunctionProofAgent.gamma_recurrence v0 (by linarith))
  exact step_1

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
