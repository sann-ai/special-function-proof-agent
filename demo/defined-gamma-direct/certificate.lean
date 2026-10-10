import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

noncomputable def ResearchFunction_70c67638866fbb45129965ce8b08bfd30ffe8c4b4a1ce6a6ec641e2aa98e1580 (p0 : ℝ) : ℝ := (Real.Gamma (p0 + (1 : ℝ)))

theorem expanded_target (v0 : ℝ) (h0 : v0 > (0 / 1 : ℝ)) : (Real.Gamma (v0 + (1 : ℝ))) = (v0 * (Real.Gamma v0)) := by
  simpa only [neg_mul, Real.rpow_eq_pow] using (SpecialFunctionProofAgent.gamma_recurrence v0 (by linarith))

theorem target (v0 : ℝ) (h0 : v0 > (0 / 1 : ℝ)) : (ResearchFunction_70c67638866fbb45129965ce8b08bfd30ffe8c4b4a1ce6a6ec641e2aa98e1580 (v0)) = (v0 * (Real.Gamma v0)) := by
  exact expanded_target v0 h0

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
