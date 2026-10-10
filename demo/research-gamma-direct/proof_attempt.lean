import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace ResearchLemma_b2d6b64014f068f0def5d3915656e24a4e87278f5830181a4acf8985bd689421

theorem target (v0 : ℝ) (h0 : v0 > (0 / 1 : ℝ)) : (Real.Gamma (v0 + (1 : ℝ))) = (v0 * (Real.Gamma v0)) := by
  simpa only [neg_mul, Real.rpow_eq_pow] using (SpecialFunctionProofAgent.gamma_recurrence v0 (by linarith))

end ResearchLemma_b2d6b64014f068f0def5d3915656e24a4e87278f5830181a4acf8985bd689421

namespace BesselAgentCandidate

theorem target (v0 : ℝ) (h0 : v0 > (0 / 1 : ℝ)) : (Real.Gamma (v0 + (2 : ℝ))) = (((v0 + (1 : ℝ)) * v0) * (Real.Gamma v0)) := by
  have research_use_1 := (ResearchLemma_b2d6b64014f068f0def5d3915656e24a4e87278f5830181a4acf8985bd689421.target ((v0 + (1 : ℝ))) (by nlinarith))
  have research_use_2 := (ResearchLemma_b2d6b64014f068f0def5d3915656e24a4e87278f5830181a4acf8985bd689421.target (v0) (by nlinarith))
  ring_nf at research_use_1 research_use_2 ⊢ <;> (simp only [research_use_1, research_use_2] <;> ring)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
