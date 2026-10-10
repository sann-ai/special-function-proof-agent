import SpecialFunctionProofAgent
import SpecialFunctionProofAgent.AnalyticDefinitions

open scoped Real
open MeasureTheory

namespace ResearchLemma_7efdc31b4b5674f4bba661d90ae2fdb0392f371b938331c88fec503789132b2b

noncomputable def ResearchFunction_66b143907cd9432ec06146f8a839686dc1f8461d20b6022565509dbdb5a86fe0 (p0 : ℝ) (p1 : ℝ) (p2 : ℝ) : ℝ := (SpecialFunctionProofAgent.homogeneousIVPSolution (p0) (p1) (p2))

theorem expanded_target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : (v1 * (Real.exp (v0 * v2))) = (v1 * (Real.exp (v0 * v2))) := by
  ring

theorem target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : (ResearchFunction_66b143907cd9432ec06146f8a839686dc1f8461d20b6022565509dbdb5a86fe0 (v0) (v1) (v2)) = (v1 * (Real.exp (v0 * v2))) := by
  simpa only [ResearchFunction_66b143907cd9432ec06146f8a839686dc1f8461d20b6022565509dbdb5a86fe0, SpecialFunctionProofAgent.homogeneousIVPSolution_eq_exp] using (expanded_target v0 v1 v2)

end ResearchLemma_7efdc31b4b5674f4bba661d90ae2fdb0392f371b938331c88fec503789132b2b

namespace BesselAgentCandidate

noncomputable def ResearchFunction_66b143907cd9432ec06146f8a839686dc1f8461d20b6022565509dbdb5a86fe0 (p0 : ℝ) (p1 : ℝ) (p2 : ℝ) : ℝ := (SpecialFunctionProofAgent.homogeneousIVPSolution (p0) (p1) (p2))

theorem expanded_target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : ((2 : ℝ) * (v1 * (Real.exp (v0 * v2)))) = ((2 : ℝ) * (v1 * (Real.exp (v0 * v2)))) := by
  have step_1 : ((2 : ℝ) * (v1 * (Real.exp (v0 * v2)))) = ((2 : ℝ) * (v1 * (Real.exp (v0 * v2)))) := by
    have research_use_1 := (ResearchLemma_7efdc31b4b5674f4bba661d90ae2fdb0392f371b938331c88fec503789132b2b.expanded_target (v0) (v1) (v2))
    ring_nf at research_use_1 ⊢ <;> (simp only [research_use_1] <;> ring)
  exact step_1

theorem target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : ((2 : ℝ) * (ResearchFunction_66b143907cd9432ec06146f8a839686dc1f8461d20b6022565509dbdb5a86fe0 (v0) (v1) (v2))) = ((2 : ℝ) * (v1 * (Real.exp (v0 * v2)))) := by
  simpa only [ResearchFunction_66b143907cd9432ec06146f8a839686dc1f8461d20b6022565509dbdb5a86fe0, SpecialFunctionProofAgent.homogeneousIVPSolution_eq_exp] using (expanded_target v0 v1 v2)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
