import SpecialFunctionProofAgent
import SpecialFunctionProofAgent.AnalyticDefinitions

open scoped Real
open MeasureTheory

namespace ResearchLemma_b282c1d9e15835c110a406007a8f103b1d632a6aac514c7147b82b75854a4498

noncomputable def ResearchFunction_a9cd0c69e62cd05c0dda348d582b8639afb20e9074aeefbce7b704c23da4082b (p0 : ℝ) : ℝ := (SpecialFunctionProofAgent.exponentialSeries (p0))

theorem expanded_target (v0 : ℝ)  : (Real.exp v0) = (Real.exp v0) := by
  ring

theorem target (v0 : ℝ)  : (ResearchFunction_a9cd0c69e62cd05c0dda348d582b8639afb20e9074aeefbce7b704c23da4082b (v0)) = (Real.exp v0) := by
  simpa only [ResearchFunction_a9cd0c69e62cd05c0dda348d582b8639afb20e9074aeefbce7b704c23da4082b, SpecialFunctionProofAgent.exponentialSeries_eq_exp] using (expanded_target v0)

end ResearchLemma_b282c1d9e15835c110a406007a8f103b1d632a6aac514c7147b82b75854a4498

namespace BesselAgentCandidate

noncomputable def ResearchFunction_a9cd0c69e62cd05c0dda348d582b8639afb20e9074aeefbce7b704c23da4082b (p0 : ℝ) : ℝ := (SpecialFunctionProofAgent.exponentialSeries (p0))

theorem expanded_target (v0 : ℝ)  : ((2 : ℝ) * (Real.exp v0)) = ((2 : ℝ) * (Real.exp v0)) := by
  have research_use_1 := (ResearchLemma_b282c1d9e15835c110a406007a8f103b1d632a6aac514c7147b82b75854a4498.expanded_target (v0))
  ring_nf at research_use_1 ⊢ <;> (simp only [research_use_1] <;> ring)

theorem target (v0 : ℝ)  : ((2 : ℝ) * (ResearchFunction_a9cd0c69e62cd05c0dda348d582b8639afb20e9074aeefbce7b704c23da4082b (v0))) = ((2 : ℝ) * (Real.exp v0)) := by
  simpa only [ResearchFunction_a9cd0c69e62cd05c0dda348d582b8639afb20e9074aeefbce7b704c23da4082b, SpecialFunctionProofAgent.exponentialSeries_eq_exp] using (expanded_target v0)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
