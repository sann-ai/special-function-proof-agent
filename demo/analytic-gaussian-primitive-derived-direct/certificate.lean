import SpecialFunctionProofAgent
import SpecialFunctionProofAgent.AnalyticDefinitions

open scoped Real
open MeasureTheory

namespace ResearchLemma_f57a2d4868ffb0b676d09f7e4c7c04b413ccfcaa431c7993ab5b624a5a0d8b50

noncomputable def ResearchFunction_81a34d239981e263eea547af58facdda907c950fc76bd9a9a620432e614d31eb (p0 : ℝ) : ℝ := (SpecialFunctionProofAgent.gaussianPrimitive (p0))

theorem expanded_target (v0 : ℝ)  : (((Real.sqrt Real.pi) / (2 : ℝ)) * (SpecialFunctionProofAgent.erf v0)) = (((Real.sqrt Real.pi) / (2 : ℝ)) * (SpecialFunctionProofAgent.erf v0)) := by
  have step_1 : (((Real.sqrt Real.pi) / (2 : ℝ)) * (SpecialFunctionProofAgent.erf v0)) = (((Real.sqrt Real.pi) / (2 : ℝ)) * (SpecialFunctionProofAgent.erf v0)) := by
    ring
  exact step_1

theorem target (v0 : ℝ)  : (ResearchFunction_81a34d239981e263eea547af58facdda907c950fc76bd9a9a620432e614d31eb (v0)) = (((Real.sqrt Real.pi) / (2 : ℝ)) * (SpecialFunctionProofAgent.erf v0)) := by
  simpa only [ResearchFunction_81a34d239981e263eea547af58facdda907c950fc76bd9a9a620432e614d31eb, SpecialFunctionProofAgent.gaussianPrimitive_eq_erf] using (expanded_target v0)

end ResearchLemma_f57a2d4868ffb0b676d09f7e4c7c04b413ccfcaa431c7993ab5b624a5a0d8b50

namespace BesselAgentCandidate

noncomputable def ResearchFunction_81a34d239981e263eea547af58facdda907c950fc76bd9a9a620432e614d31eb (p0 : ℝ) : ℝ := (SpecialFunctionProofAgent.gaussianPrimitive (p0))

theorem expanded_target (v0 : ℝ)  : ((2 : ℝ) * (((Real.sqrt Real.pi) / (2 : ℝ)) * (SpecialFunctionProofAgent.erf v0))) = ((2 : ℝ) * (((Real.sqrt Real.pi) / (2 : ℝ)) * (SpecialFunctionProofAgent.erf v0))) := by
  have research_use_1 := (ResearchLemma_f57a2d4868ffb0b676d09f7e4c7c04b413ccfcaa431c7993ab5b624a5a0d8b50.expanded_target (v0))
  ring_nf at research_use_1 ⊢ <;> (simp only [research_use_1] <;> ring)

theorem target (v0 : ℝ)  : ((2 : ℝ) * (ResearchFunction_81a34d239981e263eea547af58facdda907c950fc76bd9a9a620432e614d31eb (v0))) = ((2 : ℝ) * (((Real.sqrt Real.pi) / (2 : ℝ)) * (SpecialFunctionProofAgent.erf v0))) := by
  simpa only [ResearchFunction_81a34d239981e263eea547af58facdda907c950fc76bd9a9a620432e614d31eb, SpecialFunctionProofAgent.gaussianPrimitive_eq_erf] using (expanded_target v0)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
