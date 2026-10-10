import SpecialFunctionProofAgent
import SpecialFunctionProofAgent.AnalyticDefinitions

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

noncomputable def ResearchFunction_81a34d239981e263eea547af58facdda907c950fc76bd9a9a620432e614d31eb (p0 : ℝ) : ℝ := (SpecialFunctionProofAgent.gaussianPrimitive (p0))

theorem expanded_target (v0 : ℝ)  : (((Real.sqrt Real.pi) / (2 : ℝ)) * (SpecialFunctionProofAgent.erf v0)) = (((Real.sqrt Real.pi) / (2 : ℝ)) * (SpecialFunctionProofAgent.erf v0)) := by
  ring

theorem target (v0 : ℝ)  : (ResearchFunction_81a34d239981e263eea547af58facdda907c950fc76bd9a9a620432e614d31eb (v0)) = (((Real.sqrt Real.pi) / (2 : ℝ)) * (SpecialFunctionProofAgent.erf v0)) := by
  simpa only [ResearchFunction_81a34d239981e263eea547af58facdda907c950fc76bd9a9a620432e614d31eb, SpecialFunctionProofAgent.gaussianPrimitive_eq_erf] using (expanded_target v0)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
