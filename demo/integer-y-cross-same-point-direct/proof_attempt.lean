import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℝ) (h0 : v0 > (0 / 1 : ℝ)) : ((SpecialFunctionProofAgent.realBesselJ (0 : ℝ) v0) * (SpecialFunctionProofAgent.besselYInt (1 : ℤ) v0) - (SpecialFunctionProofAgent.besselYInt (0 : ℤ) v0) * (SpecialFunctionProofAgent.realBesselJ (1 : ℝ) v0)) = ((-2 : ℝ) / (Real.pi * v0)) := by
  convert (SpecialFunctionProofAgent.besselYInt_cross_zero_one v0 (by linarith)) using 1 <;> norm_num <;> ring

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
