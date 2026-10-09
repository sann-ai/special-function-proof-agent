import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℝ) (v1 : ℝ)  : (∫ b2 in v0..v1, (Real.exp (-(b2 ^ 2)))) = (((Real.sqrt Real.pi) / (2 : ℝ)) * ((SpecialFunctionProofAgent.erf v1) - (SpecialFunctionProofAgent.erf v0))) := by
  convert (SpecialFunctionProofAgent.gaussian_integral v0 v1) using 1 <;> (simp only [neg_mul, Real.rpow_eq_pow] <;> ring)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
