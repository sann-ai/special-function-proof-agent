import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℝ)  : (deriv (fun (d1 : ℝ) => (SpecialFunctionProofAgent.erf d1)) v0) = (((2 : ℝ) / (Real.sqrt Real.pi)) * (Real.exp (-(v0 ^ 2)))) := by
  convert (SpecialFunctionProofAgent.deriv_erf v0) using 1 <;> (simp only [neg_mul, Real.rpow_eq_pow] <;> ring)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
