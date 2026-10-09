import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℝ) (v1 : ℝ) (h0 : v0 > (0 / 1 : ℝ)) (h1 : v1 > (0 / 1 : ℝ)) : (∫ b2 in Set.Ioi (0 : ℝ), (Real.rpow b2 (v0 - (1 : ℝ)) * (Real.exp ((-v1) * b2)))) = (Real.rpow v1 (-v0) * (Real.Gamma v0)) := by
  have step_1 : (∫ b2 in Set.Ioi (0 : ℝ), (Real.rpow b2 (v0 - (1 : ℝ)) * (Real.exp ((-v1) * b2)))) = (Real.rpow v1 (-v0) * (Real.Gamma v0)) := by
    simpa only [neg_mul, Real.rpow_eq_pow] using (SpecialFunctionProofAgent.gamma_scaled_integral v0 v1 (by linarith) (by linarith))
  exact step_1

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
