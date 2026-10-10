import SpecialFunctionProofAgent.BesselYInteger

namespace BesselAgentCandidate

theorem target (n : ℤ) (x : ℝ) (hx : 0 < x)
    (h0 : DifferentiableAt ℝ (fun a : ℝ => SpecialFunctionProofAgent.realBesselJ a x) 0)
    (h1 : DifferentiableAt ℝ (fun a : ℝ => SpecialFunctionProofAgent.realBesselJ a x) 1) :
    SpecialFunctionProofAgent.besselYInt (n - 1) x + SpecialFunctionProofAgent.besselYInt (n + 1) x = (2 * (n : ℝ) / x) * SpecialFunctionProofAgent.besselYInt n x := by
  exact SpecialFunctionProofAgent.besselYInt_recurrence_of_order_differentiable_zero_one n x hx h0 h1

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
