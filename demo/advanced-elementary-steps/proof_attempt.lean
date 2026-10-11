import SpecialFunctionProofAgent
import SpecialFunctionProofAgent.AdvancedAnalyticDefinitions

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem ResearchAdvanced_c49593e9c96b7619457e349bd6f8c59aafe6c3deb0c81a59dc0c2732e888d391_contract (u0 : ℝ) (u1 : ℝ) (u2 : ℝ) : IntervalIntegrable (fun at0 : ℝ => (((Real.exp (((2 : ℝ) * at0) + u2)) + ((3 : ℝ) * (Real.sin (at0 - u2)))) + (Real.cos u2))) volume (u0) (u1) := by
  have ha0 (at0 : ℝ) : (at0 - u2) = ((1 : ℝ))*at0+((-u2)) := by ring
  have hu0_sin (at0 : ℝ) : Real.sin ((at0 - u2)) = Real.sin (((1 : ℝ))*at0+((-u2))) := congrArg Real.sin (ha0 at0)
  have ha1 (at0 : ℝ) : (((2 : ℝ) * at0) + u2) = ((2 : ℝ))*at0+(u2) := by ring
  have hu1_exp (at0 : ℝ) : Real.exp ((((2 : ℝ) * at0) + u2)) = Real.exp (((2 : ℝ))*at0+(u2)) := congrArg Real.exp (ha1 at0)
  have ha2 (at0 : ℝ) : u2 = ((0 : ℝ))*at0+(u2) := by ring
  have hu2_cos (at0 : ℝ) : Real.cos (u2) = Real.cos (((0 : ℝ))*at0+(u2)) := congrArg Real.cos (ha2 at0)
  have hfun : (fun at0 : ℝ => (((Real.exp (((2 : ℝ) * at0) + u2)) + ((3 : ℝ) * (Real.sin (at0 - u2)))) + (Real.cos u2))) = SpecialFunctionProofAgent.elementaryCombination ([((1 : ℝ), (2 : ℝ), u2)] : List (ℝ × ℝ × ℝ)) ([((3 : ℝ), (1 : ℝ), (-u2))] : List (ℝ × ℝ × ℝ)) ([((1 : ℝ), (0 : ℝ), u2)] : List (ℝ × ℝ × ℝ)) := by
    funext at0
    try simp only [hu0_sin at0, hu1_exp at0, hu2_cos at0]
    simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, SpecialFunctionProofAgent.elementaryCombination] <;> ring
  rw [hfun]
  exact SpecialFunctionProofAgent.intervalIntegrable_elementaryCombination ([((1 : ℝ), (2 : ℝ), u2)] : List (ℝ × ℝ × ℝ)) ([((3 : ℝ), (1 : ℝ), (-u2))] : List (ℝ × ℝ × ℝ)) ([((1 : ℝ), (0 : ℝ), u2)] : List (ℝ × ℝ × ℝ)) (u0) (u1)

theorem ResearchAdvanced_c49593e9c96b7619457e349bd6f8c59aafe6c3deb0c81a59dc0c2732e888d391_bridge (u0 : ℝ) (u1 : ℝ) (u2 : ℝ) : (∫ at0 in u0..u1, (((Real.exp (((2 : ℝ) * at0) + u2)) + ((3 : ℝ) * (Real.sin (at0 - u2)))) + (Real.cos u2))) = (((((1 : ℝ) * ((Real.exp (((2 : ℝ) * u1) + u2)) / (2 : ℝ))) + ((3 : ℝ) * ((-(Real.cos (((1 : ℝ) * u1) + (-u2)))) / (1 : ℝ)))) + ((1 : ℝ) * (u1 * (Real.cos u2)))) - ((((1 : ℝ) * ((Real.exp (((2 : ℝ) * u0) + u2)) / (2 : ℝ))) + ((3 : ℝ) * ((-(Real.cos (((1 : ℝ) * u0) + (-u2)))) / (1 : ℝ)))) + ((1 : ℝ) * (u0 * (Real.cos u2))))) := by
  have ha0 (at0 : ℝ) : (at0 - u2) = ((1 : ℝ))*at0+((-u2)) := by ring
  have hu0_sin (at0 : ℝ) : Real.sin ((at0 - u2)) = Real.sin (((1 : ℝ))*at0+((-u2))) := congrArg Real.sin (ha0 at0)
  have ha1 (at0 : ℝ) : (((2 : ℝ) * at0) + u2) = ((2 : ℝ))*at0+(u2) := by ring
  have hu1_exp (at0 : ℝ) : Real.exp ((((2 : ℝ) * at0) + u2)) = Real.exp (((2 : ℝ))*at0+(u2)) := congrArg Real.exp (ha1 at0)
  have ha2 (at0 : ℝ) : u2 = ((0 : ℝ))*at0+(u2) := by ring
  have hu2_cos (at0 : ℝ) : Real.cos (u2) = Real.cos (((0 : ℝ))*at0+(u2)) := congrArg Real.cos (ha2 at0)
  have hfun : (fun at0 : ℝ => (((Real.exp (((2 : ℝ) * at0) + u2)) + ((3 : ℝ) * (Real.sin (at0 - u2)))) + (Real.cos u2))) = SpecialFunctionProofAgent.elementaryCombination ([((1 : ℝ), (2 : ℝ), u2)] : List (ℝ × ℝ × ℝ)) ([((3 : ℝ), (1 : ℝ), (-u2))] : List (ℝ × ℝ × ℝ)) ([((1 : ℝ), (0 : ℝ), u2)] : List (ℝ × ℝ × ℝ)) := by
    funext at0
    try simp only [hu0_sin at0, hu1_exp at0, hu2_cos at0]
    simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, SpecialFunctionProofAgent.elementaryCombination] <;> ring
  change (∫ at0 in (u0)..(u1), (fun at0 : ℝ => (((Real.exp (((2 : ℝ) * at0) + u2)) + ((3 : ℝ) * (Real.sin (at0 - u2)))) + (Real.cos u2))) at0) = _
  rw [hfun]
  change SpecialFunctionProofAgent.elementaryIntegral ([((1 : ℝ), (2 : ℝ), u2)] : List (ℝ × ℝ × ℝ)) ([((3 : ℝ), (1 : ℝ), (-u2))] : List (ℝ × ℝ × ℝ)) ([((1 : ℝ), (0 : ℝ), u2)] : List (ℝ × ℝ × ℝ)) (u0) (u1) = _
  rw [SpecialFunctionProofAgent.elementaryIntegral_eq_primitive_sub]
  norm_num [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, SpecialFunctionProofAgent.elementaryPrimitive, SpecialFunctionProofAgent.affineExpPrimitive, SpecialFunctionProofAgent.affineSinPrimitive, SpecialFunctionProofAgent.affineCosPrimitive] <;> ring


noncomputable def ResearchFunction_b986f1978247a78cfdf0803337f4e332fb93b4eae06cd70bf83ff162e372a61b (p0 : ℝ) (p1 : ℝ) (p2 : ℝ) : ℝ := (∫ at0 in p0..p1, (((Real.exp (((2 : ℝ) * at0) + p2)) + ((3 : ℝ) * (Real.sin (at0 - p2)))) + (Real.cos p2)))

theorem expanded_target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : (((((1 : ℝ) * ((Real.exp (((2 : ℝ) * v1) + v2)) / (2 : ℝ))) + ((3 : ℝ) * ((-(Real.cos (((1 : ℝ) * v1) + (-v2)))) / (1 : ℝ)))) + ((1 : ℝ) * (v1 * (Real.cos v2)))) - ((((1 : ℝ) * ((Real.exp (((2 : ℝ) * v0) + v2)) / (2 : ℝ))) + ((3 : ℝ) * ((-(Real.cos (((1 : ℝ) * v0) + (-v2)))) / (1 : ℝ)))) + ((1 : ℝ) * (v0 * (Real.cos v2))))) = (((((1 : ℝ) * ((Real.exp (((2 : ℝ) * v1) + v2)) / (2 : ℝ))) + ((3 : ℝ) * ((-(Real.cos (((1 : ℝ) * v1) + (-v2)))) / (1 : ℝ)))) + ((1 : ℝ) * (v1 * (Real.cos v2)))) - ((((1 : ℝ) * ((Real.exp (((2 : ℝ) * v0) + v2)) / (2 : ℝ))) + ((3 : ℝ) * ((-(Real.cos (((1 : ℝ) * v0) + (-v2)))) / (1 : ℝ)))) + ((1 : ℝ) * (v0 * (Real.cos v2))))) := by
  have step_1 : (((((1 : ℝ) * ((Real.exp (((2 : ℝ) * v1) + v2)) / (2 : ℝ))) + ((3 : ℝ) * ((-(Real.cos (((1 : ℝ) * v1) + (-v2)))) / (1 : ℝ)))) + ((1 : ℝ) * (v1 * (Real.cos v2)))) - ((((1 : ℝ) * ((Real.exp (((2 : ℝ) * v0) + v2)) / (2 : ℝ))) + ((3 : ℝ) * ((-(Real.cos (((1 : ℝ) * v0) + (-v2)))) / (1 : ℝ)))) + ((1 : ℝ) * (v0 * (Real.cos v2))))) = (((((1 : ℝ) * ((Real.exp (((2 : ℝ) * v1) + v2)) / (2 : ℝ))) + ((3 : ℝ) * ((-(Real.cos (((1 : ℝ) * v1) + (-v2)))) / (1 : ℝ)))) + ((1 : ℝ) * (v1 * (Real.cos v2)))) - ((((1 : ℝ) * ((Real.exp (((2 : ℝ) * v0) + v2)) / (2 : ℝ))) + ((3 : ℝ) * ((-(Real.cos (((1 : ℝ) * v0) + (-v2)))) / (1 : ℝ)))) + ((1 : ℝ) * (v0 * (Real.cos v2))))) := by
    ring
  exact step_1

theorem target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : (ResearchFunction_b986f1978247a78cfdf0803337f4e332fb93b4eae06cd70bf83ff162e372a61b (v0) (v1) (v2)) = (((((1 : ℝ) * ((Real.exp (((2 : ℝ) * v1) + v2)) / (2 : ℝ))) + ((3 : ℝ) * ((-(Real.cos (((1 : ℝ) * v1) + (-v2)))) / (1 : ℝ)))) + ((1 : ℝ) * (v1 * (Real.cos v2)))) - ((((1 : ℝ) * ((Real.exp (((2 : ℝ) * v0) + v2)) / (2 : ℝ))) + ((3 : ℝ) * ((-(Real.cos (((1 : ℝ) * v0) + (-v2)))) / (1 : ℝ)))) + ((1 : ℝ) * (v0 * (Real.cos v2))))) := by
  simpa only [ResearchFunction_b986f1978247a78cfdf0803337f4e332fb93b4eae06cd70bf83ff162e372a61b, ResearchAdvanced_c49593e9c96b7619457e349bd6f8c59aafe6c3deb0c81a59dc0c2732e888d391_bridge] using (expanded_target v0 v1 v2)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
