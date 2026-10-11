import SpecialFunctionProofAgent
import SpecialFunctionProofAgent.AdvancedAnalyticDefinitions

open scoped Real
open MeasureTheory

namespace ResearchLemma_582e21b23a5f4ed1f312c40b31d2d4952ae32c53d43ed7f3004bf1d8faf7a328

theorem ResearchAdvanced_620b2737a6a3ff4d58611204421c58a9e0a603bd43ca08cf3dbecb649bb7ddd6_contract (u0 : ℝ) (u1 : ℝ) (u2 : ℝ) : ∃! y : ℝ → ℝ, (∀ at0, HasDerivAt y ((((u0 * at0) + (2 : ℝ)) * (Real.sqrt ((1 : ℝ) + ((y at0) ^ 2))))) at0) ∧ y ((1 : ℝ)) = (u1) := by
  have hr0 (ay0 : ℝ) : ((1 : ℝ) + (ay0 ^ 2)) = 1+ay0^2 := by ring
  have hrhs (at0 ay0 : ℝ) : (((u0 * at0) + (2 : ℝ)) * (Real.sqrt ((1 : ℝ) + (ay0 ^ 2)))) = SpecialFunctionProofAgent.evalPolynomial ([((2 : ℝ), 0), (u0, 1)] : List (ℝ × ℕ)) at0 * Real.sqrt (1+ay0^2) := by
    try simp only [hr0]
    simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring
  simpa only [hrhs] using SpecialFunctionProofAgent.existsUnique_nonlinearPolynomialIVPSolution ([((2 : ℝ), 0), (u0, 1)] : List (ℝ × ℕ)) ((1 : ℝ)) (u1)

theorem ResearchAdvanced_620b2737a6a3ff4d58611204421c58a9e0a603bd43ca08cf3dbecb649bb7ddd6_bridge (u0 : ℝ) (u1 : ℝ) (u2 : ℝ) : (SpecialFunctionProofAgent.nonlinearPolynomialIVPSolution ([((2 : ℝ), 0), (u0, 1)] : List (ℝ × ℕ)) ((1 : ℝ)) (u1) (u2)) = (Real.sinh ((Real.arsinh u1) + (((((2 : ℝ) * (u2 ^ 1)) / (1 : ℝ)) + ((u0 * (u2 ^ 2)) / (2 : ℝ))) - ((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + ((u0 * ((1 : ℝ) ^ 2)) / (2 : ℝ)))))) := by
  rw [SpecialFunctionProofAgent.nonlinearPolynomialIVPSolution_eq_sinh]
  simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd]
  congr 1 <;> ring


noncomputable def ResearchFunction_a1432ffb0b5922c9c3e7b2ac9f27e134804d06f5d8a229f345649294f0c067be (p0 : ℝ) (p1 : ℝ) (p2 : ℝ) : ℝ := (SpecialFunctionProofAgent.nonlinearPolynomialIVPSolution ([((2 : ℝ), 0), (p0, 1)] : List (ℝ × ℕ)) ((1 : ℝ)) (p1) (p2))

theorem expanded_target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : (Real.sinh ((Real.arsinh v1) + (((((2 : ℝ) * (v2 ^ 1)) / (1 : ℝ)) + ((v0 * (v2 ^ 2)) / (2 : ℝ))) - ((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + ((v0 * ((1 : ℝ) ^ 2)) / (2 : ℝ)))))) = (Real.sinh ((Real.arsinh v1) + (((((2 : ℝ) * (v2 ^ 1)) / (1 : ℝ)) + ((v0 * (v2 ^ 2)) / (2 : ℝ))) - ((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + ((v0 * ((1 : ℝ) ^ 2)) / (2 : ℝ)))))) := by
  ring

theorem target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : (ResearchFunction_a1432ffb0b5922c9c3e7b2ac9f27e134804d06f5d8a229f345649294f0c067be (v0) (v1) (v2)) = (Real.sinh ((Real.arsinh v1) + (((((2 : ℝ) * (v2 ^ 1)) / (1 : ℝ)) + ((v0 * (v2 ^ 2)) / (2 : ℝ))) - ((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + ((v0 * ((1 : ℝ) ^ 2)) / (2 : ℝ)))))) := by
  simpa only [ResearchFunction_a1432ffb0b5922c9c3e7b2ac9f27e134804d06f5d8a229f345649294f0c067be, ResearchAdvanced_620b2737a6a3ff4d58611204421c58a9e0a603bd43ca08cf3dbecb649bb7ddd6_bridge] using (expanded_target v0 v1 v2)

end ResearchLemma_582e21b23a5f4ed1f312c40b31d2d4952ae32c53d43ed7f3004bf1d8faf7a328

namespace BesselAgentCandidate

theorem ResearchAdvanced_620b2737a6a3ff4d58611204421c58a9e0a603bd43ca08cf3dbecb649bb7ddd6_contract (u0 : ℝ) (u1 : ℝ) (u2 : ℝ) : ∃! y : ℝ → ℝ, (∀ at0, HasDerivAt y ((((u0 * at0) + (2 : ℝ)) * (Real.sqrt ((1 : ℝ) + ((y at0) ^ 2))))) at0) ∧ y ((1 : ℝ)) = (u1) := by
  have hr0 (ay0 : ℝ) : ((1 : ℝ) + (ay0 ^ 2)) = 1+ay0^2 := by ring
  have hrhs (at0 ay0 : ℝ) : (((u0 * at0) + (2 : ℝ)) * (Real.sqrt ((1 : ℝ) + (ay0 ^ 2)))) = SpecialFunctionProofAgent.evalPolynomial ([((2 : ℝ), 0), (u0, 1)] : List (ℝ × ℕ)) at0 * Real.sqrt (1+ay0^2) := by
    try simp only [hr0]
    simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring
  simpa only [hrhs] using SpecialFunctionProofAgent.existsUnique_nonlinearPolynomialIVPSolution ([((2 : ℝ), 0), (u0, 1)] : List (ℝ × ℕ)) ((1 : ℝ)) (u1)

theorem ResearchAdvanced_620b2737a6a3ff4d58611204421c58a9e0a603bd43ca08cf3dbecb649bb7ddd6_bridge (u0 : ℝ) (u1 : ℝ) (u2 : ℝ) : (SpecialFunctionProofAgent.nonlinearPolynomialIVPSolution ([((2 : ℝ), 0), (u0, 1)] : List (ℝ × ℕ)) ((1 : ℝ)) (u1) (u2)) = (Real.sinh ((Real.arsinh u1) + (((((2 : ℝ) * (u2 ^ 1)) / (1 : ℝ)) + ((u0 * (u2 ^ 2)) / (2 : ℝ))) - ((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + ((u0 * ((1 : ℝ) ^ 2)) / (2 : ℝ)))))) := by
  rw [SpecialFunctionProofAgent.nonlinearPolynomialIVPSolution_eq_sinh]
  simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd]
  congr 1 <;> ring


noncomputable def ResearchFunction_a1432ffb0b5922c9c3e7b2ac9f27e134804d06f5d8a229f345649294f0c067be (p0 : ℝ) (p1 : ℝ) (p2 : ℝ) : ℝ := (SpecialFunctionProofAgent.nonlinearPolynomialIVPSolution ([((2 : ℝ), 0), (p0, 1)] : List (ℝ × ℕ)) ((1 : ℝ)) (p1) (p2))

theorem expanded_target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : ((2 : ℝ) * (Real.sinh ((Real.arsinh v1) + (((((2 : ℝ) * (v2 ^ 1)) / (1 : ℝ)) + ((v0 * (v2 ^ 2)) / (2 : ℝ))) - ((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + ((v0 * ((1 : ℝ) ^ 2)) / (2 : ℝ))))))) = ((2 : ℝ) * (Real.sinh ((Real.arsinh v1) + (((((2 : ℝ) * (v2 ^ 1)) / (1 : ℝ)) + ((v0 * (v2 ^ 2)) / (2 : ℝ))) - ((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + ((v0 * ((1 : ℝ) ^ 2)) / (2 : ℝ))))))) := by
  have research_use_1 := (ResearchLemma_582e21b23a5f4ed1f312c40b31d2d4952ae32c53d43ed7f3004bf1d8faf7a328.expanded_target (v0) (v1) (v2))
  ring_nf at research_use_1 ⊢ <;> (simp only [research_use_1] <;> ring)

theorem target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : ((2 : ℝ) * (ResearchFunction_a1432ffb0b5922c9c3e7b2ac9f27e134804d06f5d8a229f345649294f0c067be (v0) (v1) (v2))) = ((2 : ℝ) * (Real.sinh ((Real.arsinh v1) + (((((2 : ℝ) * (v2 ^ 1)) / (1 : ℝ)) + ((v0 * (v2 ^ 2)) / (2 : ℝ))) - ((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + ((v0 * ((1 : ℝ) ^ 2)) / (2 : ℝ))))))) := by
  simpa only [ResearchFunction_a1432ffb0b5922c9c3e7b2ac9f27e134804d06f5d8a229f345649294f0c067be, ResearchAdvanced_620b2737a6a3ff4d58611204421c58a9e0a603bd43ca08cf3dbecb649bb7ddd6_bridge] using (expanded_target v0 v1 v2)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
