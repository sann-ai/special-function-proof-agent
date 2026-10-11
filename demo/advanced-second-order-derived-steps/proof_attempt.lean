import SpecialFunctionProofAgent
import SpecialFunctionProofAgent.AdvancedAnalyticDefinitions

open scoped Real
open MeasureTheory

namespace ResearchLemma_ce3faa3814cd1945c34fee234dce1b6418198932956e800fc1015f2f5ce4bb5f

theorem ResearchAdvanced_aa5d4560e0353f79ce6e214a79372cf96be8d62e5cae0fc6a1e98da25065a10b_contract (u0 : ℝ) (u1 : ℝ) (u2 : ℝ) : ∃! state : (ℝ → ℝ) × (ℝ → ℝ), (∀ at0, HasDerivAt state.1 (state.2 at0) at0) ∧ (∀ at0, HasDerivAt state.2 ((at0 + (2 : ℝ))) at0) ∧ state.1 ((1 : ℝ)) = (u0) ∧ state.2 ((1 : ℝ)) = (u1) := by
  have hrhs (at0 : ℝ) : (at0 + (2 : ℝ)) = SpecialFunctionProofAgent.evalPolynomial ([((2 : ℝ), 0), ((1 : ℝ), 1)] : List (ℝ × ℕ)) at0 := by
    simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring
  simpa only [hrhs] using SpecialFunctionProofAgent.existsUnique_polynomialSecondOrderSolution ([((2 : ℝ), 0), ((1 : ℝ), 1)] : List (ℝ × ℕ)) ((1 : ℝ)) (u0) (u1)

theorem ResearchAdvanced_aa5d4560e0353f79ce6e214a79372cf96be8d62e5cae0fc6a1e98da25065a10b_bridge (u0 : ℝ) (u1 : ℝ) (u2 : ℝ) : (SpecialFunctionProofAgent.polynomialSecondOrderPosition ([((2 : ℝ), 0), ((1 : ℝ), 1)] : List (ℝ × ℕ)) ((1 : ℝ)) (u0) (u1) (u2)) = ((u0 + (u1 * (u2 - (1 : ℝ)))) + (((((((2 : ℝ) * (u2 ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * (u2 ^ 3)) / (2 : ℝ)) / (3 : ℝ))) - (((((2 : ℝ) * ((1 : ℝ) ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * ((1 : ℝ) ^ 3)) / (2 : ℝ)) / (3 : ℝ)))) - (((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + (((1 : ℝ) * ((1 : ℝ) ^ 2)) / (2 : ℝ))) * (u2 - (1 : ℝ))))) := by
  simp only [SpecialFunctionProofAgent.polynomialSecondOrderPosition, SpecialFunctionProofAgent.secondPrimitivePolynomial, SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring


noncomputable def ResearchFunction_1812679c57e9e54a71dd7d16484548c093ff85a26526ec75c3e442e92dc3ab12 (p0 : ℝ) (p1 : ℝ) (p2 : ℝ) : ℝ := (SpecialFunctionProofAgent.polynomialSecondOrderPosition ([((2 : ℝ), 0), ((1 : ℝ), 1)] : List (ℝ × ℕ)) ((1 : ℝ)) (p0) (p1) (p2))

theorem expanded_target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : ((v0 + (v1 * (v2 - (1 : ℝ)))) + (((((((2 : ℝ) * (v2 ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * (v2 ^ 3)) / (2 : ℝ)) / (3 : ℝ))) - (((((2 : ℝ) * ((1 : ℝ) ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * ((1 : ℝ) ^ 3)) / (2 : ℝ)) / (3 : ℝ)))) - (((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + (((1 : ℝ) * ((1 : ℝ) ^ 2)) / (2 : ℝ))) * (v2 - (1 : ℝ))))) = ((v0 + (v1 * (v2 - (1 : ℝ)))) + (((((((2 : ℝ) * (v2 ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * (v2 ^ 3)) / (2 : ℝ)) / (3 : ℝ))) - (((((2 : ℝ) * ((1 : ℝ) ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * ((1 : ℝ) ^ 3)) / (2 : ℝ)) / (3 : ℝ)))) - (((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + (((1 : ℝ) * ((1 : ℝ) ^ 2)) / (2 : ℝ))) * (v2 - (1 : ℝ))))) := by
  have step_1 : ((v0 + (v1 * (v2 - (1 : ℝ)))) + (((((((2 : ℝ) * (v2 ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * (v2 ^ 3)) / (2 : ℝ)) / (3 : ℝ))) - (((((2 : ℝ) * ((1 : ℝ) ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * ((1 : ℝ) ^ 3)) / (2 : ℝ)) / (3 : ℝ)))) - (((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + (((1 : ℝ) * ((1 : ℝ) ^ 2)) / (2 : ℝ))) * (v2 - (1 : ℝ))))) = ((v0 + (v1 * (v2 - (1 : ℝ)))) + (((((((2 : ℝ) * (v2 ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * (v2 ^ 3)) / (2 : ℝ)) / (3 : ℝ))) - (((((2 : ℝ) * ((1 : ℝ) ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * ((1 : ℝ) ^ 3)) / (2 : ℝ)) / (3 : ℝ)))) - (((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + (((1 : ℝ) * ((1 : ℝ) ^ 2)) / (2 : ℝ))) * (v2 - (1 : ℝ))))) := by
    ring
  exact step_1

theorem target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : (ResearchFunction_1812679c57e9e54a71dd7d16484548c093ff85a26526ec75c3e442e92dc3ab12 (v0) (v1) (v2)) = ((v0 + (v1 * (v2 - (1 : ℝ)))) + (((((((2 : ℝ) * (v2 ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * (v2 ^ 3)) / (2 : ℝ)) / (3 : ℝ))) - (((((2 : ℝ) * ((1 : ℝ) ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * ((1 : ℝ) ^ 3)) / (2 : ℝ)) / (3 : ℝ)))) - (((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + (((1 : ℝ) * ((1 : ℝ) ^ 2)) / (2 : ℝ))) * (v2 - (1 : ℝ))))) := by
  simpa only [ResearchFunction_1812679c57e9e54a71dd7d16484548c093ff85a26526ec75c3e442e92dc3ab12, ResearchAdvanced_aa5d4560e0353f79ce6e214a79372cf96be8d62e5cae0fc6a1e98da25065a10b_bridge] using (expanded_target v0 v1 v2)

end ResearchLemma_ce3faa3814cd1945c34fee234dce1b6418198932956e800fc1015f2f5ce4bb5f

namespace BesselAgentCandidate

theorem ResearchAdvanced_aa5d4560e0353f79ce6e214a79372cf96be8d62e5cae0fc6a1e98da25065a10b_contract (u0 : ℝ) (u1 : ℝ) (u2 : ℝ) : ∃! state : (ℝ → ℝ) × (ℝ → ℝ), (∀ at0, HasDerivAt state.1 (state.2 at0) at0) ∧ (∀ at0, HasDerivAt state.2 ((at0 + (2 : ℝ))) at0) ∧ state.1 ((1 : ℝ)) = (u0) ∧ state.2 ((1 : ℝ)) = (u1) := by
  have hrhs (at0 : ℝ) : (at0 + (2 : ℝ)) = SpecialFunctionProofAgent.evalPolynomial ([((2 : ℝ), 0), ((1 : ℝ), 1)] : List (ℝ × ℕ)) at0 := by
    simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring
  simpa only [hrhs] using SpecialFunctionProofAgent.existsUnique_polynomialSecondOrderSolution ([((2 : ℝ), 0), ((1 : ℝ), 1)] : List (ℝ × ℕ)) ((1 : ℝ)) (u0) (u1)

theorem ResearchAdvanced_aa5d4560e0353f79ce6e214a79372cf96be8d62e5cae0fc6a1e98da25065a10b_bridge (u0 : ℝ) (u1 : ℝ) (u2 : ℝ) : (SpecialFunctionProofAgent.polynomialSecondOrderPosition ([((2 : ℝ), 0), ((1 : ℝ), 1)] : List (ℝ × ℕ)) ((1 : ℝ)) (u0) (u1) (u2)) = ((u0 + (u1 * (u2 - (1 : ℝ)))) + (((((((2 : ℝ) * (u2 ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * (u2 ^ 3)) / (2 : ℝ)) / (3 : ℝ))) - (((((2 : ℝ) * ((1 : ℝ) ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * ((1 : ℝ) ^ 3)) / (2 : ℝ)) / (3 : ℝ)))) - (((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + (((1 : ℝ) * ((1 : ℝ) ^ 2)) / (2 : ℝ))) * (u2 - (1 : ℝ))))) := by
  simp only [SpecialFunctionProofAgent.polynomialSecondOrderPosition, SpecialFunctionProofAgent.secondPrimitivePolynomial, SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring


noncomputable def ResearchFunction_1812679c57e9e54a71dd7d16484548c093ff85a26526ec75c3e442e92dc3ab12 (p0 : ℝ) (p1 : ℝ) (p2 : ℝ) : ℝ := (SpecialFunctionProofAgent.polynomialSecondOrderPosition ([((2 : ℝ), 0), ((1 : ℝ), 1)] : List (ℝ × ℕ)) ((1 : ℝ)) (p0) (p1) (p2))

theorem expanded_target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : ((2 : ℝ) * ((v0 + (v1 * (v2 - (1 : ℝ)))) + (((((((2 : ℝ) * (v2 ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * (v2 ^ 3)) / (2 : ℝ)) / (3 : ℝ))) - (((((2 : ℝ) * ((1 : ℝ) ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * ((1 : ℝ) ^ 3)) / (2 : ℝ)) / (3 : ℝ)))) - (((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + (((1 : ℝ) * ((1 : ℝ) ^ 2)) / (2 : ℝ))) * (v2 - (1 : ℝ)))))) = ((2 : ℝ) * ((v0 + (v1 * (v2 - (1 : ℝ)))) + (((((((2 : ℝ) * (v2 ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * (v2 ^ 3)) / (2 : ℝ)) / (3 : ℝ))) - (((((2 : ℝ) * ((1 : ℝ) ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * ((1 : ℝ) ^ 3)) / (2 : ℝ)) / (3 : ℝ)))) - (((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + (((1 : ℝ) * ((1 : ℝ) ^ 2)) / (2 : ℝ))) * (v2 - (1 : ℝ)))))) := by
  have step_1 : ((2 : ℝ) * ((v0 + (v1 * (v2 - (1 : ℝ)))) + (((((((2 : ℝ) * (v2 ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * (v2 ^ 3)) / (2 : ℝ)) / (3 : ℝ))) - (((((2 : ℝ) * ((1 : ℝ) ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * ((1 : ℝ) ^ 3)) / (2 : ℝ)) / (3 : ℝ)))) - (((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + (((1 : ℝ) * ((1 : ℝ) ^ 2)) / (2 : ℝ))) * (v2 - (1 : ℝ)))))) = ((2 : ℝ) * ((v0 + (v1 * (v2 - (1 : ℝ)))) + (((((((2 : ℝ) * (v2 ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * (v2 ^ 3)) / (2 : ℝ)) / (3 : ℝ))) - (((((2 : ℝ) * ((1 : ℝ) ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * ((1 : ℝ) ^ 3)) / (2 : ℝ)) / (3 : ℝ)))) - (((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + (((1 : ℝ) * ((1 : ℝ) ^ 2)) / (2 : ℝ))) * (v2 - (1 : ℝ)))))) := by
    have research_use_1 := (ResearchLemma_ce3faa3814cd1945c34fee234dce1b6418198932956e800fc1015f2f5ce4bb5f.expanded_target (v0) (v1) (v2))
    ring_nf at research_use_1 ⊢ <;> (simp only [research_use_1] <;> ring)
  exact step_1

theorem target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : ((2 : ℝ) * (ResearchFunction_1812679c57e9e54a71dd7d16484548c093ff85a26526ec75c3e442e92dc3ab12 (v0) (v1) (v2))) = ((2 : ℝ) * ((v0 + (v1 * (v2 - (1 : ℝ)))) + (((((((2 : ℝ) * (v2 ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * (v2 ^ 3)) / (2 : ℝ)) / (3 : ℝ))) - (((((2 : ℝ) * ((1 : ℝ) ^ 2)) / (1 : ℝ)) / (2 : ℝ)) + ((((1 : ℝ) * ((1 : ℝ) ^ 3)) / (2 : ℝ)) / (3 : ℝ)))) - (((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + (((1 : ℝ) * ((1 : ℝ) ^ 2)) / (2 : ℝ))) * (v2 - (1 : ℝ)))))) := by
  simpa only [ResearchFunction_1812679c57e9e54a71dd7d16484548c093ff85a26526ec75c3e442e92dc3ab12, ResearchAdvanced_aa5d4560e0353f79ce6e214a79372cf96be8d62e5cae0fc6a1e98da25065a10b_bridge] using (expanded_target v0 v1 v2)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
