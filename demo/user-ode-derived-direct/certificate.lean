import SpecialFunctionProofAgent
import SpecialFunctionProofAgent.UserAnalyticDefinitions

open scoped Real
open MeasureTheory

namespace ResearchLemma_5c82279c78cdd3e65d45b632c5908016729bda180de48d2ce54ab6c87daf33d4

theorem ResearchAnalytic_f1f930a436d777928bc4b8d4c5db2337293b325b03ff5bb76667acdaae3b197d_contract (u0 : ℝ) (u1 : ℝ) (u2 : ℝ) : ∃! y : ℝ → ℝ, (∀ ut0, HasDerivAt y ((((u0 * ut0) + (2 : ℝ)) * (y ut0))) ut0) ∧ y ((1 : ℝ)) = (u1) := by
  have hrhs (ut0 uy0 : ℝ) : (((u0 * ut0) + (2 : ℝ)) * uy0) = SpecialFunctionProofAgent.evalPolynomial ([((2 : ℝ), 0), (u0, 1)] : List (ℝ × ℕ)) ut0 * uy0 := by
    simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, SpecialFunctionProofAgent.finiteExponentialCombination, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring
  simpa only [hrhs] using SpecialFunctionProofAgent.existsUnique_polynomialIVPSolution ([((2 : ℝ), 0), (u0, 1)] : List (ℝ × ℕ)) ((1 : ℝ)) (u1)

theorem ResearchAnalytic_f1f930a436d777928bc4b8d4c5db2337293b325b03ff5bb76667acdaae3b197d_bridge (u0 : ℝ) (u1 : ℝ) (u2 : ℝ) : (SpecialFunctionProofAgent.polynomialIVPSolution ([((2 : ℝ), 0), (u0, 1)] : List (ℝ × ℕ)) ((1 : ℝ)) (u1) (u2)) = (u1 * (Real.exp (((((2 : ℝ) * (u2 ^ 1)) / (1 : ℝ)) + ((u0 * (u2 ^ 2)) / (2 : ℝ))) - ((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + ((u0 * ((1 : ℝ) ^ 2)) / (2 : ℝ)))))) := by
  rw [SpecialFunctionProofAgent.polynomialIVPSolution_eq_exp] <;> simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, SpecialFunctionProofAgent.finiteExponentialCombination, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring


noncomputable def ResearchFunction_82261b175938d10e2dea2c231c3706699e10d94f3a2fdfcd598fc7c557a0e96a (p0 : ℝ) (p1 : ℝ) (p2 : ℝ) : ℝ := (SpecialFunctionProofAgent.polynomialIVPSolution ([((2 : ℝ), 0), (p0, 1)] : List (ℝ × ℕ)) ((1 : ℝ)) (p1) (p2))

theorem expanded_target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : (v1 * (Real.exp (((((2 : ℝ) * (v2 ^ 1)) / (1 : ℝ)) + ((v0 * (v2 ^ 2)) / (2 : ℝ))) - ((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + ((v0 * ((1 : ℝ) ^ 2)) / (2 : ℝ)))))) = (v1 * (Real.exp (((v0 * ((v2 ^ 2) - (1 : ℝ))) / (2 : ℝ)) + ((2 : ℝ) * (v2 - (1 : ℝ)))))) := by
  ring

theorem target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : (ResearchFunction_82261b175938d10e2dea2c231c3706699e10d94f3a2fdfcd598fc7c557a0e96a (v0) (v1) (v2)) = (v1 * (Real.exp (((v0 * ((v2 ^ 2) - (1 : ℝ))) / (2 : ℝ)) + ((2 : ℝ) * (v2 - (1 : ℝ)))))) := by
  simpa only [ResearchFunction_82261b175938d10e2dea2c231c3706699e10d94f3a2fdfcd598fc7c557a0e96a, ResearchAnalytic_f1f930a436d777928bc4b8d4c5db2337293b325b03ff5bb76667acdaae3b197d_bridge] using (expanded_target v0 v1 v2)

end ResearchLemma_5c82279c78cdd3e65d45b632c5908016729bda180de48d2ce54ab6c87daf33d4

namespace BesselAgentCandidate

theorem ResearchAnalytic_f1f930a436d777928bc4b8d4c5db2337293b325b03ff5bb76667acdaae3b197d_contract (u0 : ℝ) (u1 : ℝ) (u2 : ℝ) : ∃! y : ℝ → ℝ, (∀ ut0, HasDerivAt y ((((u0 * ut0) + (2 : ℝ)) * (y ut0))) ut0) ∧ y ((1 : ℝ)) = (u1) := by
  have hrhs (ut0 uy0 : ℝ) : (((u0 * ut0) + (2 : ℝ)) * uy0) = SpecialFunctionProofAgent.evalPolynomial ([((2 : ℝ), 0), (u0, 1)] : List (ℝ × ℕ)) ut0 * uy0 := by
    simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, SpecialFunctionProofAgent.finiteExponentialCombination, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring
  simpa only [hrhs] using SpecialFunctionProofAgent.existsUnique_polynomialIVPSolution ([((2 : ℝ), 0), (u0, 1)] : List (ℝ × ℕ)) ((1 : ℝ)) (u1)

theorem ResearchAnalytic_f1f930a436d777928bc4b8d4c5db2337293b325b03ff5bb76667acdaae3b197d_bridge (u0 : ℝ) (u1 : ℝ) (u2 : ℝ) : (SpecialFunctionProofAgent.polynomialIVPSolution ([((2 : ℝ), 0), (u0, 1)] : List (ℝ × ℕ)) ((1 : ℝ)) (u1) (u2)) = (u1 * (Real.exp (((((2 : ℝ) * (u2 ^ 1)) / (1 : ℝ)) + ((u0 * (u2 ^ 2)) / (2 : ℝ))) - ((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + ((u0 * ((1 : ℝ) ^ 2)) / (2 : ℝ)))))) := by
  rw [SpecialFunctionProofAgent.polynomialIVPSolution_eq_exp] <;> simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, SpecialFunctionProofAgent.finiteExponentialCombination, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring


noncomputable def ResearchFunction_82261b175938d10e2dea2c231c3706699e10d94f3a2fdfcd598fc7c557a0e96a (p0 : ℝ) (p1 : ℝ) (p2 : ℝ) : ℝ := (SpecialFunctionProofAgent.polynomialIVPSolution ([((2 : ℝ), 0), (p0, 1)] : List (ℝ × ℕ)) ((1 : ℝ)) (p1) (p2))

theorem expanded_target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : ((2 : ℝ) * (v1 * (Real.exp (((((2 : ℝ) * (v2 ^ 1)) / (1 : ℝ)) + ((v0 * (v2 ^ 2)) / (2 : ℝ))) - ((((2 : ℝ) * ((1 : ℝ) ^ 1)) / (1 : ℝ)) + ((v0 * ((1 : ℝ) ^ 2)) / (2 : ℝ))))))) = ((2 : ℝ) * (v1 * (Real.exp (((v0 * ((v2 ^ 2) - (1 : ℝ))) / (2 : ℝ)) + ((2 : ℝ) * (v2 - (1 : ℝ))))))) := by
  have research_use_1 := (ResearchLemma_5c82279c78cdd3e65d45b632c5908016729bda180de48d2ce54ab6c87daf33d4.expanded_target (v0) (v1) (v2))
  ring_nf at research_use_1 ⊢ <;> (simp only [research_use_1] <;> ring)

theorem target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : ((2 : ℝ) * (ResearchFunction_82261b175938d10e2dea2c231c3706699e10d94f3a2fdfcd598fc7c557a0e96a (v0) (v1) (v2))) = ((2 : ℝ) * (v1 * (Real.exp (((v0 * ((v2 ^ 2) - (1 : ℝ))) / (2 : ℝ)) + ((2 : ℝ) * (v2 - (1 : ℝ))))))) := by
  simpa only [ResearchFunction_82261b175938d10e2dea2c231c3706699e10d94f3a2fdfcd598fc7c557a0e96a, ResearchAnalytic_f1f930a436d777928bc4b8d4c5db2337293b325b03ff5bb76667acdaae3b197d_bridge] using (expanded_target v0 v1 v2)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
