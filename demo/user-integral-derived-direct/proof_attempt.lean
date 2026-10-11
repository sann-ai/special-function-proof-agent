import SpecialFunctionProofAgent
import SpecialFunctionProofAgent.UserAnalyticDefinitions

open scoped Real
open MeasureTheory

namespace ResearchLemma_6c0fa73c0407cfcdf7d4a9b516728719fab8af8c3fa9c13dc11be285fd7882b8

theorem ResearchAnalytic_afaea59c0c1ce0b13c3a5051c72089744a1763649dc6403f0f2622f324569129_contract (u0 : ℝ) (u1 : ℝ) (u2 : ℝ) : IntervalIntegrable (fun ut0 : ℝ => ((ut0 + u2) ^ 2)) volume (u0) (u1) := by
  have hfun : (fun ut0 : ℝ => ((ut0 + u2) ^ 2)) = SpecialFunctionProofAgent.evalPolynomial ([((u2 * u2), 0), ((u2 + u2), 1), ((1 : ℝ), 2)] : List (ℝ × ℕ)) := by
    funext ut0
    simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, SpecialFunctionProofAgent.finiteExponentialCombination, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring
  rw [hfun]
  exact SpecialFunctionProofAgent.intervalIntegrable_evalPolynomial ([((u2 * u2), 0), ((u2 + u2), 1), ((1 : ℝ), 2)] : List (ℝ × ℕ)) (u0) (u1)

theorem ResearchAnalytic_afaea59c0c1ce0b13c3a5051c72089744a1763649dc6403f0f2622f324569129_bridge (u0 : ℝ) (u1 : ℝ) (u2 : ℝ) : (∫ ut0 in u0..u1, ((ut0 + u2) ^ 2)) = ((((((u2 * u2) * (u1 ^ 1)) / (1 : ℝ)) + (((u2 + u2) * (u1 ^ 2)) / (2 : ℝ))) + (((1 : ℝ) * (u1 ^ 3)) / (3 : ℝ))) - (((((u2 * u2) * (u0 ^ 1)) / (1 : ℝ)) + (((u2 + u2) * (u0 ^ 2)) / (2 : ℝ))) + (((1 : ℝ) * (u0 ^ 3)) / (3 : ℝ)))) := by
  have hfun : (fun ut0 : ℝ => ((ut0 + u2) ^ 2)) = SpecialFunctionProofAgent.evalPolynomial ([((u2 * u2), 0), ((u2 + u2), 1), ((1 : ℝ), 2)] : List (ℝ × ℕ)) := by
    funext ut0
    simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, SpecialFunctionProofAgent.finiteExponentialCombination, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring
  change (∫ ut0 in (u0)..(u1), (fun ut0 : ℝ => ((ut0 + u2) ^ 2)) ut0) = _
  rw [hfun]
  change SpecialFunctionProofAgent.polynomialIntegral ([((u2 * u2), 0), ((u2 + u2), 1), ((1 : ℝ), 2)] : List (ℝ × ℕ)) (u0) (u1) = _
  rw [SpecialFunctionProofAgent.polynomialIntegral_eq_primitive_sub] <;> simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, SpecialFunctionProofAgent.finiteExponentialCombination, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring


noncomputable def ResearchFunction_5dc64c7ea8c9d68692eede8fd9dea99b1921b04e399fcde1429b8d23b7993d4e (p0 : ℝ) (p1 : ℝ) (p2 : ℝ) : ℝ := (∫ ut0 in p0..p1, ((ut0 + p2) ^ 2))

theorem expanded_target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : ((((((v2 * v2) * (v1 ^ 1)) / (1 : ℝ)) + (((v2 + v2) * (v1 ^ 2)) / (2 : ℝ))) + (((1 : ℝ) * (v1 ^ 3)) / (3 : ℝ))) - (((((v2 * v2) * (v0 ^ 1)) / (1 : ℝ)) + (((v2 + v2) * (v0 ^ 2)) / (2 : ℝ))) + (((1 : ℝ) * (v0 ^ 3)) / (3 : ℝ)))) = ((((v1 + v2) ^ 3) - ((v0 + v2) ^ 3)) / (3 : ℝ)) := by
  have step_1 : ((((((v2 * v2) * (v1 ^ 1)) / (1 : ℝ)) + (((v2 + v2) * (v1 ^ 2)) / (2 : ℝ))) + (((1 : ℝ) * (v1 ^ 3)) / (3 : ℝ))) - (((((v2 * v2) * (v0 ^ 1)) / (1 : ℝ)) + (((v2 + v2) * (v0 ^ 2)) / (2 : ℝ))) + (((1 : ℝ) * (v0 ^ 3)) / (3 : ℝ)))) = ((((v1 + v2) ^ 3) - ((v0 + v2) ^ 3)) / (3 : ℝ)) := by
    ring
  exact step_1

theorem target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : (ResearchFunction_5dc64c7ea8c9d68692eede8fd9dea99b1921b04e399fcde1429b8d23b7993d4e (v0) (v1) (v2)) = ((((v1 + v2) ^ 3) - ((v0 + v2) ^ 3)) / (3 : ℝ)) := by
  simpa only [ResearchFunction_5dc64c7ea8c9d68692eede8fd9dea99b1921b04e399fcde1429b8d23b7993d4e, ResearchAnalytic_afaea59c0c1ce0b13c3a5051c72089744a1763649dc6403f0f2622f324569129_bridge] using (expanded_target v0 v1 v2)

end ResearchLemma_6c0fa73c0407cfcdf7d4a9b516728719fab8af8c3fa9c13dc11be285fd7882b8

namespace BesselAgentCandidate

theorem ResearchAnalytic_afaea59c0c1ce0b13c3a5051c72089744a1763649dc6403f0f2622f324569129_contract (u0 : ℝ) (u1 : ℝ) (u2 : ℝ) : IntervalIntegrable (fun ut0 : ℝ => ((ut0 + u2) ^ 2)) volume (u0) (u1) := by
  have hfun : (fun ut0 : ℝ => ((ut0 + u2) ^ 2)) = SpecialFunctionProofAgent.evalPolynomial ([((u2 * u2), 0), ((u2 + u2), 1), ((1 : ℝ), 2)] : List (ℝ × ℕ)) := by
    funext ut0
    simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, SpecialFunctionProofAgent.finiteExponentialCombination, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring
  rw [hfun]
  exact SpecialFunctionProofAgent.intervalIntegrable_evalPolynomial ([((u2 * u2), 0), ((u2 + u2), 1), ((1 : ℝ), 2)] : List (ℝ × ℕ)) (u0) (u1)

theorem ResearchAnalytic_afaea59c0c1ce0b13c3a5051c72089744a1763649dc6403f0f2622f324569129_bridge (u0 : ℝ) (u1 : ℝ) (u2 : ℝ) : (∫ ut0 in u0..u1, ((ut0 + u2) ^ 2)) = ((((((u2 * u2) * (u1 ^ 1)) / (1 : ℝ)) + (((u2 + u2) * (u1 ^ 2)) / (2 : ℝ))) + (((1 : ℝ) * (u1 ^ 3)) / (3 : ℝ))) - (((((u2 * u2) * (u0 ^ 1)) / (1 : ℝ)) + (((u2 + u2) * (u0 ^ 2)) / (2 : ℝ))) + (((1 : ℝ) * (u0 ^ 3)) / (3 : ℝ)))) := by
  have hfun : (fun ut0 : ℝ => ((ut0 + u2) ^ 2)) = SpecialFunctionProofAgent.evalPolynomial ([((u2 * u2), 0), ((u2 + u2), 1), ((1 : ℝ), 2)] : List (ℝ × ℕ)) := by
    funext ut0
    simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, SpecialFunctionProofAgent.finiteExponentialCombination, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring
  change (∫ ut0 in (u0)..(u1), (fun ut0 : ℝ => ((ut0 + u2) ^ 2)) ut0) = _
  rw [hfun]
  change SpecialFunctionProofAgent.polynomialIntegral ([((u2 * u2), 0), ((u2 + u2), 1), ((1 : ℝ), 2)] : List (ℝ × ℕ)) (u0) (u1) = _
  rw [SpecialFunctionProofAgent.polynomialIntegral_eq_primitive_sub] <;> simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, SpecialFunctionProofAgent.finiteExponentialCombination, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring


noncomputable def ResearchFunction_5dc64c7ea8c9d68692eede8fd9dea99b1921b04e399fcde1429b8d23b7993d4e (p0 : ℝ) (p1 : ℝ) (p2 : ℝ) : ℝ := (∫ ut0 in p0..p1, ((ut0 + p2) ^ 2))

theorem expanded_target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : ((2 : ℝ) * ((((((v2 * v2) * (v1 ^ 1)) / (1 : ℝ)) + (((v2 + v2) * (v1 ^ 2)) / (2 : ℝ))) + (((1 : ℝ) * (v1 ^ 3)) / (3 : ℝ))) - (((((v2 * v2) * (v0 ^ 1)) / (1 : ℝ)) + (((v2 + v2) * (v0 ^ 2)) / (2 : ℝ))) + (((1 : ℝ) * (v0 ^ 3)) / (3 : ℝ))))) = ((2 : ℝ) * ((((v1 + v2) ^ 3) - ((v0 + v2) ^ 3)) / (3 : ℝ))) := by
  have research_use_1 := (ResearchLemma_6c0fa73c0407cfcdf7d4a9b516728719fab8af8c3fa9c13dc11be285fd7882b8.expanded_target (v0) (v1) (v2))
  ring_nf at research_use_1 ⊢ <;> (simp only [research_use_1] <;> ring)

theorem target (v0 : ℝ) (v1 : ℝ) (v2 : ℝ)  : ((2 : ℝ) * (ResearchFunction_5dc64c7ea8c9d68692eede8fd9dea99b1921b04e399fcde1429b8d23b7993d4e (v0) (v1) (v2))) = ((2 : ℝ) * ((((v1 + v2) ^ 3) - ((v0 + v2) ^ 3)) / (3 : ℝ))) := by
  simpa only [ResearchFunction_5dc64c7ea8c9d68692eede8fd9dea99b1921b04e399fcde1429b8d23b7993d4e, ResearchAnalytic_afaea59c0c1ce0b13c3a5051c72089744a1763649dc6403f0f2622f324569129_bridge] using (expanded_target v0 v1 v2)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
