import SpecialFunctionProofAgent
import SpecialFunctionProofAgent.AdvancedAnalyticDefinitions

open scoped Real
open MeasureTheory

namespace ResearchLemma_7d36d96b79dce44cb85e39346600b72adecaeb8153bd6043c78621faf2d7a552

theorem ResearchAdvanced_3a6696db636081d74397ba2a69439339210b2f63a001de3de37e80f7d88cf7c6_contract (u0 : ℝ) (u1 : ℝ) : HasSum (fun ak0 : ℕ => ((u0 * ((u1 / ((1 : ℝ) + (u1 ^ 2))) ^ ak0)) + (((1 : ℝ) - u0) * (((-1 : ℝ) / (2 : ℝ)) ^ ak0)))) (((((u0 / ((1 : ℝ) - (u1 / ((1 : ℝ) + (u1 ^ 2))))) + (((1 : ℝ) - u0) / ((1 : ℝ) - ((-1 : ℝ) / (2 : ℝ))))) + ((0 : ℝ) * (u1 / ((1 : ℝ) + (u1 ^ 2))))) + ((0 : ℝ) * ((-1 : ℝ) / (2 : ℝ))))) := by
  have hbound : ∀ term ∈ ([(u0, (u1 / ((1 : ℝ) + (u1 ^ 2)))), (((1 : ℝ) - u0), ((-1 : ℝ) / (2 : ℝ)))] : List (ℝ × ℝ)), |term.2| < 1 := by
    intro term ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · have hbase : (u1 / ((1 : ℝ) + (u1 ^ 2))) = (u1) / (1 + (u1) ^ 2) := by
        ring_nf
      change |(u1 / ((1 : ℝ) + (u1 ^ 2)))| < 1
      rw [hbase]
      simpa only [abs_neg] using SpecialFunctionProofAgent.abs_div_one_add_sq_lt_one (u1)
    · norm_num
  convert SpecialFunctionProofAgent.hasSum_geometricCombination ([(u0, (u1 / ((1 : ℝ) + (u1 ^ 2)))), (((1 : ℝ) - u0), ((-1 : ℝ) / (2 : ℝ)))] : List (ℝ × ℝ)) hbound using 1 <;>
    first | (funext ak0; simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, SpecialFunctionProofAgent.finiteGeometricCombination] <;> ring) | (simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, SpecialFunctionProofAgent.finiteGeometricCombination] <;> ring)

theorem ResearchAdvanced_3a6696db636081d74397ba2a69439339210b2f63a001de3de37e80f7d88cf7c6_bridge (u0 : ℝ) (u1 : ℝ) : (∑' (ak0 : ℕ), ((u0 * ((u1 / ((1 : ℝ) + (u1 ^ 2))) ^ ak0)) + (((1 : ℝ) - u0) * (((-1 : ℝ) / (2 : ℝ)) ^ ak0)))) = ((((u0 / ((1 : ℝ) - (u1 / ((1 : ℝ) + (u1 ^ 2))))) + (((1 : ℝ) - u0) / ((1 : ℝ) - ((-1 : ℝ) / (2 : ℝ))))) + ((0 : ℝ) * (u1 / ((1 : ℝ) + (u1 ^ 2))))) + ((0 : ℝ) * ((-1 : ℝ) / (2 : ℝ)))) := by
  exact (ResearchAdvanced_3a6696db636081d74397ba2a69439339210b2f63a001de3de37e80f7d88cf7c6_contract u0 u1).tsum_eq


noncomputable def ResearchFunction_655b230b3da1f3b789f60e7dcf8db2398965b254efe2ef288552f123f64c10e1 (p0 : ℝ) (p1 : ℝ) : ℝ := (∑' (ak0 : ℕ), ((p0 * ((p1 / ((1 : ℝ) + (p1 ^ 2))) ^ ak0)) + (((1 : ℝ) - p0) * (((-1 : ℝ) / (2 : ℝ)) ^ ak0))))

theorem expanded_target (v0 : ℝ) (v1 : ℝ)  : ((((v0 / ((1 : ℝ) - (v1 / ((1 : ℝ) + (v1 ^ 2))))) + (((1 : ℝ) - v0) / ((1 : ℝ) - ((-1 : ℝ) / (2 : ℝ))))) + ((0 : ℝ) * (v1 / ((1 : ℝ) + (v1 ^ 2))))) + ((0 : ℝ) * ((-1 : ℝ) / (2 : ℝ)))) = ((((v0 / ((1 : ℝ) - (v1 / ((1 : ℝ) + (v1 ^ 2))))) + (((1 : ℝ) - v0) / ((1 : ℝ) - ((-1 : ℝ) / (2 : ℝ))))) + ((0 : ℝ) * (v1 / ((1 : ℝ) + (v1 ^ 2))))) + ((0 : ℝ) * ((-1 : ℝ) / (2 : ℝ)))) := by
  ring

theorem target (v0 : ℝ) (v1 : ℝ)  : (ResearchFunction_655b230b3da1f3b789f60e7dcf8db2398965b254efe2ef288552f123f64c10e1 (v0) (v1)) = ((((v0 / ((1 : ℝ) - (v1 / ((1 : ℝ) + (v1 ^ 2))))) + (((1 : ℝ) - v0) / ((1 : ℝ) - ((-1 : ℝ) / (2 : ℝ))))) + ((0 : ℝ) * (v1 / ((1 : ℝ) + (v1 ^ 2))))) + ((0 : ℝ) * ((-1 : ℝ) / (2 : ℝ)))) := by
  simpa only [ResearchFunction_655b230b3da1f3b789f60e7dcf8db2398965b254efe2ef288552f123f64c10e1, ResearchAdvanced_3a6696db636081d74397ba2a69439339210b2f63a001de3de37e80f7d88cf7c6_bridge] using (expanded_target v0 v1)

end ResearchLemma_7d36d96b79dce44cb85e39346600b72adecaeb8153bd6043c78621faf2d7a552

namespace BesselAgentCandidate

theorem ResearchAdvanced_3a6696db636081d74397ba2a69439339210b2f63a001de3de37e80f7d88cf7c6_contract (u0 : ℝ) (u1 : ℝ) : HasSum (fun ak0 : ℕ => ((u0 * ((u1 / ((1 : ℝ) + (u1 ^ 2))) ^ ak0)) + (((1 : ℝ) - u0) * (((-1 : ℝ) / (2 : ℝ)) ^ ak0)))) (((((u0 / ((1 : ℝ) - (u1 / ((1 : ℝ) + (u1 ^ 2))))) + (((1 : ℝ) - u0) / ((1 : ℝ) - ((-1 : ℝ) / (2 : ℝ))))) + ((0 : ℝ) * (u1 / ((1 : ℝ) + (u1 ^ 2))))) + ((0 : ℝ) * ((-1 : ℝ) / (2 : ℝ))))) := by
  have hbound : ∀ term ∈ ([(u0, (u1 / ((1 : ℝ) + (u1 ^ 2)))), (((1 : ℝ) - u0), ((-1 : ℝ) / (2 : ℝ)))] : List (ℝ × ℝ)), |term.2| < 1 := by
    intro term ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · have hbase : (u1 / ((1 : ℝ) + (u1 ^ 2))) = (u1) / (1 + (u1) ^ 2) := by
        ring_nf
      change |(u1 / ((1 : ℝ) + (u1 ^ 2)))| < 1
      rw [hbase]
      simpa only [abs_neg] using SpecialFunctionProofAgent.abs_div_one_add_sq_lt_one (u1)
    · norm_num
  convert SpecialFunctionProofAgent.hasSum_geometricCombination ([(u0, (u1 / ((1 : ℝ) + (u1 ^ 2)))), (((1 : ℝ) - u0), ((-1 : ℝ) / (2 : ℝ)))] : List (ℝ × ℝ)) hbound using 1 <;>
    first | (funext ak0; simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, SpecialFunctionProofAgent.finiteGeometricCombination] <;> ring) | (simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd, SpecialFunctionProofAgent.finiteGeometricCombination] <;> ring)

theorem ResearchAdvanced_3a6696db636081d74397ba2a69439339210b2f63a001de3de37e80f7d88cf7c6_bridge (u0 : ℝ) (u1 : ℝ) : (∑' (ak0 : ℕ), ((u0 * ((u1 / ((1 : ℝ) + (u1 ^ 2))) ^ ak0)) + (((1 : ℝ) - u0) * (((-1 : ℝ) / (2 : ℝ)) ^ ak0)))) = ((((u0 / ((1 : ℝ) - (u1 / ((1 : ℝ) + (u1 ^ 2))))) + (((1 : ℝ) - u0) / ((1 : ℝ) - ((-1 : ℝ) / (2 : ℝ))))) + ((0 : ℝ) * (u1 / ((1 : ℝ) + (u1 ^ 2))))) + ((0 : ℝ) * ((-1 : ℝ) / (2 : ℝ)))) := by
  exact (ResearchAdvanced_3a6696db636081d74397ba2a69439339210b2f63a001de3de37e80f7d88cf7c6_contract u0 u1).tsum_eq


noncomputable def ResearchFunction_655b230b3da1f3b789f60e7dcf8db2398965b254efe2ef288552f123f64c10e1 (p0 : ℝ) (p1 : ℝ) : ℝ := (∑' (ak0 : ℕ), ((p0 * ((p1 / ((1 : ℝ) + (p1 ^ 2))) ^ ak0)) + (((1 : ℝ) - p0) * (((-1 : ℝ) / (2 : ℝ)) ^ ak0))))

theorem expanded_target (v0 : ℝ) (v1 : ℝ)  : ((2 : ℝ) * ((((v0 / ((1 : ℝ) - (v1 / ((1 : ℝ) + (v1 ^ 2))))) + (((1 : ℝ) - v0) / ((1 : ℝ) - ((-1 : ℝ) / (2 : ℝ))))) + ((0 : ℝ) * (v1 / ((1 : ℝ) + (v1 ^ 2))))) + ((0 : ℝ) * ((-1 : ℝ) / (2 : ℝ))))) = ((2 : ℝ) * ((((v0 / ((1 : ℝ) - (v1 / ((1 : ℝ) + (v1 ^ 2))))) + (((1 : ℝ) - v0) / ((1 : ℝ) - ((-1 : ℝ) / (2 : ℝ))))) + ((0 : ℝ) * (v1 / ((1 : ℝ) + (v1 ^ 2))))) + ((0 : ℝ) * ((-1 : ℝ) / (2 : ℝ))))) := by
  have research_use_1 := (ResearchLemma_7d36d96b79dce44cb85e39346600b72adecaeb8153bd6043c78621faf2d7a552.expanded_target (v0) (v1))
  ring_nf at research_use_1 ⊢ <;> (simp only [research_use_1] <;> ring)

theorem target (v0 : ℝ) (v1 : ℝ)  : ((2 : ℝ) * (ResearchFunction_655b230b3da1f3b789f60e7dcf8db2398965b254efe2ef288552f123f64c10e1 (v0) (v1))) = ((2 : ℝ) * ((((v0 / ((1 : ℝ) - (v1 / ((1 : ℝ) + (v1 ^ 2))))) + (((1 : ℝ) - v0) / ((1 : ℝ) - ((-1 : ℝ) / (2 : ℝ))))) + ((0 : ℝ) * (v1 / ((1 : ℝ) + (v1 ^ 2))))) + ((0 : ℝ) * ((-1 : ℝ) / (2 : ℝ))))) := by
  simpa only [ResearchFunction_655b230b3da1f3b789f60e7dcf8db2398965b254efe2ef288552f123f64c10e1, ResearchAdvanced_3a6696db636081d74397ba2a69439339210b2f63a001de3de37e80f7d88cf7c6_bridge] using (expanded_target v0 v1)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
