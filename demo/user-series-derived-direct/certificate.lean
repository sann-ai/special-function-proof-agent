import SpecialFunctionProofAgent
import SpecialFunctionProofAgent.UserAnalyticDefinitions

open scoped Real
open MeasureTheory

namespace ResearchLemma_dd5c8c8d92419008da5df0339ae6219d83f9ae4e5fed8032b71609f2727fb730

theorem ResearchAnalytic_90db31acc78eebd021d3330f316406541c6b10968aa2350c41bed421a3e67b84_contract (u0 : ℝ) (u1 : ℝ) : HasSum (fun uk0 : ℕ => ((u0 * ((u1 ^ uk0) / (uk0.factorial : ℝ))) + (((1 : ℝ) - u0) * (((-u1) ^ uk0) / (uk0.factorial : ℝ))))) (((u0 * (Real.exp u1)) + (((1 : ℝ) - u0) * (Real.exp (-u1))))) := by
  convert SpecialFunctionProofAgent.hasSum_factorialCombination ([(u0, u1), (((1 : ℝ) - u0), (-u1))] : List (ℝ × ℝ)) using 1 <;>
    first | (funext uk0; simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, SpecialFunctionProofAgent.finiteExponentialCombination, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring) | (simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, SpecialFunctionProofAgent.finiteExponentialCombination, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring)

theorem ResearchAnalytic_90db31acc78eebd021d3330f316406541c6b10968aa2350c41bed421a3e67b84_bridge (u0 : ℝ) (u1 : ℝ) : (∑' (uk0 : ℕ), ((u0 * ((u1 ^ uk0) / (uk0.factorial : ℝ))) + (((1 : ℝ) - u0) * (((-u1) ^ uk0) / (uk0.factorial : ℝ))))) = ((u0 * (Real.exp u1)) + (((1 : ℝ) - u0) * (Real.exp (-u1)))) := by
  exact (ResearchAnalytic_90db31acc78eebd021d3330f316406541c6b10968aa2350c41bed421a3e67b84_contract u0 u1).tsum_eq


noncomputable def ResearchFunction_a57070a8fad22ee60df32dff63ce460de5d28198e293d254874dd7caa41e650d (p0 : ℝ) (p1 : ℝ) : ℝ := (∑' (uk0 : ℕ), ((p0 * ((p1 ^ uk0) / (uk0.factorial : ℝ))) + (((1 : ℝ) - p0) * (((-p1) ^ uk0) / (uk0.factorial : ℝ)))))

theorem expanded_target (v0 : ℝ) (v1 : ℝ)  : ((v0 * (Real.exp v1)) + (((1 : ℝ) - v0) * (Real.exp (-v1)))) = ((v0 * (Real.exp v1)) + (((1 : ℝ) - v0) * (Real.exp (-v1)))) := by
  ring

theorem target (v0 : ℝ) (v1 : ℝ)  : (ResearchFunction_a57070a8fad22ee60df32dff63ce460de5d28198e293d254874dd7caa41e650d (v0) (v1)) = ((v0 * (Real.exp v1)) + (((1 : ℝ) - v0) * (Real.exp (-v1)))) := by
  simpa only [ResearchFunction_a57070a8fad22ee60df32dff63ce460de5d28198e293d254874dd7caa41e650d, ResearchAnalytic_90db31acc78eebd021d3330f316406541c6b10968aa2350c41bed421a3e67b84_bridge] using (expanded_target v0 v1)

end ResearchLemma_dd5c8c8d92419008da5df0339ae6219d83f9ae4e5fed8032b71609f2727fb730

namespace BesselAgentCandidate

theorem ResearchAnalytic_90db31acc78eebd021d3330f316406541c6b10968aa2350c41bed421a3e67b84_contract (u0 : ℝ) (u1 : ℝ) : HasSum (fun uk0 : ℕ => ((u0 * ((u1 ^ uk0) / (uk0.factorial : ℝ))) + (((1 : ℝ) - u0) * (((-u1) ^ uk0) / (uk0.factorial : ℝ))))) (((u0 * (Real.exp u1)) + (((1 : ℝ) - u0) * (Real.exp (-u1))))) := by
  convert SpecialFunctionProofAgent.hasSum_factorialCombination ([(u0, u1), (((1 : ℝ) - u0), (-u1))] : List (ℝ × ℝ)) using 1 <;>
    first | (funext uk0; simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, SpecialFunctionProofAgent.finiteExponentialCombination, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring) | (simp only [SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, SpecialFunctionProofAgent.finiteExponentialCombination, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd] <;> ring)

theorem ResearchAnalytic_90db31acc78eebd021d3330f316406541c6b10968aa2350c41bed421a3e67b84_bridge (u0 : ℝ) (u1 : ℝ) : (∑' (uk0 : ℕ), ((u0 * ((u1 ^ uk0) / (uk0.factorial : ℝ))) + (((1 : ℝ) - u0) * (((-u1) ^ uk0) / (uk0.factorial : ℝ))))) = ((u0 * (Real.exp u1)) + (((1 : ℝ) - u0) * (Real.exp (-u1)))) := by
  exact (ResearchAnalytic_90db31acc78eebd021d3330f316406541c6b10968aa2350c41bed421a3e67b84_contract u0 u1).tsum_eq


noncomputable def ResearchFunction_a57070a8fad22ee60df32dff63ce460de5d28198e293d254874dd7caa41e650d (p0 : ℝ) (p1 : ℝ) : ℝ := (∑' (uk0 : ℕ), ((p0 * ((p1 ^ uk0) / (uk0.factorial : ℝ))) + (((1 : ℝ) - p0) * (((-p1) ^ uk0) / (uk0.factorial : ℝ)))))

theorem expanded_target (v0 : ℝ) (v1 : ℝ)  : ((2 : ℝ) * ((v0 * (Real.exp v1)) + (((1 : ℝ) - v0) * (Real.exp (-v1))))) = ((2 : ℝ) * ((v0 * (Real.exp v1)) + (((1 : ℝ) - v0) * (Real.exp (-v1))))) := by
  have research_use_1 := (ResearchLemma_dd5c8c8d92419008da5df0339ae6219d83f9ae4e5fed8032b71609f2727fb730.expanded_target (v0) (v1))
  ring_nf at research_use_1 ⊢ <;> (simp only [research_use_1] <;> ring)

theorem target (v0 : ℝ) (v1 : ℝ)  : ((2 : ℝ) * (ResearchFunction_a57070a8fad22ee60df32dff63ce460de5d28198e293d254874dd7caa41e650d (v0) (v1))) = ((2 : ℝ) * ((v0 * (Real.exp v1)) + (((1 : ℝ) - v0) * (Real.exp (-v1))))) := by
  simpa only [ResearchFunction_a57070a8fad22ee60df32dff63ce460de5d28198e293d254874dd7caa41e650d, ResearchAnalytic_90db31acc78eebd021d3330f316406541c6b10968aa2350c41bed421a3e67b84_bridge] using (expanded_target v0 v1)

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
