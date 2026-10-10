import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace ResearchLemma_4d736e7c15aef1431a2f07c04b60871fa820f01fddc321162696482a52d99b86

noncomputable def ResearchFunction_70c67638866fbb45129965ce8b08bfd30ffe8c4b4a1ce6a6ec641e2aa98e1580 (p0 : ℝ) : ℝ := (Real.Gamma (p0 + (1 : ℝ)))

theorem expanded_target (v0 : ℝ) (h0 : v0 > (0 / 1 : ℝ)) : (Real.Gamma (v0 + (1 : ℝ))) = (v0 * (Real.Gamma v0)) := by
  simpa only [neg_mul, Real.rpow_eq_pow] using (SpecialFunctionProofAgent.gamma_recurrence v0 (by linarith))

theorem target (v0 : ℝ) (h0 : v0 > (0 / 1 : ℝ)) : (ResearchFunction_70c67638866fbb45129965ce8b08bfd30ffe8c4b4a1ce6a6ec641e2aa98e1580 (v0)) = (v0 * (Real.Gamma v0)) := by
  exact expanded_target v0 h0

end ResearchLemma_4d736e7c15aef1431a2f07c04b60871fa820f01fddc321162696482a52d99b86

namespace BesselAgentCandidate

noncomputable def ResearchFunction_70c67638866fbb45129965ce8b08bfd30ffe8c4b4a1ce6a6ec641e2aa98e1580 (p0 : ℝ) : ℝ := (Real.Gamma (p0 + (1 : ℝ)))

noncomputable def ResearchFunction_c439083182700d907034c4d4ae9d604640f9167f17d1763929cc179e19876d3a (p0 : ℝ) : ℝ := (ResearchFunction_70c67638866fbb45129965ce8b08bfd30ffe8c4b4a1ce6a6ec641e2aa98e1580 ((p0 + (1 : ℝ))))

theorem expanded_target (v0 : ℝ) (h0 : v0 > (0 / 1 : ℝ)) : (Real.Gamma ((v0 + (1 : ℝ)) + (1 : ℝ))) = (((v0 + (1 : ℝ)) * v0) * (Real.Gamma v0)) := by
  have step_1 : (Real.Gamma ((v0 + (1 : ℝ)) + (1 : ℝ))) = ((v0 + (1 : ℝ)) * (Real.Gamma (v0 + (1 : ℝ)))) := by
    have research_use_1 := (ResearchLemma_4d736e7c15aef1431a2f07c04b60871fa820f01fddc321162696482a52d99b86.expanded_target ((v0 + (1 : ℝ))) (by nlinarith))
    ring_nf at research_use_1 ⊢ <;> (simp only [research_use_1] <;> ring)
  have step_2 : ((v0 + (1 : ℝ)) * (Real.Gamma (v0 + (1 : ℝ)))) = (((v0 + (1 : ℝ)) * v0) * (Real.Gamma v0)) := by
    have research_use_1 := (ResearchLemma_4d736e7c15aef1431a2f07c04b60871fa820f01fddc321162696482a52d99b86.expanded_target (v0) (by nlinarith))
    ring_nf at research_use_1 ⊢ <;> (simp only [research_use_1] <;> ring)
  exact (step_1).trans step_2

theorem target (v0 : ℝ) (h0 : v0 > (0 / 1 : ℝ)) : (ResearchFunction_c439083182700d907034c4d4ae9d604640f9167f17d1763929cc179e19876d3a (v0)) = (((v0 + (1 : ℝ)) * v0) * (Real.Gamma v0)) := by
  exact expanded_target v0 h0

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
