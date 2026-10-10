import SpecialFunctionProofAgent

open scoped Real
open MeasureTheory

namespace BesselAgentCandidate

theorem target (v0 : ℝ) (v1 : ℝ) (h0 : v0 > (0 / 1 : ℝ)) (h1 : v0 < (1 / 1 : ℝ)) (h2 : v1 > (0 / 1 : ℝ)) (h3 : ((SpecialFunctionProofAgent.realBesselJ (0 : ℝ) v1) * (SpecialFunctionProofAgent.besselYInt (1 : ℤ) (v0 * v1)) - (SpecialFunctionProofAgent.besselYInt (0 : ℤ) v1) * (SpecialFunctionProofAgent.realBesselJ (1 : ℝ) (v0 * v1))) = (0 : ℝ)) : ((((SpecialFunctionProofAgent.realBesselJ (0 : ℝ) v1) * (SpecialFunctionProofAgent.besselYInt (0 : ℤ) (v0 * v1)) - (SpecialFunctionProofAgent.besselYInt (0 : ℤ) v1) * (SpecialFunctionProofAgent.realBesselJ (0 : ℝ) (v0 * v1))) ^ 2) / ((((SpecialFunctionProofAgent.realBesselJ (0 : ℝ) v1) * (SpecialFunctionProofAgent.besselYInt (1 : ℤ) v1) - (SpecialFunctionProofAgent.besselYInt (0 : ℤ) v1) * (SpecialFunctionProofAgent.realBesselJ (1 : ℝ) v1)) ^ 2) + (((v0 ^ 2) * ((SpecialFunctionProofAgent.realBesselJ (0 : ℝ) v1) * (SpecialFunctionProofAgent.besselYInt (0 : ℤ) (v0 * v1)) - (SpecialFunctionProofAgent.besselYInt (0 : ℤ) v1) * (SpecialFunctionProofAgent.realBesselJ (0 : ℝ) (v0 * v1)))) * ((SpecialFunctionProofAgent.realBesselJ (0 : ℝ) v1) * (SpecialFunctionProofAgent.besselYInt (2 : ℤ) (v0 * v1)) - (SpecialFunctionProofAgent.besselYInt (0 : ℤ) v1) * (SpecialFunctionProofAgent.realBesselJ (2 : ℝ) (v0 * v1)))))) = ((((1 : ℝ) / v0) * ((SpecialFunctionProofAgent.realBesselJ (0 : ℝ) v1) * (SpecialFunctionProofAgent.besselYInt (0 : ℤ) (v0 * v1)) - (SpecialFunctionProofAgent.besselYInt (0 : ℤ) v1) * (SpecialFunctionProofAgent.realBesselJ (0 : ℝ) (v0 * v1)))) / (((SpecialFunctionProofAgent.realBesselJ (1 : ℝ) v1) * (SpecialFunctionProofAgent.besselYInt (1 : ℤ) (v0 * v1)) - (SpecialFunctionProofAgent.besselYInt (1 : ℤ) v1) * (SpecialFunctionProofAgent.realBesselJ (1 : ℝ) (v0 * v1))) - (v0 * ((SpecialFunctionProofAgent.realBesselJ (0 : ℝ) v1) * (SpecialFunctionProofAgent.besselYInt (0 : ℤ) (v0 * v1)) - (SpecialFunctionProofAgent.besselYInt (0 : ℤ) v1) * (SpecialFunctionProofAgent.realBesselJ (0 : ℝ) (v0 * v1)))))) := by
  have h_cross_root : SpecialFunctionProofAgent.besselCross 0 1 v1 (v0 * v1) = 0 := by
    simpa only [SpecialFunctionProofAgent.besselCross, Int.cast_zero, Int.cast_one] using
      (show ((SpecialFunctionProofAgent.realBesselJ (0 : ℝ) v1) * (SpecialFunctionProofAgent.besselYInt (1 : ℤ) (v0 * v1)) - (SpecialFunctionProofAgent.besselYInt (0 : ℤ) v1) * (SpecialFunctionProofAgent.realBesselJ (1 : ℝ) (v0 * v1))) = 0 from by assumption)
  have h_left_denominator_pos := SpecialFunctionProofAgent.besselCross_root_left_denominator_pos v1 v0 (by linarith) (by linarith) (by linarith) h_cross_root
  have h_left_denominator_ne_zero := ne_of_gt h_left_denominator_pos
  have h_right_denominator_ne_zero := SpecialFunctionProofAgent.besselCross_root_right_denominator_ne_zero v1 v0 (by linarith) (by linarith) (by linarith) h_cross_root
  convert (SpecialFunctionProofAgent.besselCross_root_identity v1 v0 (by linarith) (by linarith) (by linarith) h_cross_root) using 1 <;> norm_num [SpecialFunctionProofAgent.besselCross] <;> ring

end BesselAgentCandidate

#eval IO.println "BESSEL_AUDIT_BEGIN"
#print axioms BesselAgentCandidate.target
#eval IO.println "BESSEL_AUDIT_END"
