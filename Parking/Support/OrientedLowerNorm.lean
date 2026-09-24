/- The directed divisible mean dominates the square norm of its linear potential. -/
import Parking.Support.IntegerLinearLower
import Parking.Support.LinearLowerLift
import Parking.Support.OrientedFirstMoment
import Parking.Support.OrientedLaw

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset

theorem exists_meanuOriented_lower_norm (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hnc : ∀ k : ℤ, ν {k} ≠ 1) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k : ℤ, (k : ℝ) ∂ν = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ,
      c * Real.sqrt (∑' z : Site d, orientedGreen d n z ^ 2) ≤ meanuOriented (orientedLaw d ν) n := by
  obtain ⟨c, hc, hb⟩ := exists_integer_linear_abs_lower ν hnc hint hmean
  have hμi : Integrable (id : ℝ → ℝ) (realLaw ν) := by
    apply (realLaw_integrable_iff ν measurable_id).mpr
    exact hint.mono' measurable_intCastReal.aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => by simp only [Real.norm_eq_abs]; rfl)
  have hμm : (∫ z : ℝ, z ∂(realLaw ν)) = 0 := (realLaw_integral ν measurable_id).trans hmean
  refine ⟨c / 2, by positivity, fun d hd n => ?_⟩
  have hΦi := integrable_orientedPotential_iid (realLaw ν) hμi n (0 : Site d)
  have hΦm := integral_orientedPotential_zero (realLaw ν) hμi hμm n (0 : Site d)
  have hlo := linear_abs_lower_infinitePi (realLaw ν) hb (boxFinset (0 : Site d) n) (orientedGreen d n)
  have hsq : (∑' z : Site d, orientedGreen d n z ^ 2) =
      ∑ z ∈ boxFinset (0 : Site d) n, orientedGreen d n z ^ 2 :=
    tsum_eq_sum fun z hz => by rw [orientedGreen_zero_outside hz, zero_pow (by norm_num)]
  have hΦ (η : Site d → ℝ) : (∑ z ∈ boxFinset (0 : Site d) n, orientedGreen d n z * η z) =
      orientedPotential η n 0 := by simp only [orientedPotential_eq_box, sub_zero]
  rw [← hsq] at hlo
  simp only [hΦ] at hlo
  have hpos := integral_max_zero_eq_half_abs (iidLaw d (realLaw ν)) hΦi hΦm
  have hcomp : (∫ η : Site d → ℝ, max 0 (orientedPotential η n 0) ∂(iidLaw d (realLaw ν))) ≤
      ∫ η : Site d → ℝ, uOriented η n 0 ∂(iidLaw d (realLaw ν)) := by
    have hm : Integrable (fun η : Site d → ℝ => max 0 (orientedPotential η n 0)) (iidLaw d (realLaw ν)) :=
      (integrable_zero (Site d → ℝ) ℝ (iidLaw d (realLaw ν))).sup hΦi
    exact integral_mono hm (integrable_uOriented_iid (realLaw ν) hμi n 0)
      (fun η => max_orientedPotential_le_u η n 0)
  have he : meanuOriented (orientedLaw d ν) n =
      ∫ η : Site d → ℝ, uOriented η n 0 ∂(iidLaw d (realLaw ν)) :=
    integral_oriented_confReal hd ν (measurable_uOriented n 0)
  rw [he]
  rw [hpos] at hcomp
  change c * Real.sqrt (∑' z : Site d, orientedGreen d n z ^ 2) ≤
    (∫ η : Site d → ℝ, |orientedPotential η n 0| ∂(iidLaw d (realLaw ν))) at hlo
  nlinarith

end Parking
