/- The dimension-two upper bound under the oriented parking law. -/
import Parking.Support.OrientedDivisibleMoment
import Parking.Support.OrientedLaw
import Parking.Support.UpperTarget

noncomputable section
namespace Parking
open MeasureTheory LatticeProb

theorem exists_meanuOriented_two_upper (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hmean : ∫ k : ℤ, (k : ℝ) ∂ν = 0) (r : ℝ) (hr : 4 < r)
    (hmom : Integrable (fun k : ℤ => |(k : ℝ)| ^ r) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      meanuOriented (orientedLaw 2 ν) n ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4) := by
  have hr1 : 1 ≤ r := by linarith
  have hμmom : Integrable (fun z : ℝ => |z| ^ r) (realLaw ν) :=
    (realLaw_integrable_iff ν (measurable_abs.pow_const r)).mpr hmom
  have hμmean : ∫ z : ℝ, z ∂(realLaw ν) = 0 :=
    (realLaw_integral ν measurable_id).trans hmean
  obtain ⟨C, hC, hu⟩ := exists_uOriented_two_moment (realLaw ν) r hr hμmom hμmean
  refine ⟨C, hC, fun n hn => ?_⟩
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  obtain ⟨hi, hb⟩ := hu n hn
  have hui : Integrable (fun η : Site 2 → ℝ => uOriented η n 0) (iidLaw 2 (realLaw ν)) :=
    integrable_abs_of_rpow _ hr1 _ (measurable_uOriented n 0).aestronglyMeasurable hi
  have hip : Integrable (fun η : Site 2 → ℝ => uOriented η n 0 ^ r) (iidLaw 2 (realLaw ν)) := by
    simpa only [abs_of_nonneg (uOriented_nonneg _ _ _)] using hi
  have hj := integral_le_rNorm (fun η : Site 2 → ℝ => uOriented_nonneg η n 0) hui hr1 hip
  have he : meanuOriented (orientedLaw 2 ν) n =
      ∫ η : Site 2 → ℝ, uOriented η n 0 ∂(iidLaw 2 (realLaw ν)) :=
    integral_oriented_confReal (by norm_num) ν (measurable_uOriented n 0)
  rw [he]
  exact hj.trans (by simpa only [rNorm, abs_of_nonneg (uOriented_nonneg _ _ _)] using hb)

end Parking
