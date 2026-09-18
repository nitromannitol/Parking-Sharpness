/- Finite particle moments under the directed driving law. -/
import Parking.Support.OrientedInvariance
import Parking.Support.WStarBound

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem integrable_oriented_conf_iff (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {F : (Site d → ℤ) → ℝ} (hF : Measurable F) :
    Integrable (fun ω : Data d => F ω.1) (orientedLaw d ν) ↔ Integrable F (iidLaw d ν) := by
  rw [← orientedLaw_map_conf hd ν]
  exact (integrable_map_measure hF.aestronglyMeasurable measurable_fst.aemeasurable).symm

theorem integrable_oriented_confBox_rpow (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 0 < θ)
    (he : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν)
    {r : ℝ} (hr : 1 ≤ r) (x : Site d) (R : ℕ) :
    Integrable (fun ω : Data d => confBox ω x R ^ r) (orientedLaw d ν) := by
  let F : (Site d → ℤ) → ℝ := fun η => ((∑ z ∈ boxFinset x R, (η z).toNat : ℕ) : ℝ) ^ r
  have hF : Measurable F := by
    dsimp only [F]
    exact (measurable_from_countable' fun m : ℕ => (m : ℝ) ^ r).comp
      (Finset.measurable_sum _ fun z _ => (measurable_from_countable' Int.toNat).comp (measurable_pi_apply z))
  have hmap : (law d ν).map (Prod.fst : Data d → Site d → ℤ) = iidLaw d ν := by
    haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
    exact dataLaw_map_fst hd _
  have hI : Integrable F (iidLaw d ν) := by
    rw [← hmap]
    exact (integrable_map_measure hF.aestronglyMeasurable measurable_fst.aemeasurable).mpr
      (integrable_confBox_rpow hd ν hθ he hr x R)
  exact (integrable_oriented_conf_iff hd ν hF).mpr hI

theorem integrable_oriented_U_rpow (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 0 < θ)
    (he : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν)
    {r : ℝ} (hr : 1 ≤ r) (n : ℕ) (x : Site d) :
    Integrable (fun ω : Data d => (U ω n x : ℝ) ^ r) (orientedLaw d ν) := by
  have hdom := (integrable_oriented_confBox_rpow hd ν hθ he hr x n).const_mul ((n : ℝ) ^ r)
  refine hdom.mono'
    (((measurable_from_countable' fun m : ℕ => (m : ℝ) ^ r).comp (measurable_U n x)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) r),
    ← Real.mul_rpow (Nat.cast_nonneg n) (confBox_nonneg ω x n)]
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (U_le_confBox ω n x) (le_trans zero_le_one hr)

end Parking
