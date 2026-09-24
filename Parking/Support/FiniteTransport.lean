import Parking.Support.MassTransport

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- A bounded finite-range mass transport under the stationary driving law. -/
theorem integral_box_transport (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (F : Data d → Site d → Site d → ℝ) (R : ℕ)
    (hi : ∀ a b, Integrable (fun ω => F ω a b) (law d ν))
    (he : ∀ v ω a b, F (shiftData v ω) a b = F ω (a + v) (b + v)) :
    (∫ ω, ∑ a ∈ boxFinset 0 R, F ω a 0 ∂(law d ν)) =
      ∫ ω, ∑ b ∈ boxFinset 0 R, F ω 0 b ∂(law d ν) := by
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  have ht : ∀ a : Site d, (∫ ω, F ω a 0 ∂(law d ν)) =
      ∫ ω, F ω 0 (-a) ∂(law d ν) := by
    intro a
    have h := integral_comp_shiftData (μ := iidLaw d ν) hd (fun v => iidLaw_map_shiftConf' ν v)
      (-a) (hi a 0).aestronglyMeasurable
    simpa only [he, add_neg_cancel, zero_add, dataLaw, law, stackRankLaw] using h.symm
  rw [integral_finsetSum _ (fun a _ => hi a 0), integral_finsetSum _ (fun b _ => hi 0 b)]
  simp only [ht]
  exact sum_neg_box (d := d) R (fun b : Site d => ∫ ω, F ω 0 b ∂(law d ν))

end Parking
