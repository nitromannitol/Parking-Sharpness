import Parking.Support.ProductSection

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- Partial integration is independent of the presentation of its retained set. -/
theorem partialInt_set_congr (μ : ∀ i, Measure (X i)) (S T : Set ι)
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] (hST : S = T)
    (F : (Π i, X i) → ℝ) (ω : Π i, X i) : partialInt μ S F ω = partialInt μ T F ω := by
  unfold partialInt
  apply integral_congr_ae
  apply ae_of_all
  intro η
  apply congrArg F
  funext i
  by_cases hi : i ∈ S
  · rw [comb_apply_of_mem hi, comb_apply_of_mem (hST ▸ hi)]
  · have ht : i ∉ T := hST ▸ hi
    rw [comb_apply_of_notMem hi, comb_apply_of_notMem ht]
end Parking
