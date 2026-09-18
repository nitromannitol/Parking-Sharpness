import Parking.Support.ProductReveal

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] [DecidableEq ι]

/-- Coordinate invariance is preserved by averaging any set of coordinates. -/
theorem partialInt_update_invariant (μ : ∀ i, Measure (X i))
    (S : Set ι) [DecidablePred (· ∈ S)] (F : (Π i, X i) → ℝ) (j : ι)
    (hF : ∀ ω a, F (Function.update ω j a) = F ω) (ω : Π i, X i) (a : X j) :
    partialInt μ S F (Function.update ω j a) = partialInt μ S F ω := by
  by_cases hj : j ∈ S
  · unfold partialInt
    apply integral_congr_ae
    apply ae_of_all
    intro η
    have he : comb S (Function.update ω j a) η = Function.update (comb S ω η) j a := by
      funext i
      by_cases hi : i = j
      · subst i; simp [comb, hj]
      · simp [comb, hi]
    change F (comb S (Function.update ω j a) η) = F (comb S ω η)
    rw [he, hF]
  · exact partialInt_update_of_notMem μ S F j hj ω a
end Parking
