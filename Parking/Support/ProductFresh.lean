import Parking.Support.ProductSection

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A measurable functional reading only a coordinate set is measurable for that coordinate sigma algebra. -/
theorem measurable_of_reads_coordinates (base : Π i, X i) (S : Set ι) [DecidablePred (· ∈ S)]
    (F : (Π i, X i) → ℝ) (hFm : Measurable F)
    (hF : ∀ ω η, (∀ i ∈ S, ω i = η i) → F ω = F η) :
    Measurable[productCoordAlg base S] F := by
  have he : F = F ∘ (fun ω => comb S ω base) := by
    funext ω
    apply hF
    intro i hi
    exact (comb_apply_of_mem hi).symm
  rw [he]
  exact hFm.comp (Measurable.of_comap_le le_rfl)

/-- Conditional expectation of a fresh-coordinate functional is its one-coordinate average. -/
theorem condExp_eq_coordinate_integral (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (base : Π i, X i) (S : Set ι) [DecidablePred (· ∈ S)] (j : ι) (hj : j ∉ S)
    (F : (Π i, X i) → ℝ) (hFm : Measurable F) (hFi : Integrable F (Measure.infinitePi μ))
    (hF : ∀ ω η, (∀ i ∈ insert j S, ω i = η i) → F ω = F η) :
    (Measure.infinitePi μ)[F | productCoordAlg base S] =ᵐ[Measure.infinitePi μ]
      (fun ω => ∫ a, F (Function.update ω j a) ∂(μ j)) := by
  refine (partialInt_eq_condExp_coord μ base S hFm hFi).symm.trans ?_
  exact ae_of_all _ fun ω => partialInt_single_coordinate μ S j hj F hFm hF ω

/-- A centered fresh-coordinate functional is a martingale difference. -/
theorem condExp_zero_of_fresh_coordinate (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (base : Π i, X i) (S : Set ι) [DecidablePred (· ∈ S)] (j : ι) (hj : j ∉ S)
    (F : (Π i, X i) → ℝ) (hFm : Measurable F) (hFi : Integrable F (Measure.infinitePi μ))
    (hF : ∀ ω η, (∀ i ∈ insert j S, ω i = η i) → F ω = F η)
    (hzero : ∀ ω, ∫ a, F (Function.update ω j a) ∂(μ j) = 0) :
    (Measure.infinitePi μ)[F | productCoordAlg base S] =ᵐ[Measure.infinitePi μ] 0 := by
  refine (condExp_eq_coordinate_integral μ base S j hj F hFm hFi hF).trans ?_
  exact ae_of_all _ hzero
end Parking
