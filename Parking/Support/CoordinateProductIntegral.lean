import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.InfinitePi

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory

/-- The expectation of a finite product of independent coordinate functions factors. -/
theorem integral_finset_prod_coordinates {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Finset ι) (f : ∀ i, X i → ℝ) (hf : ∀ i, Measurable (f i)) :
    (∫ ω, ∏ i ∈ S, f i (ω i) ∂(Measure.infinitePi μ)) = ∏ i ∈ S, ∫ x, f i x ∂(μ i) := by
  classical
  have hi : iIndepFun (fun i (ω : ∀ i, X i) => f i (ω i)) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi hf
  have hs := iIndepFun.precomp (g := fun i : S => i.val) Subtype.val_injective hi
  have h := hs.integral_fun_prod_eq_prod_integral
    (fun i => ((hf i.val).comp (measurable_pi_apply i.val)).aestronglyMeasurable)
  change (∫ ω, ∏ i : S, f i.val (ω i.val) ∂(Measure.infinitePi μ)) =
    ∏ i : S, ∫ ω, f i.val (ω i.val) ∂(Measure.infinitePi μ) at h
  have hleft (ω : ∀ i, X i) : (∏ i : S, f i.val (ω i.val)) = ∏ i ∈ S, f i (ω i) :=
    Finset.prod_coe_sort S (fun i => f i (ω i))
  simp_rw [hleft] at h
  rw [Finset.prod_coe_sort S (fun i => ∫ ω, f i (ω i) ∂(Measure.infinitePi μ))] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro i _
  have hmap := measurePreserving_eval_infinitePi μ i
  have he := integral_map (μ := Measure.infinitePi μ) hmap.measurable.aemeasurable (hf i).aestronglyMeasurable
  rw [hmap.map_eq] at he
  exact he.symm
end Parking
