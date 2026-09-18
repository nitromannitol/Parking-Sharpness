/-
Almost-sure properties under finite updates to positive-mass atoms.
-/
import LatticeProb.Prob.Splice

noncomputable section
namespace Parking
open MeasureTheory MeasureTheory.Measure Filter

/-- An almost-sure property holds at every atom of positive mass. -/
theorem ae_property_at_atom {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {p : X → Prop} (hp : ∀ᵐ x ∂μ, p x) {b : X} (hb : μ {b} ≠ 0) : p b := by
  by_contra h
  have hm : μ {b} ≤ μ {x | ¬ p x} := measure_mono (Set.singleton_subset_iff.mpr h)
  have hz : μ {x | ¬ p x} = 0 := hp
  rw [hz] at hm
  exact hb (le_antisymm hm zero_le)

/-- Fixing one independent coordinate to a positive-mass atom preserves almost-sure properties. -/
theorem ae_update_infinitePi_atom {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (j : ι) (b : X) (hb : μ {b} ≠ 0)
    {p : (ι → X) → Prop} (hp : ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ι => μ)), p ω) :
    ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ι => μ)), p (Function.update ω j b) := by
  classical
  have hm := LatticeProb.measurePreserving_update_infinitePi (fun _ : ι => μ) j
  have h := hm.quasiMeasurePreserving.ae hp
  filter_upwards [Measure.ae_ae_of_ae_prod h] with ω hω
  exact ae_property_at_atom hω hb

/-- A positive-mass coordinate update is absolutely continuous with respect to the product law. -/
theorem quasiMeasurePreserving_update_infinitePi_atom {ι X : Type*}
    [DecidableEq ι] [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (j : ι) (b : X) (hb : μ {b} ≠ 0) :
    QuasiMeasurePreserving (fun ω : ι → X => Function.update ω j b)
      (Measure.infinitePi (fun _ : ι => μ)) (Measure.infinitePi (fun _ : ι => μ)) := by
  have hm : Measurable (fun ω : ι → X => Function.update ω j b) :=
    measurable_pi_lambda _ fun k => by
      by_cases hk : k = j
      · subst k; simp
      · simpa [hk] using (measurable_pi_apply k : Measurable (fun ω : ι → X => ω k))
  refine ⟨hm, AbsolutelyContinuous.mk fun s hs hz => ?_⟩
  rw [Measure.map_apply hm hs]
  have h : ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ι => μ)), ω ∉ s := by
    simpa [ae_iff] using hz
  have h' := ae_update_infinitePi_atom μ j b hb h
  rw [ae_iff] at h'
  simp only [not_not] at h'
  exact h'

/-- Fixing finitely many independent coordinates to atoms preserves almost-sure properties. -/
theorem ae_overwrite_infinitePi_atoms {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (s : Finset ι) (v : ι → X)
    (hv : ∀ j ∈ s, μ {v j} ≠ 0) {p : (ι → X) → Prop}
    (hp : ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ι => μ)), p ω) :
    ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ι => μ)), p (fun j => if j ∈ s then v j else ω j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hp
  | @insert j s hj ih =>
      have hs := ih (fun k hk => hv k (Finset.mem_insert_of_mem hk))
      have h := ae_update_infinitePi_atom μ j (v j) (hv j (Finset.mem_insert_self j s)) hs
      filter_upwards [h] with ω hω
      convert hω using 1
      funext k
      by_cases hk : k = j
      · subst k; simp [hj]
      · simp [hk]
end Parking
