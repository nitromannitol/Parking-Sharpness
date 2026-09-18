/- A filtration revealing a finite list of distinct product coordinates. -/
import Parking.Support.CoordinateErasedSpace

noncomputable section
namespace Parking
open MeasureTheory
open scoped Classical

variable {Ω ι : Type*} {X : ι → Type*} {K : ℕ}

/-- The coordinates in a finite list that have not yet been exposed. -/
def remainingCoordinates (q : Fin K → ι) (n : ℕ) : Set ι :=
  {c | ∃ j : Fin K, n ≤ j.val ∧ q j = c}

theorem remainingCoordinates_antitone (q : Fin K → ι) : Antitone (remainingCoordinates q) := by
  intro n m hnm c hc
  obtain ⟨j, hj, rfl⟩ := hc
  exact ⟨j, hnm.trans hj, rfl⟩

theorem mem_remainingCoordinates_iff {q : Fin K → ι} (hq : Function.Injective q)
    (j : Fin K) (n : ℕ) : q j ∈ remainingCoordinates q n ↔ n ≤ j.val := by
  constructor
  · rintro ⟨i, hi, hij⟩
    simpa only [hq hij] using hi
  · exact fun hj => ⟨j, hj, rfl⟩

variable [MeasurableSpace Ω] [∀ i, MeasurableSpace (X i)]

@[reducible] def coordinateFiltration (b : Π i, X i) (q : Fin K → ι) (n : ℕ) :
    MeasurableSpace (Ω × (Π i, X i)) := erasedCoordinateSpace b (remainingCoordinates q n)

theorem coordinateFiltration_mono (b : Π i, X i) (q : Fin K → ι) :
    Monotone (coordinateFiltration (Ω := Ω) b q) := by
  intro n m hnm
  exact erasedCoordinateSpace_antitone b (remainingCoordinates_antitone q hnm)

theorem coordinateFiltration_le (b : Π i, X i) (q : Fin K → ι) (n : ℕ) :
    coordinateFiltration (Ω := Ω) b q n ≤ (inferInstance : MeasurableSpace (Ω × (Π i, X i))) :=
  erasedCoordinateSpace_le b (remainingCoordinates q n)

theorem measurable_coordinateFiltration_eval (b : Π i, X i) {q : Fin K → ι}
    (hq : Function.Injective q) (j : Fin K) {n : ℕ} (hjn : j.val < n) :
    Measurable[coordinateFiltration (Ω := Ω) b q n] (fun z => z.2 (q j)) := by
  apply measurable_erasedCoordinateSpace b (remainingCoordinates q n) _ (by fun_prop)
  intro z
  have hnot : q j ∉ remainingCoordinates q n := by
    rw [mem_remainingCoordinates_iff hq]
    omega
  simp only [eraseCoordinates, if_neg hnot]

theorem coordinateFiltration_set_update [DecidableEq ι] (b : Π i, X i) (q : Fin K → ι)
    (j : Fin K) {n : ℕ} (hnj : n ≤ j.val) (a : X (q j))
    (A : Set (Ω × (Π i, X i))) (hA : MeasurableSet[coordinateFiltration b q n] A)
    (η : Ω) (σ : Π i, X i) :
    (η, Function.update σ (q j) a) ∈ A ↔ (η, σ) ∈ A :=
  erasedCoordinateSpace_set_update b (remainingCoordinates q n) ⟨j, hnj, rfl⟩ a A hA η σ

end Parking
