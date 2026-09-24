/- Sigma algebras obtained by erasing a prescribed family of unrevealed coordinates. -/
import Mathlib

noncomputable section
namespace Parking
open MeasureTheory
open scoped Classical

variable {Ω ι : Type*} {X : ι → Type*}
variable [MeasurableSpace Ω] [∀ i, MeasurableSpace (X i)]

omit [MeasurableSpace Ω] [∀ i, MeasurableSpace (X i)] in
def eraseCoordinates (b : Π i, X i) (S : Set ι) (z : Ω × (Π i, X i)) : Ω × (Π i, X i) :=
  (z.1, fun i => if i ∈ S then b i else z.2 i)

@[reducible] def erasedCoordinateSpace (b : Π i, X i) (S : Set ι) : MeasurableSpace (Ω × (Π i, X i)) :=
  MeasurableSpace.comap (eraseCoordinates b S) inferInstance

theorem measurable_eraseCoordinates (b : Π i, X i) (S : Set ι) :
    Measurable (eraseCoordinates (Ω := Ω) b S) := by
  refine measurable_fst.prodMk (measurable_pi_lambda _ fun i => ?_)
  by_cases hi : i ∈ S
  · simpa only [if_pos hi] using (measurable_const : Measurable (fun _ : Ω × (Π i, X i) => b i))
  · simp only [if_neg hi]
    fun_prop

omit [MeasurableSpace Ω] [∀ i, MeasurableSpace (X i)] in
theorem eraseCoordinates_erase_of_subset (b : Π i, X i) {S T : Set ι} (hTS : T ⊆ S)
    (z : Ω × (Π i, X i)) : eraseCoordinates b S (eraseCoordinates b T z) = eraseCoordinates b S z := by
  apply Prod.ext
  · rfl
  funext i
  by_cases hi : i ∈ S
  · simp only [eraseCoordinates, if_pos hi]
  · have hiT : i ∉ T := fun h => hi (hTS h)
    simp only [eraseCoordinates, if_neg hi, if_neg hiT]

theorem erasedCoordinateSpace_le (b : Π i, X i) (S : Set ι) :
    erasedCoordinateSpace (Ω := Ω) b S ≤ (inferInstance : MeasurableSpace (Ω × (Π i, X i))) :=
  (measurable_eraseCoordinates b S).comap_le

theorem erasedCoordinateSpace_antitone (b : Π i, X i) {S T : Set ι} (hTS : T ⊆ S) :
    erasedCoordinateSpace (Ω := Ω) b S ≤ erasedCoordinateSpace b T := by
  have he : eraseCoordinates (Ω := Ω) b S ∘ eraseCoordinates b T = eraseCoordinates b S :=
    funext (eraseCoordinates_erase_of_subset b hTS)
  calc
    erasedCoordinateSpace (Ω := Ω) b S = MeasurableSpace.comap (eraseCoordinates b T)
        (MeasurableSpace.comap (eraseCoordinates b S) inferInstance) := by
      rw [MeasurableSpace.comap_comp, he]
    _ ≤ _ := MeasurableSpace.comap_mono (erasedCoordinateSpace_le b S)

theorem measurable_erasedCoordinateSpace {E : Type*} [MeasurableSpace E]
    (b : Π i, X i) (S : Set ι) (F : Ω × (Π i, X i) → E) (hF : Measurable F)
    (hinv : ∀ z, F (eraseCoordinates b S z) = F z) :
    Measurable[erasedCoordinateSpace b S] F := by
  have he : F ∘ eraseCoordinates b S = F := funext hinv
  have hself : Measurable[erasedCoordinateSpace (Ω := Ω) b S,
      inferInstanceAs (MeasurableSpace (Ω × (Π i, X i)))] (eraseCoordinates (Ω := Ω) b S) :=
    measurable_iff_comap_le.mpr le_rfl
  have h := hF.comp hself
  rwa [he] at h

omit [MeasurableSpace Ω] [∀ i, MeasurableSpace (X i)] in
theorem eraseCoordinates_update [DecidableEq ι] (b : Π i, X i) (S : Set ι) {q : ι}
    (hq : q ∈ S) (a : X q) (η : Ω) (σ : Π i, X i) :
    eraseCoordinates b S (η, Function.update σ q a) = eraseCoordinates b S (η, σ) := by
  apply Prod.ext
  · rfl
  funext i
  by_cases hi : i ∈ S
  · simp only [eraseCoordinates, if_pos hi]
  · have hne : i ≠ q := fun h => hi (h ▸ hq)
    simp only [eraseCoordinates, if_neg hi, Function.update_of_ne hne]

theorem erasedCoordinateSpace_set_update [DecidableEq ι] (b : Π i, X i) (S : Set ι) {q : ι}
    (hq : q ∈ S) (a : X q) (A : Set (Ω × (Π i, X i)))
    (hA : MeasurableSet[erasedCoordinateSpace b S] A) (η : Ω) (σ : Π i, X i) :
    (η, Function.update σ q a) ∈ A ↔ (η, σ) ∈ A := by
  obtain ⟨B, _hB, rfl⟩ := hA
  change eraseCoordinates b S (η, Function.update σ q a) ∈ B ↔ eraseCoordinates b S (η, σ) ∈ B
  rw [eraseCoordinates_update b S hq a η σ]

end Parking
