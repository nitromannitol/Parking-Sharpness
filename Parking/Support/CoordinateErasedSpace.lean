import Mathlib

/-!
# Erasing a family of unrevealed coordinates

Given a base point `b`, overwriting the coordinates in a set `S` of a product space
`Π i, X i` with `b`'s values defines a map `eraseCoordinates b S`, whose comap
`erasedCoordinateSpace b S` is the σ-algebra of events that only depend on the coordinates
outside `S`. This file records that this σ-algebra is antitone in `S`, that a function
invariant under the erasure map is measurable with respect to it, and that a set measurable
for it cannot distinguish two points that agree outside `S`.
-/

noncomputable section
namespace Parking
open MeasureTheory
open scoped Classical

variable {Ω ι : Type*} {X : ι → Type*}
variable [MeasurableSpace Ω] [∀ i, MeasurableSpace (X i)]

omit [MeasurableSpace Ω] [∀ i, MeasurableSpace (X i)] in
/-- Overwrite the coordinates of `z.2` lying in `S` with the base point `b`'s values, leaving
`z.1` and the coordinates outside `S` unchanged. -/
def eraseCoordinates (b : Π i, X i) (S : Set ι) (z : Ω × (Π i, X i)) : Ω × (Π i, X i) :=
  (z.1, fun i => if i ∈ S then b i else z.2 i)

/-- The σ-algebra of events depending only on the coordinates outside `S`, obtained as the
comap of the erasure map `eraseCoordinates b S`. -/
@[reducible] def erasedCoordinateSpace (b : Π i, X i) (S : Set ι) :
    MeasurableSpace (Ω × (Π i, X i)) :=
  MeasurableSpace.comap (eraseCoordinates b S) inferInstance

/-- `eraseCoordinates b S` is measurable, since each output coordinate is either the constant
`b i` (for `i ∈ S`) or the measurable projection `z ↦ z.2 i` (for `i ∉ S`). -/
theorem measurable_eraseCoordinates (b : Π i, X i) (S : Set ι) :
    Measurable (eraseCoordinates (Ω := Ω) b S) := by
  refine measurable_fst.prodMk (measurable_pi_lambda _ fun i => ?_)
  by_cases hi : i ∈ S
  · simpa only [if_pos hi] using (measurable_const : Measurable (fun _ : Ω × (Π i, X i) => b i))
  · simp only [if_neg hi]
    fun_prop

omit [MeasurableSpace Ω] [∀ i, MeasurableSpace (X i)] in
/-- Erasing the larger set `S` after already erasing a subset `T ⊆ S` is the same as erasing
`S` directly, since erasing `T` only changes coordinates in `T`, which are erased again by `S`
regardless. -/
theorem eraseCoordinates_erase_of_subset (b : Π i, X i) {S T : Set ι} (hTS : T ⊆ S)
    (z : Ω × (Π i, X i)) :
    eraseCoordinates b S (eraseCoordinates b T z) = eraseCoordinates b S z := by
  apply Prod.ext
  · rfl
  funext i
  by_cases hi : i ∈ S
  · simp only [eraseCoordinates, if_pos hi]
  · have hiT : i ∉ T := fun h => hi (hTS h)
    simp only [eraseCoordinates, if_neg hi, if_neg hiT]

/-- `erasedCoordinateSpace b S` is a sub-σ-algebra of the ambient product σ-algebra, since the
erasure map generating it is measurable. -/
theorem erasedCoordinateSpace_le (b : Π i, X i) (S : Set ι) :
    erasedCoordinateSpace (Ω := Ω) b S ≤ (inferInstance : MeasurableSpace (Ω × (Π i, X i))) :=
  (measurable_eraseCoordinates b S).comap_le

/-- Erasing a smaller set `T ⊆ S` gives a larger σ-algebra, since
`eraseCoordinates_erase_of_subset` factors the `S`-erasure map through the `T`-erasure map. -/
theorem erasedCoordinateSpace_antitone (b : Π i, X i) {S T : Set ι} (hTS : T ⊆ S) :
    erasedCoordinateSpace (Ω := Ω) b S ≤ erasedCoordinateSpace b T := by
  have he : eraseCoordinates (Ω := Ω) b S ∘ eraseCoordinates b T = eraseCoordinates b S :=
    funext (eraseCoordinates_erase_of_subset b hTS)
  calc
    erasedCoordinateSpace (Ω := Ω) b S = MeasurableSpace.comap (eraseCoordinates b T)
        (MeasurableSpace.comap (eraseCoordinates b S) inferInstance) := by
      rw [MeasurableSpace.comap_comp, he]
    _ ≤ _ := MeasurableSpace.comap_mono (erasedCoordinateSpace_le b S)

/-- A function `F` unchanged by the erasure map is measurable with respect to the erased
σ-algebra: `F` factors as `F ∘ eraseCoordinates b S`, and the erasure map itself is
`erasedCoordinateSpace b S`-measurable by construction. -/
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
/-- Overwriting an already-erased coordinate `q ∈ S` before applying `eraseCoordinates b S`
does not change the result, since that coordinate is replaced by `b q` either way. -/
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

/-- A set measurable for `erasedCoordinateSpace b S` cannot distinguish two points that agree
outside an already-erased coordinate `q ∈ S`, by pulling `eraseCoordinates_update` back through
the preimage description of such a set. -/
theorem erasedCoordinateSpace_set_update [DecidableEq ι] (b : Π i, X i) (S : Set ι) {q : ι}
    (hq : q ∈ S) (a : X q) (A : Set (Ω × (Π i, X i)))
    (hA : MeasurableSet[erasedCoordinateSpace b S] A) (η : Ω) (σ : Π i, X i) :
    (η, Function.update σ q a) ∈ A ↔ (η, σ) ∈ A := by
  obtain ⟨B, _hB, rfl⟩ := hA
  change eraseCoordinates b S (η, Function.update σ q a) ∈ B ↔ eraseCoordinates b S (η, σ) ∈ B
  rw [eraseCoordinates_update b S hq a η σ]

end Parking
