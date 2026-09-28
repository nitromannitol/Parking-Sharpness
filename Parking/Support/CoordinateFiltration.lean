import Parking.Support.CoordinateErasedSpace

/-!
# A filtration revealing a finite list of coordinates

Given an injective list `q : Fin K → ι` of coordinates and a base point `b`, this builds the
filtration `coordinateFiltration b q n` whose stage `n` erases (replaces by `b`) exactly the
coordinates `q j` with `j.val ≥ n`, so stage `n` has revealed the first `n` coordinates of the
list. It is built from `erasedCoordinateSpace` applied to the shrinking set
`remainingCoordinates q n` of not-yet-revealed coordinates, and inherits monotonicity,
measurability of the revealed coordinates, and update-invariance from that construction.
-/

noncomputable section
namespace Parking
open MeasureTheory
open scoped Classical

variable {Ω ι : Type*} {X : ι → Type*} {K : ℕ}

/-- The coordinates in a finite list that have not yet been exposed. -/
def remainingCoordinates (q : Fin K → ι) (n : ℕ) : Set ι :=
  {c | ∃ j : Fin K, n ≤ j.val ∧ q j = c}

/-- `remainingCoordinates q` shrinks as `n` grows, since a coordinate needing index `≥ n`
also needs index `≥ m` for `m ≤ n`. -/
theorem remainingCoordinates_antitone (q : Fin K → ι) : Antitone (remainingCoordinates q) := by
  intro n m hnm c hc
  obtain ⟨j, hj, rfl⟩ := hc
  exact ⟨j, hnm.trans hj, rfl⟩

/-- For an injective list `q`, the coordinate `q j` still remains at stage `n` iff `j.val ≥ n`,
by cancelling `q` in the defining existential of `remainingCoordinates`. -/
theorem mem_remainingCoordinates_iff {q : Fin K → ι} (hq : Function.Injective q)
    (j : Fin K) (n : ℕ) : q j ∈ remainingCoordinates q n ↔ n ≤ j.val := by
  constructor
  · rintro ⟨i, hi, hij⟩
    simpa only [hq hij] using hi
  · exact fun hj => ⟨j, hj, rfl⟩

variable [MeasurableSpace Ω] [∀ i, MeasurableSpace (X i)]

/-- The σ-algebra at stage `n`: coordinates `q j` with `j.val ≥ n` are erased to the base
point `b`, via `erasedCoordinateSpace` applied to `remainingCoordinates q n`. -/
@[reducible] def coordinateFiltration (b : Π i, X i) (q : Fin K → ι) (n : ℕ) :
    MeasurableSpace (Ω × (Π i, X i)) := erasedCoordinateSpace b (remainingCoordinates q n)

/-- `coordinateFiltration b q` is monotone in the stage `n`, since `remainingCoordinates q`
is antitone and `erasedCoordinateSpace` is antitone in its erased set. -/
theorem coordinateFiltration_mono (b : Π i, X i) (q : Fin K → ι) :
    Monotone (coordinateFiltration (Ω := Ω) b q) := by
  intro n m hnm
  exact erasedCoordinateSpace_antitone b (remainingCoordinates_antitone q hnm)

/-- Each stage of the filtration is a sub-σ-algebra of the ambient product σ-algebra. -/
theorem coordinateFiltration_le (b : Π i, X i) (q : Fin K → ι) (n : ℕ) :
    coordinateFiltration (Ω := Ω) b q n ≤ (inferInstance : MeasurableSpace (Ω × (Π i, X i))) :=
  erasedCoordinateSpace_le b (remainingCoordinates q n)

/-- Once a coordinate `q j` has been revealed (`j.val < n`), evaluation at it is measurable
with respect to stage `n` of the filtration, since it no longer lies in
`remainingCoordinates q n`. -/
theorem measurable_coordinateFiltration_eval (b : Π i, X i) {q : Fin K → ι}
    (hq : Function.Injective q) (j : Fin K) {n : ℕ} (hjn : j.val < n) :
    Measurable[coordinateFiltration (Ω := Ω) b q n] (fun z => z.2 (q j)) := by
  apply measurable_erasedCoordinateSpace b (remainingCoordinates q n) _ (by fun_prop)
  intro z
  have hnot : q j ∉ remainingCoordinates q n := by
    rw [mem_remainingCoordinates_iff hq]
    omega
  simp only [eraseCoordinates, if_neg hnot]

/-- Membership of a stage-`n`-measurable set is unaffected by overwriting a coordinate `q j`
that has not yet been revealed (`j.val ≥ n`), inherited from `erasedCoordinateSpace_set_update`
since such `q j` lies in `remainingCoordinates q n`. -/
theorem coordinateFiltration_set_update [DecidableEq ι] (b : Π i, X i) (q : Fin K → ι)
    (j : Fin K) {n : ℕ} (hnj : n ≤ j.val) (a : X (q j))
    (A : Set (Ω × (Π i, X i))) (hA : MeasurableSet[coordinateFiltration b q n] A)
    (η : Ω) (σ : Π i, X i) :
    (η, Function.update σ (q j) a) ∈ A ↔ (η, σ) ∈ A :=
  erasedCoordinateSpace_set_update b (remainingCoordinates q n) ⟨j, hnj, rfl⟩ a A hA η σ

end Parking
