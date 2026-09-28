import Parking.Support.Measurability
import LatticeProb.Equivariance

/-!
# Translation equivariance of the particle-hole process

Translation equivariance of the particle-hole process.

Translating the data by `v` means reading the configuration, the instruction
stacks and the uniform variables at the translated site, and translating the
instructions themselves back, so that an instruction of the shifted data is
again a neighbour of the site carrying it.  The particle labelled `(x, i)` in
the shifted realization is the particle labelled `(x + v, i)` in the original
one, which is `shiftLabel`.

The whole round commutes with that relabelling, field by field.  The one thing
that has to be checked, and that is easy to doubt, is that the order which
fixes the reading order of co-departing particles is itself translation
invariant.  It is: `labelKey` compares the start sites lexicographically in
their coordinates, and the lexicographic order on `Fin d → ℤ` is invariant
under adding a fixed vector to both sides, coordinate by coordinate.  So the
equivariance holds at the level of the labels and not only of the counts, which
is what the survivor counts of `lem:transport` need.
-/

open LatticeProb (ShiftDriver ShiftState card_activeAt_shift shiftRank shiftStack state_shift)

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### The translation of labels and of the data -/

/-- The translation of the driving data by `v`: the configuration, the stacks
and the uniform variables are all read at the translated site, and the
instructions are translated back. -/
def shiftData (v : Site d) (ω : Data d) : Data d :=
  (shiftConf v ω.1, shiftStack v ω.2.1, shiftRank v ω.2.2)

/-- `shiftData v` acts componentwise, as `Prod.map` of `shiftConf v`, `shiftStack v` and
`shiftRank v`. -/
theorem shiftData_eq_prodMap (v : Site d) :
    shiftData (d := d) v = Prod.map (shiftConf v) (Prod.map (shiftStack v) (shiftRank v)) := rfl

/-! ### The label order is translation invariant -/

/-! ### The candidate sets -/

/-! ### The relations between a shifted realization and the original one -/

/-- The driver built from `shiftData v ω` is a `ShiftDriver` translate of the driver built from
`ω`, with each field (`eta`, `stack`, `rank`) an immediate `rfl`. -/
theorem shiftDriver_toDriver (v : Site d) (ω : Data d) :
    ShiftDriver v (toDriver (shiftData v ω)) (toDriver ω) where
  eta _ := rfl
  stack _ := rfl
  rank _ _ := rfl

variable {v : Site d} {D' D : Driver d} {S' S : State d}

/-! ### The equivariance of the observables -/

variable (v) (ω : Data d)

/-- The state at time `t` of the shifted data `shiftData v ω` is a `ShiftState` translate of
the state of `ω`, by `LatticeProb.state_shift` applied to `shiftDriver_toDriver`. -/
theorem state_shiftData (t : ℕ) :
    ShiftState v (state (toDriver (shiftData v ω)) t) (state (toDriver ω) t) :=
  state_shift (shiftDriver_toDriver v ω) t

/-- The odometer of the shifted data reads the original odometer at the translated site, from
the `departures` field of `state_shiftData`. -/
theorem U_shiftData (n : ℕ) (x : Site d) : U (shiftData v ω) n x = U ω n (x + v) :=
  (state_shiftData v ω n).departures x

/-- The hole indicator of the shifted data reads the original one at the translated site, from
the `holes` field of `state_shiftData`. -/
theorem H_shiftData (t : ℕ) (x : Site d) : H (shiftData v ω) t x = H ω t (x + v) :=
  (state_shiftData v ω t).holes x

/-- The active-particle count of the shifted data reads the original count at the translated
site, via `LatticeProb.card_activeAt_shift`. -/
theorem A_shiftData (t : ℕ) (x : Site d) : A (shiftData v ω) t x = A ω t (x + v) :=
  card_activeAt_shift (shiftDriver_toDriver v ω) (state_shiftData v ω t) t x

/-- The particles surviving from `y` in the shifted data are exactly those surviving from
`y + v` in the original data. -/
theorem survivorsFrom_shiftData (t : ℕ) (y : Site d) :
    survivorsFrom (toDriver (shiftData v ω)) t y = survivorsFrom (toDriver ω) t (y + v) := by
  have hact : ∀ i : ℕ, (state (toDriver (shiftData v ω)) t).active (y, i)
      = (state (toDriver ω) t).active (y + v, i) := fun i =>
    (state_shiftData v ω t).active (y, i)
  simp only [survivorsFrom, hact]
  rfl

/-- The instructions of a shifted realization are neighbours of the site
carrying them as soon as the original ones are. -/
theorem stepsToNeighbour_shiftData
    (h : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) :
    ∀ q : Site d × ℕ, (shiftData v ω).2.1 q ∈ nbrFinset q.1 := by
  intro q
  have := h (q.1 + v, q.2)
  rw [mem_nbrFinset_iff] at this ⊢
  obtain ⟨i, hi | hi⟩ := this
  · refine ⟨i, Or.inl ?_⟩
    show ω.2.1 (q.1 + v, q.2) - v = q.1 + unit i
    rw [hi]; simp only; abel
  · refine ⟨i, Or.inr ?_⟩
    show ω.2.1 (q.1 + v, q.2) - v = q.1 - unit i
    rw [hi]; simp only; abel

end Parking

end
