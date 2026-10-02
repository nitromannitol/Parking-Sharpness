import Mathlib
import Parking.MainTheorems
import ParkingAudit.SubcriticalTail.SolutionBasic

/-!
# Bridge for `SubcriticalTail`: Mathlib-only vocabulary to the repository

The challenge vocabulary (`ParkingAudit/SubcriticalTail/SolutionBasic.lean`, a verbatim copy of the
vocabulary block of `ParkingAudit/SubcriticalTail/Challenge.lean`, namespace `ParkingAudit`) is a
statement-level copy of the repository definitions and of the definitions it uses from
`Lattice-Probability`. A plain definition over shared Mathlib types (`law`, `walkLaw`, `contOp`,
`contValue`, …) unfolds to the same term as its counterpart, and the solution uses it
definitionally. The declarations below are those that the statement of `SubcriticalTail` depends on
and that are not of that kind:

* the particle–hole process: `Driver` and `State` are new structures, converted field by field
  (`toDriverLP`, `toStateLP`), and its state is a new recursive definition, identified with the
  library's by induction on the round (`state_eq`);
* the recursive definition `walkPath`, which is defined anew and equal to its counterpart by
  induction on the recursion variable;
* the definitions built on these (`survivorsFrom` and `S`), whose equality follows by unfolding and
  rewriting;
* the cited-result proposition that the statement takes as a hypothesis
  (`External.DonskerVaradhanRange`), equal to the repository's, by `rfl` or by rewriting with the
  declarations above.

Each equality is stated between the constants themselves, so that it rewrites every occurrence in a
statement.
-/

namespace ParkingAudit.Bridge

open MeasureTheory

/-! ### The particle–hole process -/

section Process

variable {d : ℕ}

/-- A vocabulary driver as a library driver. -/
def toDriverLP (D : ParkingAudit.Driver d) : LatticeProb.Driver d := ⟨D.eta, D.stack, D.rank⟩

/-- A vocabulary state as a library state. -/
def toStateLP (S : ParkingAudit.State d) : LatticeProb.State d :=
  ⟨S.active, S.pos, S.holes, S.departures⟩

theorem state_eq (D : ParkingAudit.Driver d) :
    ∀ t, toStateLP (ParkingAudit.state D t) = LatticeProb.state (toDriverLP D) t
  | 0 => rfl
  | t + 1 => by
    show toStateLP (ParkingAudit.step D (ParkingAudit.state D t) t)
      = LatticeProb.step (toDriverLP D) (LatticeProb.state (toDriverLP D) t) t
    rw [← state_eq D t]
    rfl

theorem state_data (ω : ParkingAudit.Data d) (t : ℕ) :
    LatticeProb.state (Parking.toDriver ω) t
      = toStateLP (ParkingAudit.state (ParkingAudit.toDriver ω) t) :=
  (state_eq (ParkingAudit.toDriver ω) t).symm

theorem survivorsFrom_eq (ω : ParkingAudit.Data d) (t : ℕ) (y : ParkingAudit.Site d) :
    ParkingAudit.survivorsFrom (ParkingAudit.toDriver ω) t y
      = LatticeProb.survivorsFrom (Parking.toDriver ω) t y := by
  show _ = ((Finset.range ((Parking.toDriver ω).eta y).toNat).filter fun i =>
    (LatticeProb.state (Parking.toDriver ω) t).active (y, i)).card
  rw [state_data]
  rfl

theorem S_eq : @ParkingAudit.S = @Parking.S := by
  funext d P t
  delta ParkingAudit.S Parking.S
  simp only [survivorsFrom_eq]

end Process

/-! ### Walks and heat kernels -/

theorem walkPath_eq : @ParkingAudit.walkPath = @Parking.walkPath := by
  funext d x p j
  induction j with
  | zero => rfl
  | succ j ih =>
    show ParkingAudit.walkPath x p j + ParkingAudit.stepVec (p j)
      = Parking.walkPath x p j + Parking.stepVec (p j)
    rw [ih]
    rfl

/-! ### The cited results -/

theorem donskerVaradhan_eq :
    ParkingAudit.External.DonskerVaradhanRange = Parking.External.DonskerVaradhanRange := by
  delta ParkingAudit.External.DonskerVaradhanRange ParkingAudit.rangeCard
  rw [walkPath_eq]
  rfl

end ParkingAudit.Bridge
