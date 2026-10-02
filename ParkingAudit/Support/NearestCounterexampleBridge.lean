import Mathlib
import Parking.MainTheorems
import ParkingAudit.NearestCounterexample.SolutionBasic

/-!
# Bridge for `NearestCounterexample`: Mathlib-only vocabulary to the repository

The challenge vocabulary (`ParkingAudit/NearestCounterexample/SolutionBasic.lean`, a verbatim copy
of the vocabulary block of `ParkingAudit/NearestCounterexample/Challenge.lean`, namespace
`ParkingAudit`) is a statement-level copy of the repository definitions and of the definitions it
uses from `Lattice-Probability`. A plain definition over shared Mathlib types (`law`, `walkLaw`,
`contOp`, `contValue`, …) unfolds to the same term as its counterpart, and the solution uses it
definitionally. The declarations below are those that the statement of `NearestCounterexample`
depends on and that are not of that kind:

* the particle–hole process: `Driver` and `State` are new structures, converted field by field
  (`toDriverLP`, `toStateLP`), and its state is a new recursive definition, identified with the
  library's by induction on the round (`state_eq`);
* the definitions built on these (`A`, `H` and `HoleCloser`), whose equality follows by unfolding
  and rewriting;
* the cited-result proposition that the statement takes as a hypothesis (`External.Bernstein`),
  equal to the repository's, by `rfl` or by rewriting with the declarations above.

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

theorem A_eq : @ParkingAudit.A = @Parking.A := by
  funext d ω n x
  show _ = (LatticeProb.activeAt (Parking.toDriver ω) (LatticeProb.state (Parking.toDriver ω) n)
    n x).card
  rw [state_data]
  rfl

theorem H_eq : @ParkingAudit.H = @Parking.H := by
  funext d ω n x
  show _ = (LatticeProb.state (Parking.toDriver ω) n).holes x
  rw [state_data]
  rfl

theorem HoleCloser_eq : @ParkingAudit.HoleCloser = @Parking.HoleCloser := by
  delta ParkingAudit.HoleCloser ParkingAudit.holeDistance ParkingAudit.activeDistance
  rw [A_eq, H_eq]
  rfl

end Process

/-! ### The cited results -/

theorem bernstein_eq : ParkingAudit.External.Bernstein = Parking.External.Bernstein := rfl

end ParkingAudit.Bridge
