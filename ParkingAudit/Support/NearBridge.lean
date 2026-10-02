import Mathlib
import Parking.MainTheorems
import ParkingAudit.Near.SolutionBasic

/-!
# Bridge for `Near`: Mathlib-only vocabulary to the repository

The challenge vocabulary (`ParkingAudit/Near/SolutionBasic.lean`, a verbatim copy of the vocabulary
block of `ParkingAudit/Near/Challenge.lean`, namespace `ParkingAudit`) is a statement-level copy of
the repository definitions and of the definitions it uses from `Lattice-Probability`. A plain
definition over shared Mathlib types (`law`, `walkLaw`, `contOp`, `contValue`, …) unfolds to the
same term as its counterpart, and the solution uses it definitionally. The declarations below are
those that the statement of `Near` depends on and that are not of that kind:

* the particle–hole process: `Driver` and `State` are new structures, converted field by field
  (`toDriverLP`, `toStateLP`), and its state is a new recursive definition, identified with the
  library's by induction on the round (`state_eq`);
* the recursive definition `u`, which is defined anew and equal to its counterpart by induction on
  the recursion variable;
* the definitions built on these (`U`, `Ulimit` and `meanUlimit`), whose equality follows by
  unfolding and rewriting;
* the cited-result propositions that the statement takes as hypotheses (`External.SandpileGrowth`
  and `External.Bernstein`), each equal to the repository's, by `rfl` or by rewriting with the
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

theorem U_eq : @ParkingAudit.U = @Parking.U := by
  funext d ω n x
  show _ = (LatticeProb.state (Parking.toDriver ω) n).departures x
  rw [state_data]
  rfl

theorem Ulimit_eq : @ParkingAudit.Ulimit = @Parking.Ulimit := by
  delta ParkingAudit.Ulimit
  rw [U_eq]
  rfl

theorem meanUlimit_eq : @ParkingAudit.meanUlimit = @Parking.meanUlimit := by
  delta ParkingAudit.meanUlimit
  rw [Ulimit_eq]
  rfl

end Process

/-! ### The divisible sandpile odometers -/

theorem u_eq : @ParkingAudit.u = @Parking.u := by
  funext d η n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    show max 0 (η x + ParkingAudit.walkOp (ParkingAudit.u η n) x)
      = max 0 (η x + LatticeProb.walkOp (Parking.u η n) x)
    rw [ih]
    rfl

/-! ### The cited results -/

theorem sandpileGrowth_eq :
    ParkingAudit.External.SandpileGrowth = Parking.External.SandpileGrowth := by
  delta ParkingAudit.External.SandpileGrowth ParkingAudit.External.meanSandpileReal
  rw [u_eq]
  rfl

theorem bernstein_eq : ParkingAudit.External.Bernstein = Parking.External.Bernstein := rfl

end ParkingAudit.Bridge
