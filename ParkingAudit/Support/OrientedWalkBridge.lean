import Mathlib
import Parking.MainTheorems
import ParkingAudit.OrientedWalk.SolutionBasic

/-!
# Bridge for `OrientedWalk`: Mathlib-only vocabulary to the repository

The challenge vocabulary (`ParkingAudit/OrientedWalk/SolutionBasic.lean`, a verbatim copy of the
vocabulary block of `ParkingAudit/OrientedWalk/Challenge.lean`, namespace `ParkingAudit`) is a
statement-level copy of the repository definitions and of the definitions it uses from
`Lattice-Probability`. A plain definition over shared Mathlib types (`law`, `walkLaw`, `contOp`,
`contValue`, …) unfolds to the same term as its counterpart, and the solution uses it
definitionally. The declarations below are those that the statement of `OrientedWalk` depends on and
that are not of that kind:

* the particle–hole process: `Driver` and `State` are new structures, converted field by field
  (`toDriverLP`, `toStateLP`), and its state is a new recursive definition, identified with the
  library's by induction on the round (`state_eq`);
* the recursive definitions `uOriented` and `orientedPath`, which are defined anew and equal to
  their counterparts by induction on the recursion variable;
* the propositional structure `CriticalLaw`, a new inductive type, proved equivalent to its
  counterpart field by field;
* the definitions built on these (`U`, `survivorsFrom`, `S`, `meanU` and `meanuOriented`), whose
  equality follows by unfolding and rewriting;
* the cited-result propositions that the statement takes as hypotheses (`External.Bernstein` and
  `External.OrientedStoppingStability`), each equal to the repository's, by `rfl` or by rewriting
  with the declarations above.

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

theorem meanU_eq : @ParkingAudit.meanU = @Parking.meanU := by
  delta ParkingAudit.meanU
  rw [U_eq]
  rfl

end Process

/-! ### The divisible sandpile odometers -/

theorem uOriented_eq : @ParkingAudit.uOriented = @Parking.uOriented := by
  funext d η n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    show max 0 (η x + ParkingAudit.orientedOp (ParkingAudit.uOriented η n) x)
      = max 0 (η x + Parking.orientedOp (Parking.uOriented η n) x)
    rw [ih]
    rfl

theorem meanuOriented_eq : @ParkingAudit.meanuOriented = @Parking.meanuOriented := by
  delta ParkingAudit.meanuOriented
  rw [uOriented_eq]
  rfl

/-! ### Walks and heat kernels -/

theorem orientedPath_eq : @ParkingAudit.orientedPath = @Parking.orientedPath := by
  funext d x p j
  induction j with
  | zero => rfl
  | succ j ih =>
    show ParkingAudit.orientedPath x p j - ParkingAudit.unit (p j).1
      = Parking.orientedPath x p j - LatticeProb.unit (p j).1
    rw [ih]
    rfl

/-! ### The two propositional structures -/

theorem criticalLaw_eq : @ParkingAudit.CriticalLaw = @Parking.CriticalLaw := by
  funext ν
  exact propext ⟨fun h => ⟨h.prob, h.nonconst, h.mean, h.expMoment⟩,
    fun h => ⟨h.prob, h.nonconst, h.mean, h.expMoment⟩⟩

/-! ### The cited results -/

theorem bernstein_eq : ParkingAudit.External.Bernstein = Parking.External.Bernstein := rfl

theorem orientedStoppingStability_eq :
    ParkingAudit.External.OrientedStoppingStability
      = Parking.External.OrientedStoppingStability := by
  delta ParkingAudit.External.OrientedStoppingStability ParkingAudit.orientedStoppingSup
    ParkingAudit.orientedTerminalValues ParkingAudit.orientedTerminalValue
  rw [orientedPath_eq]
  rfl

end ParkingAudit.Bridge
