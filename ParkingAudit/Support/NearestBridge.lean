import Mathlib
import Parking.MainTheorems
import ParkingAudit.Nearest.SolutionBasic

/-!
# Bridge for `Nearest`: Mathlib-only vocabulary to the repository

The challenge vocabulary (`ParkingAudit/Nearest/SolutionBasic.lean`, a verbatim copy of the
vocabulary block of `ParkingAudit/Nearest/Challenge.lean`, namespace `ParkingAudit`) is a
statement-level copy of the repository definitions and of the definitions it uses from
`Lattice-Probability`. A plain definition over shared Mathlib types (`law`, `walkLaw`, `contOp`,
`contValue`, …) unfolds to the same term as its counterpart, and the solution uses it
definitionally. The declarations below are those that the statement of `Nearest` depends on and that
are not of that kind:

* the particle–hole process: `Driver` and `State` are new structures, converted field by field
  (`toDriverLP`, `toStateLP`), and its state is a new recursive definition, identified with the
  library's by induction on the round (`state_eq`);
* the recursive definition `u`, which is defined anew and equal to its counterpart by induction on
  the recursion variable;
* the propositional structures `CriticalLaw` and `IsBrownianSpace`, new inductive types, proved
  equivalent to their counterparts field by field;
* the definitions built on these (`A`, `H`, `HoleCloser` and `uOf`), whose equality follows by
  unfolding and rewriting;
* the cited-result propositions that the statement takes as hypotheses (`External.SandpileGrowth`,
  `External.Bernstein`, `External.SpatialOdometerScaling`, `External.HeatInteriorRegularity`,
  `External.HeatCompactness` and `External.MultivariateBerryEsseen`), each equal to the
  repository's, by `rfl` or by rewriting with the declarations above.

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

theorem uOf_eq : @ParkingAudit.uOf = @Parking.uOf := by
  delta ParkingAudit.uOf
  rw [u_eq]
  rfl

/-! ### The two propositional structures -/

theorem criticalLaw_eq : @ParkingAudit.CriticalLaw = @Parking.CriticalLaw := by
  funext ν
  exact propext ⟨fun h => ⟨h.prob, h.nonconst, h.mean, h.expMoment⟩,
    fun h => ⟨h.prob, h.nonconst, h.mean, h.expMoment⟩⟩

theorem isBrownianSpace_eq :
    @ParkingAudit.IsBrownianSpace = @LatticeProb.IsBrownianSpace := by
  funext Ω _ d x B P
  exact propext ⟨fun h => ⟨h.start, h.coord, h.indep⟩, fun h => ⟨h.start, h.coord, h.indep⟩⟩

/-! ### The cited results -/

theorem sandpileGrowth_eq :
    ParkingAudit.External.SandpileGrowth = Parking.External.SandpileGrowth := by
  delta ParkingAudit.External.SandpileGrowth ParkingAudit.External.meanSandpileReal
  rw [u_eq]
  rfl

theorem bernstein_eq : ParkingAudit.External.Bernstein = Parking.External.Bernstein := rfl

theorem spatialOdometerScaling_eq :
    ParkingAudit.External.SpatialOdometerScaling
      = Parking.External.SpatialOdometerScaling := by
  delta ParkingAudit.External.SpatialOdometerScaling ParkingAudit.barDivisible
  rw [criticalLaw_eq, isBrownianSpace_eq, uOf_eq]
  rfl

theorem heatInteriorRegularity_eq :
    ParkingAudit.External.HeatInteriorRegularity = Parking.External.HeatInteriorRegularity :=
  rfl

theorem heatCompactness_eq :
    ParkingAudit.External.HeatCompactness = Parking.External.HeatCompactness := rfl

theorem multivariateBerryEsseen_eq :
    ParkingAudit.External.MultivariateBerryEsseen
      = Parking.External.MultivariateBerryEsseen := rfl

end ParkingAudit.Bridge
