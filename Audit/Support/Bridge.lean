import Mathlib
import Parking.MainTheorems
import Audit.Support.Vocabulary

/-!
# Bridges from the Mathlib-only vocabulary to the repository

The challenge vocabulary (`Audit/Support/Vocabulary.lean`, namespace `ParkingAudit`) is a
statement-level copy of the repository definitions and of the definitions it uses from
`Lattice-Probability`.  A plain definition over shared Mathlib types (`law`, `walkLaw`,
`contOp`, `contValue`, …) unfolds to the same term as its counterpart.  Three kinds of
declaration do not, and this file identifies each with its counterpart:

* the recursive definitions (`u`, `uOriented`, `walkPath`, `heat`, `kIter`, `kSol`,
  `orientedPath`, `LocalCLT.heatKernel`, `CriticalScale.odometer`, and the state of the
  particle–hole process), which are new recursive definitions, equal to their counterparts by
  induction;
* the structures (`Driver`, `State`, `CriticalLaw`, `IsBrownianSpace`), which are new
  inductive types: the two process structures are converted field by field, and the two
  propositional ones are equivalent to their counterparts;
* the definitions built on these, whose equality follows by unfolding and rewriting.

Each equality is stated between the constants themselves, so that it rewrites every occurrence
in a statement.  From these, each cited-result proposition of the vocabulary equals the
repository's.
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

theorem Ulimit_eq : @ParkingAudit.Ulimit = @Parking.Ulimit := by
  delta ParkingAudit.Ulimit
  rw [U_eq]
  rfl

theorem meanUlimit_eq : @ParkingAudit.meanUlimit = @Parking.meanUlimit := by
  delta ParkingAudit.meanUlimit
  rw [Ulimit_eq]
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

theorem uOf_eq : @ParkingAudit.uOf = @Parking.uOf := by
  delta ParkingAudit.uOf
  rw [u_eq]
  rfl

theorem meanu_eq : @ParkingAudit.meanu = @Parking.meanu := by
  delta ParkingAudit.meanu
  rw [uOf_eq]
  rfl

theorem meanuOriented_eq : @ParkingAudit.meanuOriented = @Parking.meanuOriented := by
  delta ParkingAudit.meanuOriented
  rw [uOriented_eq]
  rfl

theorem kIter_eq : @ParkingAudit.kIter = @LatticeProb.Walk.kIter := by
  funext d r K j
  induction j with
  | zero => rfl
  | succ j ih =>
    funext x
    show ∑ y ∈ ParkingAudit.boxFinset x r, ParkingAudit.kIter r K j y * K y x
      = ∑ y ∈ LatticeProb.boxFinset x r, LatticeProb.Walk.kIter r K j y * K y x
    rw [ih]
    rfl

theorem kSol_eq : @ParkingAudit.kSol = @Parking.kSol := by
  funext d r K η n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    show max 0 (η x + ParkingAudit.kOp r K (ParkingAudit.kSol r K η n) x)
      = max 0 (η x + LatticeProb.Walk.kOp r K (Parking.kSol r K η n) x)
    rw [ih]
    rfl

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

theorem orientedPath_eq : @ParkingAudit.orientedPath = @Parking.orientedPath := by
  funext d x p j
  induction j with
  | zero => rfl
  | succ j ih =>
    show ParkingAudit.orientedPath x p j - ParkingAudit.unit (p j).1
      = Parking.orientedPath x p j - LatticeProb.unit (p j).1
    rw [ih]
    rfl

theorem heat_eq : @ParkingAudit.heat = @Parking.heat := by
  funext d j
  induction j with
  | zero => rfl
  | succ j ih =>
    funext x
    show ParkingAudit.walkOp (ParkingAudit.heat d j) x = LatticeProb.walkOp (Parking.heat d j) x
    rw [ih]
    rfl

theorem heatKernel_eq : @ParkingAudit.LocalCLT.heatKernel = @LatticeProb.LocalCLT.heatKernel := by
  funext d k
  induction k with
  | zero => rfl
  | succ k ih =>
    funext x y
    show (∑ i : Fin d, (ParkingAudit.LocalCLT.heatKernel d k (x + ParkingAudit.unit i) y
        + ParkingAudit.LocalCLT.heatKernel d k (x - ParkingAudit.unit i) y)) / (2 * d)
      = (∑ i : Fin d, (LatticeProb.LocalCLT.heatKernel d k (x + LatticeProb.unit i) y
        + LatticeProb.LocalCLT.heatKernel d k (x - LatticeProb.unit i) y)) / (2 * d)
    rw [ih]
    rfl

theorem odometer_eq :
    @ParkingAudit.CriticalScale.odometer = @Parking.CriticalScale.odometer := by
  funext d σ t
  induction t with
  | zero => rfl
  | succ t ih =>
    show ParkingAudit.CriticalScale.relax σ (ParkingAudit.CriticalScale.odometer σ t)
      = Parking.CriticalScale.relax σ (Parking.CriticalScale.odometer σ t)
    rw [ih]
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

theorem uConcentration_eq :
    ParkingAudit.External.UConcentration = Parking.External.UConcentration := by
  delta ParkingAudit.External.UConcentration ParkingAudit.kGreen
  rw [kSol_eq, kIter_eq]
  rfl

theorem greenNorms_eq : ParkingAudit.External.GreenNorms = Parking.External.GreenNorms := by
  delta ParkingAudit.External.GreenNorms ParkingAudit.greenMax ParkingAudit.green
  rw [heat_eq]
  rfl

theorem donskerVaradhan_eq :
    ParkingAudit.External.DonskerVaradhanRange = Parking.External.DonskerVaradhanRange := by
  delta ParkingAudit.External.DonskerVaradhanRange ParkingAudit.rangeCard
  rw [walkPath_eq]
  rfl

theorem spatialOdometerScaling_eq :
    ParkingAudit.External.SpatialOdometerScaling
      = Parking.External.SpatialOdometerScaling := by
  delta ParkingAudit.External.SpatialOdometerScaling ParkingAudit.barDivisible
  rw [criticalLaw_eq, isBrownianSpace_eq, uOf_eq]
  rfl

theorem heatInteriorRegularity_eq :
    ParkingAudit.External.HeatInteriorRegularity = Parking.External.HeatInteriorRegularity :=
  rfl

theorem heatStrongMinimum_eq :
    ParkingAudit.External.HeatStrongMinimum = Parking.External.HeatStrongMinimum := rfl

theorem heatCompactness_eq :
    ParkingAudit.External.HeatCompactness = Parking.External.HeatCompactness := rfl

theorem varianceScale_eq :
    ParkingAudit.External.VarianceScale = Parking.External.VarianceScale := by
  delta ParkingAudit.External.VarianceScale ParkingAudit.CriticalScale.greenTime
    ParkingAudit.greenTime ParkingAudit.CriticalScale.windowKernel
    ParkingAudit.CriticalScale.heatKernel
  rw [heatKernel_eq]
  rfl

theorem multivariateBerryEsseen_eq :
    ParkingAudit.External.MultivariateBerryEsseen
      = Parking.External.MultivariateBerryEsseen := rfl

theorem criticalScaleLowerTail_eq :
    ParkingAudit.External.CriticalScaleLowerTail
      = Parking.External.CriticalScaleLowerTail := by
  delta ParkingAudit.External.CriticalScaleLowerTail
  rw [varianceScale_eq, multivariateBerryEsseen_eq, odometer_eq]
  rfl

theorem orientedStoppingStability_eq :
    ParkingAudit.External.OrientedStoppingStability
      = Parking.External.OrientedStoppingStability := by
  delta ParkingAudit.External.OrientedStoppingStability ParkingAudit.orientedStoppingSup
    ParkingAudit.orientedTerminalValues ParkingAudit.orientedTerminalValue
  rw [orientedPath_eq]
  rfl

theorem binomialLocalCLT_eq :
    ParkingAudit.External.BinomialLocalCLT = Parking.External.BinomialLocalCLT := rfl

end ParkingAudit.Bridge
