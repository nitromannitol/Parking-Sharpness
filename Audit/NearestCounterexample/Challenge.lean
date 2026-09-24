import Mathlib

/-!
# Theorem 1.6 (`thm:nearest-counterexample`): comparator challenge

Mathlib-only comparator challenge for Theorem 1.6 (`thm:nearest-counterexample`) of Bou-Rabee and Panagiotis,
*Sharpness and critical scaling of parking* (arXiv:2609.02820).  The certified statement is
`Parking.Frozen.nearest_counterexample`, restated in `Parking/MainTheorems.lean` as `Parking.nearest_counterexample`.  Content:
for `d ≥ 5` there is `p ∈ (0, 1/2)` such that, for the three-point law
`P(±1) = p`, `P(0) = 1 - 2p`, that probability has a positive liminf.

Only Mathlib is imported.  The vocabulary between `VOCABULARY-BEGIN` and `VOCABULARY-END`
rebuilds, from Mathlib primitives, every definition needed to read the theorem: the lattice,
i.i.d. fields and the particle–hole process (copied from `Lattice-Probability`), the parking
model and its two odometers, the walk and lattice kernels, the continuum objects of the scaling
limits, the critical-scale model of the cited lower-tail estimate, and the cited results.  It is
a statement-level copy of the definitions the repository uses (see `Audit/README.md` for the
provenance table) and is byte-identical in all eight challenges.  The sole intentional `sorry`
is the proof of the final theorem.

## Cited results

The paper uses results from the literature without proof.  The repository does not prove them
either: each is a proposition taken as an explicit hypothesis, and this challenge carries the
same hypotheses, restated in the vocabulary:
* `External.Bernstein`: Pinelis's martingale moment and Bernstein inequalities.

## Presentation deltas

None at the level of the displayed statement: the theorem below is the statement of
`Parking.nearest_counterexample` with every repository and library name replaced by its vocabulary copy.
-/

-- VOCABULARY-BEGIN
namespace ParkingAudit

/-! ## 1. The lattice, i.i.d. fields and the particle–hole process

Copied from the shared library `Lattice-Probability` (`LatticeProb/Site.lean`,
`LatticeProb/IID.lean`, `LatticeProb/ParticleHole.lean`). -/

section LatticeProb

/-- A site of the lattice `ℤ^d`. -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ

/-- The unit vector in direction `i`. -/
def unit {d : ℕ} (i : Fin d) : Site d := Pi.single i 1

/-- The sum of `u` over the neighbours of `x`, direction by direction. -/
def nbrSum {d : ℕ} (u : Site d → ℝ) (x : Site d) : ℝ :=
  ∑ i : Fin d, (u (x + unit i) + u (x - unit i))

/-- The simple random walk operator `(P u)(x) = (1/2d) ∑_{y ∼ x} u(y)`. -/
noncomputable def walkOp {d : ℕ} (u : Site d → ℝ) (x : Site d) : ℝ :=
  nbrSum u x / (2 * d)

open MeasureTheory
open scoped ENNReal

/-- The law of an i.i.d. field on `ℤ^d` with one-site law `μ`. -/
noncomputable def iidLaw (d : ℕ) {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    Measure (Site d → α) :=
  Measure.infinitePi fun _ : Site d => μ

/-- One instruction at `y`: a uniformly chosen neighbour. -/
noncomputable def instructionLaw {d : ℕ} (y : Site d) : Measure (Site d) :=
  ((2 * (d : ℝ≥0∞))⁻¹) • Finset.univ.sum fun i : Fin d =>
    Measure.dirac (y + unit i) + Measure.dirac (y - unit i)

/-- The law of independent instruction stacks, one at each site. -/
noncomputable def stackLaw (d : ℕ) : Measure (Site d × ℕ → Site d) :=
  Measure.infinitePi fun p : Site d × ℕ => instructionLaw p.1

end LatticeProb

section ParticleHole

noncomputable section

/-- A particle label: its starting site and its index there. -/
abbrev Label (d : ℕ) : Type := Site d × ℕ

/-- The data driving one realization of the process. -/
structure Driver (d : ℕ) where
  /-- The initial configuration, particles minus holes. -/
  eta : Site d → ℤ
  /-- The instruction stacks: the `j`-th departure from `y` goes to `stack (y, j)`. -/
  stack : Site d × ℕ → Site d
  /-- The uniform variable of particle `p` in round `t + 1`. -/
  rank : Label d × ℕ → ℝ

/-- The state after a round. -/
structure State (d : ℕ) where
  active : Label d → Bool
  pos : Label d → Site d
  holes : Site d → ℕ
  departures : Site d → ℕ

/-- The sup-norm box of radius `r` about `y`, as a finset. -/
def boxFinset {d : ℕ} (y : Site d) (r : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun i => (Finset.Icc (y i - r) (y i + r))

/-- The labels of every particle that started within sup-distance `r` of `y`. -/
def candidates {d : ℕ} (η : Site d → ℤ) (y : Site d) (r : ℕ) : Finset (Label d) :=
  (boxFinset y r).biUnion fun x => (Finset.range (η x).toNat).map ⟨fun i => (x, i), by
    intro a b h; simpa using h⟩

/-- The initial state: `η(x)⁺` active particles at `x`, `η(x)⁻` holes there. -/
def initial {d : ℕ} (η : Site d → ℤ) : State d where
  active := fun p => decide (p.2 < (η p.1).toNat)
  pos := fun p => p.1
  holes := fun x => (-η x).toNat
  departures := fun _ => 0

/-- The key that orders labels: the start site, read as a function on `Fin d`
and ordered lexicographically in the coordinates, and then the index. -/
def labelKey {d : ℕ} (p : Label d) : Lex (Lex (Fin d → ℤ) × ℕ) := toLex (toLex p.1, p.2)

/-- Labels are ordered lexicographically, in the start site first, itself ordered
lexicographically in the coordinates, and then in the index.  This is a genuine
linear order on labels; it fixes the reading order of the instructions when
several particles leave a site in the same round, and it breaks ties among
ranks. -/
def labelLT {d : ℕ} (p q : Label d) : Prop := labelKey p < labelKey q

instance {d : ℕ} : DecidableRel (labelLT (d := d)) := Classical.decRel _

/-- The particles active at `y` after round `t`, among the candidates. -/
def activeAt {d : ℕ} (D : Driver d) (S : State d) (t : ℕ) (y : Site d) : Finset (Label d) :=
  (candidates D.eta y t).filter fun p => S.active p ∧ S.pos p = y

/-- The instruction index read by `p` when it leaves `y` in round `t + 1`: the
departures so far plus the number of co-departing particles with smaller labels. -/
def instructionIndex {d : ℕ} (D : Driver d) (S : State d) (t : ℕ) (p : Label d) : ℕ :=
  S.departures (S.pos p) + ((activeAt D S t (S.pos p)).filter fun q => labelLT q p).card

/-- Where `p` stands after the step of round `t + 1`. -/
def nextPos {d : ℕ} (D : Driver d) (S : State d) (t : ℕ) (p : Label d) : Site d :=
  if S.active p then D.stack (S.pos p, instructionIndex D S t p) else S.pos p

/-- The particles arriving at `x` in round `t + 1`. -/
def arrivalsAt {d : ℕ} (D : Driver d) (S : State d) (t : ℕ) (x : Site d) : Finset (Label d) :=
  (candidates D.eta x (t + 1)).filter fun p => S.active p ∧ nextPos D S t p = x

/-- `p` settles in round `t + 1` when fewer arrivals of smaller rank than it
reach its new site than there are holes there. -/
def settles {d : ℕ} (D : Driver d) (S : State d) (t : ℕ) (p : Label d) : Bool :=
  S.active p ∧
    ((arrivalsAt D S t (nextPos D S t p)).filter fun q =>
        D.rank (q, t) < D.rank (p, t) ∨ (D.rank (q, t) = D.rank (p, t) ∧ labelLT q p)).card
      < S.holes (nextPos D S t p)

/-- One round. -/
def step {d : ℕ} (D : Driver d) (S : State d) (t : ℕ) : State d where
  active := fun p => S.active p ∧ !settles D S t p
  pos := nextPos D S t
  holes := fun x => S.holes x - (arrivalsAt D S t x).card
  departures := fun y => S.departures y + (activeAt D S t y).card

/-- The state after `t` rounds. -/
def state {d : ℕ} (D : Driver d) : ℕ → State d
  | 0 => initial D.eta
  | t + 1 => step D (state D t) t

/-- The particle odometer `U_t(x)`: the departures from `x` in the first `t` rounds. -/
def particleOdometer {d : ℕ} (D : Driver d) (t : ℕ) (x : Site d) : ℕ :=
  (state D t).departures x

/-- `A_t(x)`: the number of active particles at `x` after round `t`. -/
def activeCount {d : ℕ} (D : Driver d) (t : ℕ) (x : Site d) : ℕ :=
  (activeAt D (state D t) t x).card

/-- `H_t(x)`: the unfilled holes at `x` after round `t`. -/
def holeCount {d : ℕ} (D : Driver d) (t : ℕ) (x : Site d) : ℕ :=
  (state D t).holes x

/-- The particles which started at `y` and are still active after round `t`. -/
def survivorsFrom {d : ℕ} (D : Driver d) (t : ℕ) (y : Site d) : ℕ :=
  ((Finset.range (D.eta y).toNat).filter fun i => (state D t).active (y, i)).card

/-- The law of the uniform variables: independent uniforms on `[0, 1]`. -/
noncomputable def rankLaw (d : ℕ) : MeasureTheory.Measure (Label d × ℕ → ℝ) :=
  MeasureTheory.Measure.infinitePi fun _ : Label d × ℕ =>
    MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The law of the instruction stacks for the oriented walk: each step goes to
`y + e_i` with probability `1/d`. -/
noncomputable def orientedInstructionLaw {d : ℕ} (y : Site d) : MeasureTheory.Measure (Site d) :=
  ((d : ENNReal)⁻¹) • Finset.univ.sum fun i : Fin d => MeasureTheory.Measure.dirac (y + unit i)

noncomputable def orientedStackLaw (d : ℕ) : MeasureTheory.Measure (Site d × ℕ → Site d) :=
  MeasureTheory.Measure.infinitePi fun p : Site d × ℕ => orientedInstructionLaw p.1

end

end ParticleHole

/-! ## 2. Heat kernels, the finite-time Green kernel and Brownian motion

Copied from `LatticeProb/Walk/LocalCLT.lean`, `LatticeProb/Walk/LatticeGreen.lean` and
`LatticeProb/Prob/BrownianExit.lean`. -/

namespace LocalCLT

/-- The `k`-step transition probability `p_k(x, y)` of simple random walk,
recursing in the starting point `x` (the form used by the sandpile paper). -/
noncomputable def heatKernel (d : ℕ) : ℕ → Site d → Site d → ℝ
  | 0 => fun x y => if x = y then 1 else 0
  | k + 1 => fun x y =>
      (∑ i : Fin d, (heatKernel d k (x + unit i) y + heatKernel d k (x - unit i) y)) / (2 * d)

end LocalCLT

section LatticeGreen

open Finset

/-- The finite-time Green kernel `g_t(x, y) = ∑_{k<t} p_k(x, y)`. -/
noncomputable def greenTime (d : ℕ) (t : ℕ) (x y : Site d) : ℝ :=
  ∑ k ∈ Finset.range t, LocalCLT.heatKernel d k x y

end LatticeGreen

section Brownian

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

/-- **Brownian motion on `ℝ ^ d` with generator `Δ / (2 d)` started at `x`**: it starts at
`x`, each coordinate centred and scaled by `√d` is a real Brownian motion, and the
coordinate processes are independent.  These are the three properties produced by
`ParkingAudit.exists_isBrownian`. -/
structure IsBrownianSpace {Ω : Type*} [MeasurableSpace Ω] (d : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (P : Measure Ω) : Prop where
  /-- The process starts at `x`. -/
  start : ∀ᵐ ω ∂P, B 0 ω = x
  /-- Each coordinate, centred and scaled by `√d`, is a real Brownian motion. -/
  coord : ∀ i : Fin d, IsBrownianReal (fun t ω => Real.sqrt d * (B t ω i - x i)) P
  /-- The coordinate processes are independent. -/
  indep : iIndepFun (fun (i : Fin d) (ω : Ω) => fun t : ℝ≥0 => B t ω i) P

end Brownian

/-! ## 3. The parking model

Copied from `Parking/Basic.lean`. -/

section Basic

open MeasureTheory
open scoped ENNReal

/-- The driving data as a plain triple, so that its law is a product measure. -/
abbrev Data (d : ℕ) : Type :=
  (Site d → ℤ) × (Site d × ℕ → Site d) × (Label d × ℕ → ℝ)

/-- The driver built from a triple. -/
def toDriver {d : ℕ} (ω : Data d) : Driver d := ⟨ω.1, ω.2.1, ω.2.2⟩

/-- The law of the data for the simple random walk: i.i.d. `η` with one-site
law `ν`, independent instruction stacks, independent uniforms. -/
noncomputable def law (d : ℕ) (ν : Measure ℤ) : Measure (Data d) :=
  (ParkingAudit.iidLaw d ν).prod ((ParkingAudit.stackLaw d).prod (ParkingAudit.rankLaw d))

/-- The law of the data for the oriented walk. -/
noncomputable def orientedLaw (d : ℕ) (ν : Measure ℤ) : Measure (Data d) :=
  (ParkingAudit.iidLaw d ν).prod ((ParkingAudit.orientedStackLaw d).prod (ParkingAudit.rankLaw d))

/-- The particle odometer `U_n(x)` of a realization. -/
noncomputable def U {d : ℕ} (ω : Data d) (n : ℕ) (x : Site d) : ℕ :=
  ParkingAudit.particleOdometer (toDriver ω) n x

/-- `A_t(x)`, the active particles at `x` after round `t`. -/
noncomputable def A {d : ℕ} (ω : Data d) (t : ℕ) (x : Site d) : ℕ :=
  ParkingAudit.activeCount (toDriver ω) t x

/-- `H_t(x)`, the unfilled holes at `x` after round `t`. -/
noncomputable def H {d : ℕ} (ω : Data d) (t : ℕ) (x : Site d) : ℕ :=
  ParkingAudit.holeCount (toDriver ω) t x

/-- The limiting odometer `U_∞(x)`, in `ℕ∞`. -/
noncomputable def Ulimit {d : ℕ} (ω : Data d) (x : Site d) : ℕ∞ :=
  ⨆ n : ℕ, (U ω n x : ℕ∞)

/-- `E U_n(0)` under a law `P` on the data. -/
noncomputable def meanU {d : ℕ} (P : Measure (Data d)) (n : ℕ) : ℝ :=
  ∫ ω, (U ω n 0 : ℝ) ∂P

/-- `E U_∞(0)`, in `ℝ≥0∞`. -/
noncomputable def meanUlimit {d : ℕ} (P : Measure (Data d)) : ℝ≥0∞ :=
  ∫⁻ ω, (Ulimit ω 0 : ℝ≥0∞) ∂P

/-- `S_t`: the expected number of particles started at the origin and still
active after round `t`. -/
noncomputable def S {d : ℕ} (P : Measure (Data d)) (t : ℕ) : ℝ :=
  ∫ ω, (ParkingAudit.survivorsFrom (toDriver ω) t 0 : ℝ) ∂P

/-- The divisible sandpile odometer `u_{n+1} = (η + P u_n)⁺`, `u_0 = 0`. -/
noncomputable def u {d : ℕ} (η : Site d → ℝ) : ℕ → Site d → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => max 0 (η x + walkOp (u η n) x)

/-- The oriented operator `(P⃗ f)(x) = (1/d) ∑_i f(x - e_i)`. -/
noncomputable def orientedOp {d : ℕ} (f : Site d → ℝ) (x : Site d) : ℝ :=
  (∑ i : Fin d, f (x - unit i)) / d

/-- The oriented divisible sandpile odometer `u⃗_{n+1} = (η + P⃗ u⃗_n)⁺`. -/
noncomputable def uOriented {d : ℕ} (η : Site d → ℝ) : ℕ → Site d → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => max 0 (η x + orientedOp (uOriented η n) x)

/-- The sandpile odometer of a realization, from its integer configuration. -/
noncomputable def uOf {d : ℕ} (ω : Data d) (n : ℕ) (x : Site d) : ℝ :=
  u (fun y => (ω.1 y : ℝ)) n x

/-- `E u_n(0)` under a law `P` on the data. -/
noncomputable def meanu {d : ℕ} (P : Measure (Data d)) (n : ℕ) : ℝ :=
  ∫ ω, uOf ω n 0 ∂P

/-- `E u⃗_n(0)` under a law `P` on the data. -/
noncomputable def meanuOriented {d : ℕ} (P : Measure (Data d)) (n : ℕ) : ℝ :=
  ∫ ω, uOriented (fun y => (ω.1 y : ℝ)) n 0 ∂P

/-- The standing hypotheses on the one-site law at the critical density:
integer valued, nonconstant, mean zero, with an exponential moment. -/
structure CriticalLaw (ν : Measure ℤ) : Prop where
  prob : IsProbabilityMeasure ν
  nonconst : ∀ k : ℤ, ν {k} ≠ 1
  mean : ∫ k, (k : ℝ) ∂ν = 0
  expMoment : ∃ θ : ℝ, 0 < θ ∧ Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν

/-- The sup-norm of a site, in `ℕ`.  It measures the range of a kernel, where
one step in each coordinate is one unit. -/
def supNorm {d : ℕ} (x : Site d) : ℕ := Finset.univ.sup fun i => (x i).natAbs

/-- The graph distance from the origin, `|x| = ∑_i |x_i|`.  `parking.tex:588-601`
fixes distances on `Z^d` to be graph distances, so this is the paper's `|x|`. -/
def graphNorm {d : ℕ} (x : Site d) : ℕ := ∑ i, (x i).natAbs

/-- The graph distance from the origin to the nearest unfilled hole after round
`t`, in `ℕ∞`, so that "no hole anywhere" is `⊤` and not a junk value. -/
noncomputable def holeDistance {d : ℕ} (ω : Data d) (t : ℕ) : ℕ∞ :=
  ⨅ x ∈ {x : Site d | 0 < H ω t x}, (graphNorm x : ℕ∞)

/-- The graph distance from the origin to the nearest active particle after
round `t`. -/
noncomputable def activeDistance {d : ℕ} (ω : Data d) (t : ℕ) : ℕ∞ :=
  ⨅ x ∈ {x : Site d | 0 < A ω t x}, (graphNorm x : ℕ∞)

/-- The event that the origin is closer to an unfilled hole than to an active
particle after round `t`. -/
def HoleCloser {d : ℕ} (ω : Data d) (t : ℕ) : Prop :=
  holeDistance ω t < activeDistance ω t

end Basic

/-! ## 4. The walk, lattice kernels, the range and the continuum objects

Copied from `Parking/Support/` (`Walk`, `Kernel`, `Range`, `Continuum`, `ContOrientedLimit`,
`ContStopGeneral`, `ContSpatialValue`, `ContUc`, `SpatialGreenPairing`, `Oriented`,
`OrientedMaximum`, `OrientedScaling`, `OrientedTerminal`, `Near`, `ThreePointLaw`) and from the
two kernels of `Parking/External/SRWLocalCLT.lean` and `Parking/External/LinearFieldScaling.lean`. -/

section Walk

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The displacement of one signed direction. -/
def stepVec {d : ℕ} (b : Fin d × Bool) : Site d :=
  if b.2 then ParkingAudit.unit b.1 else -ParkingAudit.unit b.1

/-- The position of the walk from `x` after `j` steps of the direction
sequence `p`. -/
def walkPath {d : ℕ} (x : Site d) (p : ℕ → Fin d × Bool) : ℕ → Site d
  | 0 => x
  | j + 1 => walkPath x p j + stepVec (p j)

/-- The uniform law of one signed direction. -/
def stepLaw (d : ℕ) : Measure (Fin d × Bool) :=
  ((2 * (d : ℝ≥0∞))⁻¹) • Finset.univ.sum fun b : Fin d × Bool => Measure.dirac b

/-- The law of the direction sequence of a simple random walk. -/
def walkLaw (d : ℕ) : Measure (ℕ → Fin d × Bool) :=
  Measure.infinitePi fun _ : ℕ => stepLaw d

/-- `σ` is a stopping time for the natural filtration of the walk, bounded by
`n`: it never exceeds `n`, and it is decided by the directions it has read. -/
def IsStoppingTimeLE {d : ℕ} (n : ℕ) (σ : (ℕ → Fin d × Bool) → ℕ) : Prop :=
  (∀ p, σ p ≤ n) ∧ ∀ p q : ℕ → Fin d × Bool, (∀ j < σ p, p j = q j) → σ q = σ p

/-- `P^j(0, x)`, the `j`-step transition probability of the walk. -/
def heat (d : ℕ) : ℕ → Site d → ℝ
  | 0 => fun x => if x = 0 then 1 else 0
  | j + 1 => fun x => ParkingAudit.walkOp (heat d j) x

/-- The truncated Green function `g_m(x) = ∑_{j<m} P^j(0, x)`. -/
def green (d : ℕ) (m : ℕ) (x : Site d) : ℝ :=
  ∑ j ∈ Finset.range m, heat d j x

/-- `K` is a finite-range translation-invariant stochastic kernel of range `r`. -/
def IsLatticeKernel {d : ℕ} (r : ℕ) (K : Site d → Site d → ℝ) : Prop :=
  (∀ y x, 0 ≤ K y x) ∧
  (∀ y x, K y x ≠ 0 → supNorm (x - y) ≤ r) ∧
  (∀ y, ∑ x ∈ boxFinset y r, K y x = 1) ∧
  (∀ v y x, K (y + v) (x + v) = K y x)

/-- `(K f)(x) = ∑_y K(x, y) f(y)`. -/
def kOp {d : ℕ} (r : ℕ) (K : Site d → Site d → ℝ) (f : Site d → ℝ) (x : Site d) : ℝ :=
  ∑ y ∈ boxFinset x r, K x y * f y

/-- `K^j(0, x)`. -/
def kIter {d : ℕ} (r : ℕ) (K : Site d → Site d → ℝ) : ℕ → Site d → ℝ
  | 0 => fun x => if x = 0 then 1 else 0
  | j + 1 => fun x => ∑ y ∈ boxFinset x r, kIter r K j y * K y x

/-- The truncated Green function `g^K_n(z) = ∑_{j<n} K^j(0, z)`. -/
def kGreen {d : ℕ} (r : ℕ) (K : Site d → Site d → ℝ) (n : ℕ) (z : Site d) : ℝ :=
  ∑ j ∈ Finset.range n, kIter r K j z

/-- The solution of `v_0 = 0`, `v_{n+1} = (η + K v_n)⁺`. -/
def kSol {d : ℕ} (r : ℕ) (K : Site d → Site d → ℝ) (η : Site d → ℝ) : ℕ → Site d → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => max 0 (η x + kOp r K (kSol r K η n) x)

/-- The `l^2` norm of a function on the lattice. -/
def l2Norm {d : ℕ} (f : Site d → ℝ) : ℝ := Real.sqrt (∑' x : Site d, f x ^ 2)

/-- The sup norm of a function on the lattice. -/
def supAbs {d : ℕ} (f : Site d → ℝ) : ℝ := ⨆ x : Site d, |f x|

/-- `max_x g_n(x)` for the simple random walk. -/
def greenMax (d : ℕ) (n : ℕ) : ℝ := ⨆ x : Site d, green d n x

/-- `|R_t|`, the number of distinct sites visited by time `t`. -/
def rangeCard {d : ℕ} (x : Site d) (p : ℕ → Fin d × Bool) (t : ℕ) : ℕ :=
  ((Finset.range (t + 1)).image fun j => walkPath x p j).card

/-- A test function on `R^d`. -/
def IsTestFun {d : ℕ} (φ : (Fin d → ℝ) → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ

/-- A test function on `(0,∞) × R^d`. -/
def IsSpaceTimeTest {d : ℕ} (ψ : ℝ × (Fin d → ℝ) → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ ∀ p ∈ tsupport ψ, 0 < p.1

/-- The Laplacian of a smooth function on `R^d`. -/
def lap {d : ℕ} (φ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, deriv (fun s => deriv (fun t => φ (Function.update x i t)) s) (x i)

/-- `L = (2d)^{-1}Δ`. -/
def contOp (d : ℕ) (φ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ := lap φ x / (2 * d)

/-- `W` is a mean-zero spatial white noise of intensity `v`. -/
def IsSpatialWhiteNoise (d : ℕ) (v : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ) : Prop :=
  (∀ φ ψ : (Fin d → ℝ) → ℝ, IsTestFun φ → IsTestFun ψ → ∀ a b : ℝ,
      W (fun x => a * φ x + b * ψ x) =ᵐ[μ] fun ω => a * W φ ω + b * W ψ ω) ∧
  (∀ φ, IsTestFun φ → Integrable (W φ) μ ∧ ∫ ω, W φ ω ∂μ = 0) ∧
  (∀ φ ψ, IsTestFun φ → IsTestFun ψ →
      Integrable (fun ω => W φ ω * W ψ ω) μ ∧
      ∫ ω, W φ ω * W ψ ω ∂μ = v * ∫ x, φ x * ψ x) ∧
  (∀ φ, IsTestFun φ → ∃ s : NNReal, (s : ℝ) = v * ∫ x, φ x ^ 2 ∧
      μ.map (W φ) = ProbabilityTheory.gaussianReal 0 s)

/-- The coordinatewise floor `⌊Rx⌋`. -/
def latticePoint {d : ℕ} (R : ℝ) (x : Fin d → ℝ) : Site d := fun i => ⌊R * x i⌋

/-- `R^{d/2-2}u_{⌊sR^2⌋}(⌊Rx⌋)`. -/
def barDivisible {d : ℕ} (ω : Data d) (R : ℝ) (s : ℝ) (x : Fin d → ℝ) : ℝ :=
  R ^ ((d : ℝ) / 2 - 2) * uOf ω ⌊s * R ^ 2⌋₊ (latticePoint R x)

/-- `⟨η_R, φ⟩ = R^{-d/2}∑_y η(y)φ(y/R)`. -/
def scenePair {d : ℕ} (ω : Data d) (R : ℝ) (φ : (Fin d → ℝ) → ℝ) : ℝ :=
  R ^ (-(d : ℝ) / 2) * ∑' y : Site d, (ω.1 y : ℝ) * φ fun i => (y i : ℝ) / R

end

end Walk

end ParkingAudit

section Kernels

open MeasureTheory

namespace ParkingAudit.External

/-- **The Brownian heat kernel**, BP's equation (14): `p_t^{BM}(x,y) = (4πt/(2d))^{-d/2}
exp(-d|x-y|²/(2t))`, for the Brownian motion on `ℝ^d` with generator `(2d)^{-1}Δ`. -/
noncomputable def contHeatKernel (d : ℕ) (t : ℝ) (x y : Fin d → ℝ) : ℝ :=
  (4 * Real.pi * t / (2 * d)) ^ (-(d : ℝ) / 2) *
    Real.exp (-(d : ℝ) * (∑ i, (x i - y i) ^ 2) / (2 * t))

end ParkingAudit.External

/-- **The finite-time Brownian Green kernel**, BP's `g_t^{BM}(x,y) = ∫₀^t p_a^{BM}(x,y) da`
(equation (14)-(19), page 17). -/
noncomputable def ParkingAudit.External.contFiniteGreen (d : ℕ) (t : ℝ) (x y : Fin d → ℝ) : ℝ :=
  ∫ a in Set.Ioc (0 : ℝ) t, ParkingAudit.External.contHeatKernel d a x y

end Kernels

namespace ParkingAudit

section Continuum

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

/-- The Green field is obtained from the same noise by its continuous linear
extension to spatial `L²`. The norm identity is the white-noise isometry at
intensity `v`. Agreement with test coordinates determines the extension, since
smooth compactly supported functions are dense in spatial `L²`.

Both agreements are coordinatewise almost everywhere. In particular the Green
kernel is used as an `L²` equivalence class, independently of its diagonal value,
and `Z` may be a continuous modification of the resulting random variables. -/
def IsSpatialGreenPairing (d : ℕ) (v : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure Ω) (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ)
    (Z : Ω → ℝ → (Fin d → ℝ) → ℝ) : Prop :=
  ∃ I : Lp ℝ 2 (volume : Measure (Fin d → ℝ)) →L[ℝ] Lp ℝ 2 Q,
    (∀ f, ‖I f‖ = Real.sqrt v * ‖f‖) ∧
    (∀ φ, IsTestFun φ → ∃ hφ : MemLp φ 2 volume,
      (I (hφ.toLp φ) : Ω → ℝ) =ᵐ[Q] W φ) ∧
    (∀ t x, 0 ≤ t → ∃ hg : MemLp (External.contFiniteGreen d t x) 2 volume,
      (I (hg.toLp (External.contFiniteGreen d t x)) : Ω → ℝ) =ᵐ[Q]
        fun ω => Z ω t x)

/-- **The Brownian motion of the directed scaling limit**: `Var(B_t) = t/4` and
`B_0 = 0`, which is exactly the statement that `2B` is a standard real Brownian
motion. -/
def IsQuarterBrownian {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) : Prop :=
  IsBrownianReal (fun t ω => 2 * B t ω) P

/-- Galmarino's criterion: `τ` is a stopping time of the natural filtration of
`B`.  If `τ` takes the value `t` at a path and a second path agrees with it up
to time `t`, then `τ` takes the value `t` there too. -/
def IsContStopping {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) : Prop :=
  ∀ (t : ℝ≥0) (ω ω' : Ω), τ ω = t → (∀ s ≤ t, B s ω = B s ω') → τ ω' = t

/-- The payoffs `E_0 G(τ, B_τ)` attained by the stopping times of `B` bounded by
`T`.  The first argument of `G` is the elapsed time.

The payoff of a rule counts only when it exists.  Galmarino's criterion does not
make `τ` measurable, so for a general rule the integrand need not be
measurable and the Bochner integral is then the junk value zero; a supremum
over those junk values would be at least zero whatever the reward, and would
exceed the value of the problem whenever every genuine payoff is negative.
The definition therefore conjoins integrability. -/
def contPayoffs {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB)
    (G : ℝ → ℝ → ℝ) (T : ℝ) : Set ℝ :=
  {a : ℝ | ∃ τ : ΩB → ℝ≥0, IsContStopping B τ ∧ (∀ β, (τ β : ℝ) ≤ T) ∧
    Integrable (fun β => G (τ β) (B (τ β) β)) PB ∧
    a = ∫ β, G (τ β) (B (τ β) β) ∂PB}

/-- `sup_{τ ≤ T} E_0 G(τ, B_τ)`, the Brownian optimal-stopping value at the
reward `G`. -/
def contValue {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB)
    (G : ℝ → ℝ → ℝ) (T : ℝ) : ℝ :=
  sSup (contPayoffs B PB G T)

/-- **Galmarino's criterion**, for a stopping time of a `(Fin d → ℝ)`-valued process: if `τ`
takes the value `t` at a path and a second path agrees with it up to time `t`, then `τ` takes
the value `t` there too.  The `Fin d`-dimensional analogue of `ParkingAudit.IsContStopping`
(`Parking/Support/ContOrientedLimit.lean`), which is hard-wired to a real-valued process. -/
def IsSpatialContStopping {Ω : Type*} {d : ℕ} (B : ℝ≥0 → Ω → (Fin d → ℝ)) (τ : Ω → ℝ≥0) :
    Prop :=
  ∀ (t : ℝ≥0) (ω ω' : Ω), τ ω = t → (∀ s ≤ t, B s ω = B s ω') → τ ω' = t

/-- The payoffs `E_0 G(τ, B_τ)` attained by the stopping times of `B` bounded by `T`, for a
`(Fin d → ℝ)`-valued driving process.  The first argument of `G` is the elapsed time.

The payoff of a rule counts only when it exists: Galmarino's criterion does not make `τ`
measurable, so for a general rule the integrand need not be measurable and the Bochner
integral is then the junk value zero; the definition therefore conjoins
integrability, exactly as `ParkingAudit.contPayoffs` does for the one-dimensional case. -/
def spatialContPayoffs {d : ℕ} {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → (Fin d → ℝ))
    (PB : Measure ΩB) (G : ℝ → (Fin d → ℝ) → ℝ) (T : ℝ) : Set ℝ :=
  {a : ℝ | ∃ τ : ΩB → ℝ≥0, IsSpatialContStopping B τ ∧ (∀ β, (τ β : ℝ) ≤ T) ∧
    Integrable (fun β => G (τ β) (B (τ β) β)) PB ∧
    a = ∫ β, G (τ β) (B (τ β) β) ∂PB}

/-- `sup_{τ ≤ T} E_0 G(τ, B_τ)`, the Brownian optimal-stopping value at the reward `G`, for a
`(Fin d → ℝ)`-valued driving process. -/
def spatialContValue {d : ℕ} {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → (Fin d → ℝ))
    (PB : Measure ΩB) (G : ℝ → (Fin d → ℝ) → ℝ) (T : ℝ) : ℝ :=
  sSup (spatialContPayoffs B PB G T)

/-- **The driving process of a `ParkingAudit.IsBrownianSpace`, read in the paper's own
`Fin d → ℝ` vocabulary.** -/
def ofBrownianSpace {d : ℕ} {Ω : Type*} (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) :
    ℝ≥0 → Ω → (Fin d → ℝ) :=
  fun t ω => (EuclideanSpace.equiv (Fin d) ℝ) (B t ω)

section

variable {d : ℕ} {Ω' : Type}

/-- **The continuum spatial value field.** `Z`'s own value at `(s,x)` plus the Brownian
optimal-stopping value, at the reward `k y ↦ -Z ω' (s-k) (x+y)`, started at the origin and
bounded by the horizon `s`. -/
def contUc {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → (Fin d → ℝ)) (PB : Measure ΩB)
    (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ) (ω' : Ω') (s : ℝ) (x : Fin d → ℝ) : ℝ :=
  Z ω' s x + spatialContValue B PB (fun k y => -Z ω' (s - k) (x + y)) s

end

end

end Continuum

section Oriented

open MeasureTheory

noncomputable section

/-- The binomial law of `l` trials and success probability `1/2`, extended by
zero to the integers. -/
def binomLaw (l : ℕ) (j : ℤ) : ℝ :=
  (if 0 ≤ j then (Nat.choose l j.toNat : ℝ) else 0) / 2 ^ l

section

variable {d : ℕ}

/-- A walk in the negative coordinate directions, using the coordinate of
each uniform signed direction. -/
def orientedPath (x : Site d) (p : ℕ → Fin d × Bool) : ℕ → Site d
  | 0 => x
  | j + 1 => orientedPath x p j - unit (p j).1

/-- `E_x F(σ, X_σ)`, the expected terminal reward of the oriented stopping rule
`σ`.  The first argument of `F` is the elapsed time. -/
def orientedTerminalValue (F : ℕ → Site d → ℝ) (x : Site d)
    (σ : (ℕ → Fin d × Bool) → ℕ) : ℝ :=
  ∫ p, F (σ p) (orientedPath x p (σ p)) ∂(walkLaw d)

/-- The set of expected terminal rewards of the oriented stopping rules bounded
by `n`. -/
def orientedTerminalValues (d : ℕ) (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d) : Set ℝ :=
  {a | ∃ σ, IsStoppingTimeLE n σ ∧ a = orientedTerminalValue F x σ}

/-- `sup_{σ ≤ n} E_x F(σ, X_σ)`, the value of the oriented stopping problem with
terminal reward `F`. -/
def orientedStoppingSup (d : ℕ) (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d) : ℝ :=
  sSup (orientedTerminalValues d F n x)

end

/-- The rescaled spatial coordinate `(j - ℓ/2)/√n = (z₂ - z₁)/(2√n)` of a site
of `ℤ²` at scale `n`. -/
def orientedScaledSite (n : ℕ) (z : Site 2) : ℝ :=
  ((z 1 : ℝ) - (z 0 : ℝ)) / (2 * Real.sqrt n)

end

end Oriented

section Near

open MeasureTheory
open scoped ENNReal

/-- The rate of Theorem 1.7. -/
noncomputable def nearRate (d : ℕ) (δ : ℝ) : ℝ :=
  if d = 1 then δ ^ (-(3 : ℝ))
  else if d = 2 then δ⁻¹
  else if d = 3 then δ ^ (-(1 : ℝ) / 3)
  else Real.log (Real.exp 1 / δ)

end Near

end ParkingAudit

section ThreePoint

open MeasureTheory

/-- The three-point law `P(±1) = p`, `P(0) = 1 - 2p` on `ℤ`. -/
noncomputable def ParkingAudit.threePointLaw (p : ℝ) : Measure ℤ :=
  ENNReal.ofReal p • Measure.dirac 1 + ENNReal.ofReal p • Measure.dirac (-1) +
    ENNReal.ofReal (1 - 2 * p) • Measure.dirac 0

end ThreePoint

/-! ## 5. The critical-scale model of the cited lower-tail estimate

Copied from `Parking/Support/NearestCriticalModel.lean`. -/

section CriticalScale

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
namespace ParkingAudit.CriticalScale

def relax {d : ℕ} (σ u : Site d → ℝ) (x : Site d) : ℝ :=
  max 0 ((σ x - 1 + nbrSum u x) / (2 * d))
def odometer {d : ℕ} (σ : Site d → ℝ) : ℕ → Site d → ℝ
  | 0 => fun _ => 0
  | t + 1 => relax σ (odometer σ t)
def centeredMassLaw (d : ℕ) (ν : Measure ℝ) : Measure (Site d → ℝ) :=
  ParkingAudit.iidLaw d (ν.map fun z => 1 + 2 * (d : ℝ) * z)

/-- The `k`-step transition probability `p_k(x, y)` of simple random walk.
Reuses `ParkingAudit.LocalCLT.heatKernel`. -/
abbrev heatKernel (d : ℕ) : ℕ → Site d → Site d → ℝ :=
  ParkingAudit.LocalCLT.heatKernel d

/-- The finite-time Green kernel `g_t(x, y) = ∑_{k<t} p_k(x, y)`.
Reuses `ParkingAudit.greenTime`. -/
abbrev greenTime (d : ℕ) (t : ℕ) (x y : Site d) : ℝ :=
  ParkingAudit.greenTime d t x y

/-- The `d`-dependent rate on the right of `eq:Qt-table`
(`sandpile.tex:1186-1195`): `t^{3/2}` in dimension one, `t` in dimension two,
`t^{1/2}` in dimension three, `\log t` in dimension four, and `1` in dimensions
five and above.  The final branch is the paper's `d\geq5` case; the frozen
statement binds `1 \leq d`, so the branch is reached only there. -/
def varianceRate (d : ℕ) (t : ℕ) : ℝ :=
  if d = 1 then (t : ℝ) ^ ((3 : ℝ) / 2)
  else if d = 2 then (t : ℝ)
  else if d = 3 then (t : ℝ) ^ ((1 : ℝ) / 2)
  else if d = 4 then Real.log (t : ℝ)
  else 1

/-- The `d`-dependent rate on the right of `eq:corr-bound`
(`sandpile.tex:1206-1217`), with the constant `C` stripped off:
`(1+\log(n/m))\sqrt{m/n}` in dimension two, `\sqrt{(1+\log m)/(1+\log n)}` in
dimension four, and `(m/n)^{1/4}` in dimensions one and three, which the paper
gives the same case.  The final branch is that common case; the frozen
statement binds `1 \leq d` and `d \leq 4`, so it is reached only for
`d\in\{1,3\}`. -/
def corrRate (d : ℕ) (m n : ℕ) : ℝ :=
  if d = 2 then (1 + Real.log ((n : ℝ) / (m : ℝ))) * Real.sqrt ((m : ℝ) / (n : ℝ))
  else if d = 4 then Real.sqrt ((1 + Real.log (m : ℝ)) / (1 + Real.log (n : ℝ)))
  else ((m : ℝ) / (n : ℝ)) ^ ((1 : ℝ) / 4)

/-- The time window `\sum_{k=m}^{n-1}p_k(x,z)` of `eq:d4-window-l2` and
`eq:d4-window-linfty` (`sandpile.tex:1222-1232`), a finite sum over the steps
`k` with `m \leq k < n`. -/
def windowKernel (m n : ℕ) (x z : Site 4) : ℝ :=
  ∑ k ∈ Finset.Ico m n, heatKernel 4 k x z

/-- The covariance matrix `Σ` of the linear forms `Y_j = ∑_i a_i(j) ξ_i` when
the coordinates `ξ_i` are i.i.d. with one-site law `ν`:
`Σ_{jk} = \Var(ν)\sum_i a_i(j) a_i(k)`. -/
def gram {N m : ℕ} (ν : Measure ℝ) (a : Fin N → Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun j k => variance id ν * ∑ i, a i j * a i k

/-- `|a(i)|`, the Euclidean norm of the coefficient vector of the `i`-th
coordinate. -/
def coeffNorm {N m : ℕ} (a : Fin N → Fin m → ℝ) (i : Fin N) : ℝ :=
  Real.sqrt (∑ j, a i j ^ 2)

/-- The quadratic form `v ↦ ⟨Sv, v⟩` of a matrix, in which the paper's spectral
bound on `Σ` is transcribed. -/
def quadForm {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) : ℝ :=
  ∑ j, ∑ k, S j k * v j * v k

/-- The Berry--Esseen remainder of `eq:dlt4-green-lower-tail`: the factor that
multiplies `C` in the second summand, `(\log t)^{3/4}t^{-1/4}L^{a/4}` for
`d ∈ {1, 3}` and `(\log t)^{7/4}t^{-1/2}L^{a/2}` for `d = 2`. -/
def lowerTailRemainder (d : ℕ) (t : ℕ) (L a : ℝ) : ℝ :=
  if d = 2 then
    Real.log t ^ ((7 : ℝ) / 4) * (t : ℝ) ^ (-(1 : ℝ) / 2) * L ^ (a / 2)
  else
    Real.log t ^ ((3 : ℝ) / 4) * (t : ℝ) ^ (-(1 : ℝ) / 4) * L ^ (a / 4)

end ParkingAudit.CriticalScale

end

end CriticalScale

/-! ## 6. The cited results

Copied from `Parking/External/`.  Each is assumed, not proved, and enters a theorem
only as an explicit hypothesis. -/

section

open MeasureTheory ProbabilityTheory Filter Topology

/-- The mean sandpile odometer for a real i.i.d. field: this input allows the
field to be real valued, not only integer valued. -/
noncomputable def ParkingAudit.External.meanSandpileReal (d : ℕ) (ν : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ η, ParkingAudit.u η n 0 ∂(ParkingAudit.iidLaw d ν)

/-- Theorem 1.3, Corollary 6.2, Theorem 6.6 and equation (94) of the divisible
sandpile paper, as quoted in `parking.tex`. -/
def ParkingAudit.External.SandpileGrowth : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
    ∫ z, z ∂ν = 0 → 0 < evariance id ν → evariance id ν < ⊤ →
    (∃ θ : ℝ, 0 < θ ∧ Integrable (fun z => Real.exp (θ * |z|)) ν) →
    (d ≤ 3 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        c * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) ≤ ParkingAudit.External.meanSandpileReal d ν n ∧
          ParkingAudit.External.meanSandpileReal d ν n ≤ C * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) ∧
    (d = 4 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        c * Real.log n ≤ ParkingAudit.External.meanSandpileReal d ν n ∧
          ParkingAudit.External.meanSandpileReal d ν n ≤ C * Real.log n) ∧
    (5 ≤ d → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        c * (Real.log n) ^ ((2 : ℝ) / d) ≤ ParkingAudit.External.meanSandpileReal d ν n ∧
          ParkingAudit.External.meanSandpileReal d ν n ≤ C * Real.log (n + 1)) ∧
    (5 ≤ d → (∃ b : ℝ, ∀ᵐ z ∂ν, b ≤ z) → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        c * (Real.log n) ^ ((2 : ℝ) / d) ≤ ParkingAudit.External.meanSandpileReal d ν n ∧
          ParkingAudit.External.meanSandpileReal d ν n ≤ C * (Real.log n) ^ ((2 : ℝ) / d)) ∧
    (d ≤ 3 → ∃ L : ℝ, 0 < L ∧
        Tendsto (fun n : ℕ => (n : ℝ) ^ (-((4 - (d : ℝ)) / 4)) * ParkingAudit.External.meanSandpileReal d ν n)
          atTop (𝓝 L))

end

section

open MeasureTheory

/-- "Let $(\mathcal F_i)_{i=0}^k$ be a filtration, let $(\xi_i)_{i=1}^k$ be
martingale differences for it, let $r\geq2$, and let $a>0$.  If
$|\xi_i|\leq a$ for every $1\leq i\leq k$, then
$(\E|\sum\xi_i|^r)^{1/r}\leq C(\sqrt r(\E[\sum\E[\xi_i^2\mid\mathcal
F_{i-1}]]^{r/2})^{1/r}+ra)$, with $C$ universal.  If instead there is $v>0$
such that, almost surely, $\sum\E[|\xi_i|^q\mid\mathcal F_{i-1}]\leq
\frac{q!}2a^{q-2}v$ for every integer $q\geq2$, then
$(\E|\sum\xi_i|^r)^{1/r}\leq C(\sqrt{rv}+ra)$, again with $C$ universal." -/
def ParkingAudit.External.Bernstein : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (k : ℕ) (F : ℕ → MeasurableSpace Ω) (ξ : ℕ → Ω → ℝ) (r a : ℝ),
      Monotone F → (∀ i, F i ≤ ‹MeasurableSpace Ω›) →
      (∀ i, Measurable[F i] (ξ i)) → (∀ i, Integrable (ξ i) μ) →
      (∀ i, 1 ≤ i → i ≤ k → μ[ξ i | F (i - 1)] =ᵐ[μ] 0) →
      2 ≤ r → 0 < a →
      ((∀ i, 1 ≤ i → i ≤ k → ∀ ω, |ξ i ω| ≤ a) →
        (∫ ω, |∑ i ∈ Finset.Icc 1 k, ξ i ω| ^ r ∂μ) ^ (1 / r) ≤
          C * (Real.sqrt r *
              (∫ ω, (∑ i ∈ Finset.Icc 1 k, (μ[fun ω' => ξ i ω' ^ 2 | F (i - 1)]) ω) ^ (r / 2) ∂μ)
                ^ (1 / r)
            + r * a)) ∧
      (∀ v : ℝ, 0 < v → (∀ (i : ℕ) (q : ℕ), Integrable (fun ω => |ξ i ω| ^ q) μ) →
        (∀ q : ℕ, 2 ≤ q → ∀ᵐ ω ∂μ,
            ∑ i ∈ Finset.Icc 1 k, (μ[fun ω' => |ξ i ω'| ^ q | F (i - 1)]) ω
              ≤ (Nat.factorial q : ℝ) / 2 * a ^ (q - 2) * v) →
        (∫ ω, |∑ i ∈ Finset.Icc 1 k, ξ i ω| ^ r ∂μ) ^ (1 / r) ≤
          C * (Real.sqrt (r * v) + r * a))

end

section

open MeasureTheory

/-- "Let $K$ be a finite-range, translation-invariant transition kernel on
$\Z^d$.  Let $g_n^K(z)\coloneqq\sum_{j<n}K^j(0,z)$, and let $v_0=0$ and
$v_{n+1}=(\eta+Kv_n)^+$ for i.i.d. $\eta(x)$ satisfying
$\E e^{\theta|\eta(0)|}<\infty$ for some $\theta>0$.  Then there is $C<\infty$,
depending on $K$ and the law of $\eta(0)$, such that, for every $n\geq1$ and
$r\geq2$,
$(\E|v_n(0)-\E v_n(0)|^r)^{1/r}\leq C(\sqrt r\,\|g_n^K\|_2+r\|g_n^K\|_\infty)$." -/
def ParkingAudit.External.UConcentration : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (r : ℕ) (K : ParkingAudit.Site d → ParkingAudit.Site d → ℝ),
    ParkingAudit.IsLatticeKernel r K → ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
    ∀ θ : ℝ, 0 < θ → Integrable (fun z : ℝ => Real.exp (θ * |z|)) ν →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ q : ℝ, 2 ≤ q →
      (∫ η, |ParkingAudit.kSol r K η n 0
            - ∫ η', ParkingAudit.kSol r K η' n 0 ∂(ParkingAudit.iidLaw d ν)| ^ q
          ∂(ParkingAudit.iidLaw d ν)) ^ (1 / q)
        ≤ C * (Real.sqrt q * ParkingAudit.l2Norm (ParkingAudit.kGreen r K n)
            + q * ParkingAudit.supAbs (ParkingAudit.kGreen r K n))

end

section

open MeasureTheory

noncomputable section

namespace ParkingAudit.External

/-- The rate of `‖g_n‖₂` in `eq:green-norms`: `n^{3/4}`, `n^{1/2}`, `n^{1/4}`,
`√(log n)` and `1` in dimensions one, two, three, four and five upward. -/
def greenL2Rate (d : ℕ) (n : ℕ) : ℝ :=
  if d = 1 then (n : ℝ) ^ ((3 : ℝ) / 4)
  else if d = 2 then (n : ℝ) ^ ((1 : ℝ) / 2)
  else if d = 3 then (n : ℝ) ^ ((1 : ℝ) / 4)
  else if d = 4 then Real.sqrt (Real.log n)
  else 1

/-- The rate of `max_x g_n(x)` in `eq:green-norms`: `n^{1/2}`, `log n` and `1`
in dimensions one, two and three upward. -/
def greenMaxRate (d : ℕ) (n : ℕ) : ℝ :=
  if d = 1 then (n : ℝ) ^ ((1 : ℝ) / 2)
  else if d = 2 then Real.log n
  else 1

end ParkingAudit.External

/-- "The Green estimates collected in \\citet[Section~3.1]{BP} give
$\\|g_n\\|_2\\asymp n^{3/4}\\ (d=1)$, $n^{1/2}\\ (d=2)$, $n^{1/4}\\ (d=3)$,
$\\sqrt{\\log n}\\ (d=4)$, $1\\ (d\\geq5)$, and
$\\max_xg_n(x)\\asymp n^{1/2}\\ (d=1)$, $\\log n\\ (d=2)$, $1\\ (d\\geq3)$."

Each of the two relations `≍` carries its own pair of constants, as the paper's
two displays do, and each holds on the range `n ≥ 2` in which the paper reads
them.  Both quantities and both rates are positive and finite at every `n ≥ 2`,
so this is the same assertion as the one for all large `n`. -/
def ParkingAudit.External.GreenNorms : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        c * ParkingAudit.External.greenL2Rate d n ≤ ParkingAudit.l2Norm (ParkingAudit.green d n) ∧
          ParkingAudit.l2Norm (ParkingAudit.green d n) ≤ C * ParkingAudit.External.greenL2Rate d n) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        c * ParkingAudit.External.greenMaxRate d n ≤ ParkingAudit.greenMax d n ∧
          ParkingAudit.greenMax d n ≤ C * ParkingAudit.External.greenMaxRate d n)

end

end

section

open MeasureTheory

/-- "By the Donsker--Varadhan estimate for the range, the logarithm of the
expectation on the right is asymptotic to $-kt^{d/(d+2)}$ for some $k>0$."
Here the expectation is $\E_0e^{-a|R_t|}$, the average over the walk from the
origin alone of `Real.exp (-(a * |R_t|))`. -/
def ParkingAudit.External.DonskerVaradhanRange : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ a : ℝ, 0 < a →
    ∃ k : ℝ, 0 < k ∧
      Filter.Tendsto
        (fun t : ℕ =>
          Real.log (∫ p, Real.exp (-(a * (ParkingAudit.rangeCard (0 : ParkingAudit.Site d) p t : ℝ)))
              ∂(ParkingAudit.walkLaw d)) / (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))
        Filter.atTop (nhds (-k))

end

section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- BouRabeePanagiotis2026's Theorem 1.3(i)(b) (`sandpile.tex:206-235`, `thm:main-explosion`):
the parabolic scaling limit of the rescaled divisible odometer is a Brownian optimal-stopping
value driven by a spatial white noise, jointly, with the time variable and scenery retained
(the strengthening `parking.tex:1755-1759` cites for Step 1 of `prop:spatial-scaling`). -/
def ParkingAudit.External.SpatialOdometerScaling : Prop :=
  ∀ (d : ℕ), 1 ≤ d → d ≤ 3 → ∀ (ν : Measure ℤ), ParkingAudit.CriticalLaw ν →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
      (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ)
      (Z : Ω → ℝ → (Fin d → ℝ) → ℝ)
      (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ),
      ParkingAudit.IsSpatialWhiteNoise d (variance (fun k : ℤ => (k : ℝ)) ν) Q W ∧
      (∀ φ, ParkingAudit.IsTestFun φ → Measurable (W φ)) ∧
      ParkingAudit.IsSpatialGreenPairing d (variance (fun k : ℤ => (k : ℝ)) ν) Q W Z ∧
      (∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Z ω p.1 p.2) ∧
      (∀ ω x, Uc ω 0 x = 0) ∧
      (∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2) ∧
      (∀ ω x, Monotone fun s => Uc ω s x) ∧
      (∀ s x, Measurable fun ω => Uc ω s x) ∧
      (∃ (ΩB : Type) (_ : MeasurableSpace ΩB) (PB : Measure ΩB)
          (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)),
        ParkingAudit.IsBrownianSpace d 0 B PB ∧
        ∀ ω T x, 0 ≤ T →
          Uc ω T x = ParkingAudit.contUc (ParkingAudit.ofBrownianSpace B) PB Z ω T x) ∧
      (∀ (m p' : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (sp : Fin p' → ℝ × (Fin d → ℝ)),
        (∀ i, ParkingAudit.IsTestFun (φ i)) → (∀ j, 0 < (sp j).1) →
        ∀ F : BoundedContinuousFunction ((Fin m → ℝ) × (Fin p' → ℝ)) ℝ,
          Tendsto (fun R : ℝ =>
              ∫ w : ParkingAudit.Data d,
                F (fun i => ParkingAudit.scenePair w R (φ i),
                  fun j => ParkingAudit.barDivisible w R (sp j).1 (sp j).2) ∂(ParkingAudit.law d ν))
            atTop
            (𝓝 (∫ ω, F (fun i => W (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2) ∂Q))) ∧
      (∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → (∀ p ∈ K, 0 < p.1) → ∀ ε : ℝ, 0 < ε →
        ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
          ((ParkingAudit.law d ν) {w | ε < ⨆ p ∈ K, ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ,
              |ParkingAudit.barDivisible w R p.1 p.2 - ParkingAudit.barDivisible w R q.1 q.2|}).toReal
            ≤ ε')

end

section

open MeasureTheory

noncomputable section

/-- The hypoelliptic (Weyl-type) interior regularity theorem for the heat operator
`(2d)^{-1}Δ`: standard classical parabolic PDE, uncited by the paper (`parking.tex:1800-1820`,
Step 3 of the proof of `prop:spatial-scaling`).  A continuous function
that solves `∂_s u = (2d)^{-1}Δu` in the sense of distributions on an open set, tested against
every space-time test function supported there, is represented on that set by a function smooth
there and solving the equation classically. -/
def ParkingAudit.External.HeatInteriorRegularity : Prop :=
  ∀ (d : ℕ) (U : Set (ℝ × (Fin d → ℝ))), IsOpen U →
    U ⊆ {p : ℝ × (Fin d → ℝ) | 0 < p.1} →
    ∀ u : ℝ × (Fin d → ℝ) → ℝ, Continuous u →
      (∀ ψ : ℝ × (Fin d → ℝ) → ℝ, ParkingAudit.IsSpaceTimeTest ψ → tsupport ψ ⊆ U →
        -∫ p : ℝ × (Fin d → ℝ), u p * deriv (fun s => ψ (s, p.2)) p.1
          = ∫ p : ℝ × (Fin d → ℝ), u p * ParkingAudit.contOp d (fun x => ψ (p.1, x)) p.2) →
      ∃ v : ℝ × (Fin d → ℝ) → ℝ,
        ContDiffOn ℝ (⊤ : ℕ∞) v U ∧
        (∀ p ∈ U, u p = v p) ∧
        (∀ p ∈ U, HasDerivAt (fun s => v (s, p.2))
          (ParkingAudit.contOp d (fun x => v (p.1, x)) p.2) p.1)

end

end

section

open MeasureTheory

noncomputable section

/-- The strong minimum principle for the heat operator `(2d)^{-1}Δ`, sign-adapted from the
usual strong maximum principle: standard classical parabolic PDE, uncited by the paper
(`parking.tex:1800-1820`, Step 4 of the proof of `prop:spatial-scaling`).  A smooth,
nonnegative classical solution on an open set that vanishes at a point
vanishes on every backward-in-time, space-fixed segment through that point which lies entirely
in the open set. -/
def ParkingAudit.External.HeatStrongMinimum : Prop :=
  ∀ (d : ℕ) (U : Set (ℝ × (Fin d → ℝ))), IsOpen U →
    ∀ v : ℝ × (Fin d → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v U →
      (∀ p ∈ U, 0 ≤ v p) →
      (∀ p ∈ U, HasDerivAt (fun s => v (s, p.2))
        (ParkingAudit.contOp d (fun x => v (p.1, x)) p.2) p.1) →
      ∀ s₀ : ℝ, ∀ x₀ : Fin d → ℝ, (s₀, x₀) ∈ U → v (s₀, x₀) = 0 →
      ∀ τ : ℝ, τ < s₀ → (Set.Ioc τ s₀ ×ˢ ({x₀} : Set (Fin d → ℝ))) ⊆ U →
      ∀ s ∈ Set.Ioc τ s₀, v (s, x₀) = 0

end

end

section

open MeasureTheory Filter Topology

noncomputable section

/-- Classical parabolic compactness for `(2d)⁻¹Δ`: a sequence of nonnegative smooth
heat solutions with uniformly bounded local `L¹` norms has a subsequence converging
locally uniformly to a smooth classical heat solution. This is the compactness
consequence of standard parabolic interior derivative estimates used in
`parking.tex:1800-1820`, Step 3 of `prop:spatial-scaling`. -/
def ParkingAudit.External.HeatCompactness : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (U : Set (ℝ × (Fin d → ℝ))), IsOpen U →
    ∀ f : ℕ → ℝ × (Fin d → ℝ) → ℝ,
      (∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (f n) U) →
      (∀ n p, p ∈ U → 0 ≤ f n p) →
      (∀ n p, p ∈ U → HasDerivAt (fun s => f n (s, p.2))
        (ParkingAudit.contOp d (fun x => f n (p.1, x)) p.2) p.1) →
      (∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → K ⊆ U →
        ∃ C : ℝ, ∀ n, IntegrableOn (f n) K ∧ (∫ p in K, ‖f n p‖) ≤ C) →
      ∃ (r : ℕ → ℕ) (v : ℝ × (Fin d → ℝ) → ℝ), StrictMono r ∧
        ContDiffOn ℝ (⊤ : ℕ∞) v U ∧
        (∀ p ∈ U, 0 ≤ v p) ∧
        (∀ p ∈ U, HasDerivAt (fun s => v (s, p.2))
          (ParkingAudit.contOp d (fun x => v (p.1, x)) p.2) p.1) ∧
        (∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → K ⊆ U →
          TendstoUniformlyOn (fun n => f (r n)) v atTop K)

end

end

section

open MeasureTheory ProbabilityTheory

/-- The finite-time variance scale `eq:Qt-table`, the membrane correlation bound
`eq:corr-bound`, and the dimension-four window and tail bounds
`eq:d4-window-l2`, `eq:d4-window-linfty` and `eq:d4-full-window-bounds` of
`ssec:green-estimates`, all in their scenery-free Green-kernel form.  Assumed,
not proved. -/
def ParkingAudit.External.VarianceScale : Prop :=
  (∀ d : ℕ, 1 ≤ d →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ t : ℕ, 2 ≤ t →
          c * ParkingAudit.CriticalScale.varianceRate d t ≤
              ∑' y : ParkingAudit.Site d, ParkingAudit.CriticalScale.greenTime d t 0 y ^ 2 ∧
            (∑' y : ParkingAudit.Site d, ParkingAudit.CriticalScale.greenTime d t 0 y ^ 2) ≤
              C * ParkingAudit.CriticalScale.varianceRate d t) ∧
  (∀ d : ℕ, 1 ≤ d → d ≤ 4 →
      ∃ C : ℝ, 0 < C ∧
        ∀ m n : ℕ, 1 ≤ m → m ≤ n →
          (∑' x : ParkingAudit.Site d,
              ParkingAudit.CriticalScale.greenTime d m 0 x * ParkingAudit.CriticalScale.greenTime d n 0 x) ≤
            C * ParkingAudit.CriticalScale.corrRate d m n *
              Real.sqrt (∑' x : ParkingAudit.Site d, ParkingAudit.CriticalScale.greenTime d m 0 x ^ 2) *
              Real.sqrt (∑' x : ParkingAudit.Site d, ParkingAudit.CriticalScale.greenTime d n 0 x ^ 2)) ∧
  (∃ C : ℝ, 0 < C ∧
      (∀ m n : ℕ, 1 ≤ m → m < n → ∀ x : ParkingAudit.Site 4,
          (∑' z : ParkingAudit.Site 4,
              ParkingAudit.CriticalScale.windowKernel m n x z ^ 2) ≤
            C * (1 + Real.log (((n : ℝ) + 2) / ((m : ℝ) + 2))) ∧
          ∀ z : ParkingAudit.Site 4,
            ParkingAudit.CriticalScale.windowKernel m n x z ≤ C / (m : ℝ)) ∧
      (∀ n : ℕ, 2 ≤ n → ∀ x : ParkingAudit.Site 4,
          (∑' z : ParkingAudit.Site 4, ParkingAudit.CriticalScale.greenTime 4 n x z ^ 2) ≤
            C * Real.log ((n : ℝ) + 2) ∧
          ∀ z : ParkingAudit.Site 4, ParkingAudit.CriticalScale.greenTime 4 n x z ≤ C))

end

section

open MeasureTheory ProbabilityTheory

/-- The multivariate Berry--Esseen comparison of `sandpile.tex:1770-1782`, in
the standardized form the proof of `thm:critical-toppling` applies: for an
i.i.d. mean-zero one-site law whose third absolute moment is at most `M` times
the `3/2` power of its variance, and coefficients `a` whose covariance matrix
`Σ` has quadratic form between `1-δ` and `1+δ`, the law of the linear forms
`Y_j = ∑_i a_i(j) ξ_i` and the centred Gaussian with covariance `Σ` assign
probabilities to the orthant `{y_j ≤ h_j}` differing by at most
`C m^{1/4} \Var(ν)^{3/2} ∑_i |a(i)|³`.  Assumed, not proved. -/
def ParkingAudit.External.MultivariateBerryEsseen : Prop :=
  ∀ M δ : ℝ, 0 < M → 0 < δ → δ < 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N m : ℕ), 1 ≤ m →
        ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
          ∫ z, z ∂ν = 0 → 0 < variance id ν →
          Integrable (fun z => |z| ^ 3) ν →
          ∫ z, |z| ^ 3 ∂ν ≤ M * variance id ν ^ ((3 : ℝ) / 2) →
          ∀ a : Fin N → Fin m → ℝ,
            (∀ v : Fin m → ℝ,
              (1 - δ) * ∑ j, v j ^ 2 ≤
                  ParkingAudit.CriticalScale.quadForm
                    (ParkingAudit.CriticalScale.gram ν a) v ∧
                ParkingAudit.CriticalScale.quadForm
                    (ParkingAudit.CriticalScale.gram ν a) v ≤
                  (1 + δ) * ∑ j, v j ^ 2) →
            ∀ h : Fin m → ℝ,
              |((Measure.pi fun _ : Fin N => ν)
                      {ξ | ∀ j, ∑ i, a i j * ξ i ≤ h j}).toReal -
                  (multivariateGaussian 0
                      (ParkingAudit.CriticalScale.gram ν a)
                      {y | ∀ j, y j ≤ h j}).toReal| ≤
                C * (m : ℝ) ^ ((1 : ℝ) / 4) * variance id ν ^ ((3 : ℝ) / 2) *
                  ∑ i, ParkingAudit.CriticalScale.coeffNorm a i ^ 3

end

section

open MeasureTheory ProbabilityTheory Filter Topology

/-- The critical-scale lower tail estimate of Bou-Rabee and Panagiotis,
`sandpile.tex:1696-1720`, cited at `parking.tex:1822-1848`. -/
def ParkingAudit.External.CriticalScaleLowerTail : Prop :=
  ParkingAudit.External.VarianceScale → ParkingAudit.External.MultivariateBerryEsseen →
  ∀ (d : ℕ) (_hd : 1 ≤ d) (_hd3 : d ≤ 3) (ν₀ M : ℝ) (_hν₀ : 0 < ν₀)
    (a : ℝ) (_ha : 0 < a) (_ha' : a < 4 / (4 - (d : ℝ))),
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → 0 < evariance id ν → evariance id ν < ⊤ →
      Integrable (fun z => |z| ^ 3) ν →
      ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
      ∫ z, |z| ^ 3 ∂ν ≤ M * variance id ν ^ ((3 : ℝ) / 2) →
      ∀ (t : ℕ) (L : ℝ), 3 ≤ t → 2 ≤ L → L ^ a ≤ (t : ℝ) / 2 →
        ParkingAudit.CriticalScale.centeredMassLaw d ν
            {σ | ParkingAudit.CriticalScale.odometer σ t 0 ≤ (t : ℝ) ^ ((4 - (d : ℝ)) / 4) / L} ≤
          ENNReal.ofReal (C * L ^ (-c) + C * ParkingAudit.CriticalScale.lowerTailRemainder d t L a)

end

section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

/-- Stability of optimal-stopping values under uniform convergence of uniformly
bounded rewards, with the invariance principle for the stopped oriented walk
(`parking.tex:3214-3218`; the cutoff and stability estimates of the parabolic
scaling limit in the cited companion paper, of the kind of Coquet-Toldo,
Theorem 3 and Corollary 4).  Assumed, not proved. -/
def ParkingAudit.External.OrientedStoppingStability : Prop :=
  ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
      (B : ℝ≥0 → ΩB → ℝ), ParkingAudit.IsQuarterBrownian B PB →
    ∀ T : ℝ, 0 < T →
      (∀ (m : ℕ) (ts : Fin m → ℝ), (∀ i, ts i ∈ Set.Icc (0 : ℝ) T) →
        ∀ F : BoundedContinuousFunction (Fin m → ℝ) ℝ,
          Tendsto (fun n : ℕ =>
              ∫ p, F (fun i => ParkingAudit.orientedScaledSite n
                  (ParkingAudit.orientedPath (0 : ParkingAudit.Site 2) p ⌊(n : ℝ) * ts i⌋₊))
                ∂(ParkingAudit.walkLaw 2)) atTop
            (𝓝 (∫ β, F (fun i => B (Real.toNNReal (ts i)) β) ∂PB))) →
    ∀ M : ℝ, 0 ≤ M →
    ∀ G : ℝ → ℝ → ℝ, Continuous (fun p : ℝ × ℝ => G p.1 p.2) →
      (∀ s y : ℝ, |G s y| ≤ M) →
    ∀ G' : ℕ → ℝ → ℝ → ℝ, (∀ (n : ℕ) (s y : ℝ), |G' n s y| ≤ M) →
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : ℝ, |G' n s y - G s y| ≤ ε) →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |ParkingAudit.orientedStoppingSup 2
            (fun (k : ℕ) (z : ParkingAudit.Site 2) =>
              G' n ((k : ℝ) / n) (ParkingAudit.orientedScaledSite n z))
            ⌊(n : ℝ) * T⌋₊ (0 : ParkingAudit.Site 2) -
          ParkingAudit.contValue B PB G T| ≤ ε

end

section

open MeasureTheory

/-- The local central limit theorem for the simple symmetric walk on `ℤ`, with
the error `C/m` uniform in the endpoint, in the form cited at
`parking.tex:3207-3218`. -/
def ParkingAudit.External.BinomialLocalCLT : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ j : ℤ, (j - (m : ℤ)) % 2 = 0 →
    |Real.sqrt (m : ℝ) * ParkingAudit.binomLaw m ((j + (m : ℤ)) / 2)
        - 2 * (Real.exp (-((j : ℝ) / Real.sqrt (m : ℝ)) ^ 2 / 2) /
            Real.sqrt (2 * Real.pi))| ≤ C / (m : ℝ)

end

-- VOCABULARY-END

namespace ParkingAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Theorem 1.6 (`thm:nearest-counterexample`). -/
theorem nearest_counterexample (hBernstein : External.Bernstein) (d : ℕ)
    (hd : 5 ≤ d) :
    ∃ p : ℝ, 0 < p ∧ p < 1 / 2 ∧ ∃ c : ℝ, 0 < c ∧
      c ≤ liminf (fun t : ℕ =>
        ((law d (threePointLaw p)) {ω | HoleCloser ω t}).toReal) atTop := by
  sorry

end ParkingAudit
