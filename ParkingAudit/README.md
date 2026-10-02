# Audit Comparator Surface

This directory contains Mathlib-only comparator challenges for the eight main
theorems of the formalization of *Sharpness and critical scaling of parking*
(Bou-Rabee and Panagiotis, arXiv:2609.02820): Theorems 1.1, 1.2 and 1.4 to 1.8
and Corollary 1.3.  Each comparator lives in its own subdirectory:

| Directory | Paper statement | Checked theorem | Library theorem |
| --- | --- | --- | --- |
| `SubcriticalTail/` | Theorem 1.1, `thm:subcritical-tail` | `ParkingAudit.subcritical_tail` | `Parking.subcritical_tail` |
| `Master/` | Theorem 1.2, `thm:master` | `ParkingAudit.master` | `Parking.master` |
| `Growth/` | Corollary 1.3, `cor:growth` | `ParkingAudit.growth` | `Parking.growth` |
| `Trichotomy/` | Theorem 1.4, `thm:trichotomy` | `ParkingAudit.trichotomy` | `Parking.trichotomy` |
| `Nearest/` | Theorem 1.5, `thm:nearest` | `ParkingAudit.nearest` | `Parking.nearest` |
| `NearestCounterexample/` | Theorem 1.6, `thm:nearest-counterexample` | `ParkingAudit.nearest_counterexample` | `Parking.nearest_counterexample` |
| `Near/` | Theorem 1.7, `thm:near` | `ParkingAudit.near` | `Parking.near` |
| `OrientedWalk/` | Theorem 1.8, `thm:oriented-walk` | `ParkingAudit.oriented_walk` | `Parking.oriented_walk` |

Each `Challenge.lean` imports only `Mathlib`, rebuilds from scratch every
definition needed to read the theorem, states the theorem, and ends with one
`sorry`, the proof being checked.  The definitions form one vocabulary block,
between `-- VOCABULARY-BEGIN` and `-- VOCABULARY-END`, byte-identical in all
eight challenges: the lattice, i.i.d. fields and the particle–hole process with
its state, its odometer, its active particles and its unfilled holes; the
parking law, the two odometers `U` and `u` and their means; the walk, its range,
lattice kernels and Green functions; the continuum objects of the scaling
limits (test functions, the heat operator, spatial white noise and its Green
pairing, Brownian optimal-stopping values); the oriented walk and its stopping
problem; the critical-scale model of the cited lower-tail estimate; and the
eight cited results the eight theorems use.

## What Is Checked

The theorems are conditional on results the paper cites without proof, and so
are the challenges: each carries, as explicit hypotheses, the cited results
its library theorem uses, restated in the vocabulary.

| Directory | Cited results carried as hypotheses |
| --- | --- |
| `SubcriticalTail/` | `External.DonskerVaradhanRange` |
| `Master/`, `Growth/`, `Trichotomy/` | `External.SandpileGrowth`, `External.Bernstein` |
| `Nearest/` | the same two, `External.SpatialOdometerScaling`, `External.HeatInteriorRegularity`, `External.HeatCompactness`, `External.MultivariateBerryEsseen` |
| `NearestCounterexample/` | `External.Bernstein` |
| `Near/` | `External.SandpileGrowth`, `External.Bernstein` |
| `OrientedWalk/` | `External.Bernstein`, `External.OrientedStoppingStability` |

The certified statements of Theorems 1.4 and 1.7 also carry the optimal
stopping representation `Parking.External.Stopping`.  The repository proves it
(`Parking.External.stopping`), so the library theorems of
`Parking/MainTheorems.lean`, and these challenges, do not carry it.

- **`SubcriticalTail`** (Theorem 1.1): below the critical density, the
  expected number `S_t` of particles started at the origin and still active
  after round `t` satisfies `C⁻¹ exp(-C t^{d/(d+2)}) ≤ S_t ≤ C exp(-c t^{d/(d+2)})`.
- **`Master`** (Theorem 1.2): at the critical density,
  `c (E u_n(0) + log n) ≤ E U_n(0) ≤ C (E u_n(0) + log n)` for `n ≥ 2`.
- **`Growth`** (Corollary 1.3): `E U_n(0) ≍ n^{(4-d)/4}` and
  `S_t ≍ (t+1)^{-d/4}` for `d ≤ 3`; `E U_n(0) ≍ log n` and
  `c/(t+1) ≤ S_t ≤ C log(t+2)/(t+1)` for `d ≥ 4`.
- **`Trichotomy`** (Theorem 1.4): the quenched comparison of `U_n(0)` and
  `u_n(0)` for `d ≤ 3`, `d = 4` and `d ≥ 5`.
- **`Nearest`** (Theorem 1.5): for `d ≤ 3` the probability that the origin is
  closer to an unfilled hole than to an active particle after round `t` tends
  to zero.
- **`NearestCounterexample`** (Theorem 1.6): for `d ≥ 5` and a three-point law,
  that probability has a positive lower limit.
- **`Near`** (Theorem 1.7): `E U_∞(0)` is of order `nearRate d δ` as the mean
  `-δ` rises to zero.
- **`OrientedWalk`** (Theorem 1.8): the growth of `E U_n(0)` for the oriented
  walk, and for `d = 2` its ratio to the oriented sandpile odometer and the
  limits of `E U_n(0)` and `S_t`.

## Definition Provenance

The challenge definitions are statement-level copies of the definitions the
repository uses to state the theorems, in the namespace `ParkingAudit`.

| Challenge declaration | Source |
| --- | --- |
| `Site`, `unit`, `nbrSum`, `walkOp` | `LatticeProb/Site.lean` (Lattice-Probability) |
| `iidLaw`, `instructionLaw`, `stackLaw` | `LatticeProb/IID.lean` (Lattice-Probability) |
| `Label`, `Driver`, `State`, `boxFinset`, `candidates`, `initial`, `labelKey`, `labelLT` and its decidability instance, `activeAt`, `instructionIndex`, `nextPos`, `arrivalsAt`, `settles`, `step`, `state`, `particleOdometer`, `activeCount`, `holeCount`, `survivorsFrom`, `rankLaw`, `orientedInstructionLaw`, `orientedStackLaw` | `LatticeProb/ParticleHole.lean` (Lattice-Probability) |
| `LocalCLT.heatKernel` | `LatticeProb/Walk/LocalCLT.lean` (Lattice-Probability) |
| `greenTime` | `LatticeProb/Walk/LatticeGreen.lean` (Lattice-Probability) |
| `IsBrownianSpace` | `LatticeProb/Prob/BrownianExit.lean` (Lattice-Probability) |
| `Data`, `toDriver`, `law`, `orientedLaw`, `U`, `A`, `H`, `Ulimit`, `meanU`, `meanUlimit`, `S`, `u`, `orientedOp`, `uOriented`, `uOf`, `meanu`, `meanuOriented`, `CriticalLaw`, `supNorm`, `graphNorm`, `holeDistance`, `activeDistance`, `HoleCloser` | `Parking/Basic.lean` |
| `stepVec`, `walkPath`, `stepLaw`, `walkLaw`, `IsStoppingTimeLE`, `heat`, `green` | `Parking/Support/Walk.lean` |
| `IsLatticeKernel`, `kOp`, `kIter`, `kGreen`, `kSol`, `l2Norm`, `supAbs`, `greenMax` | `Parking/Support/Kernel.lean` |
| `rangeCard` | `Parking/Support/Range.lean` |
| `IsTestFun`, `IsSpaceTimeTest`, `lap`, `contOp`, `IsSpatialWhiteNoise`, `latticePoint`, `barDivisible`, `scenePair` | `Parking/Support/Continuum.lean` |
| `External.contHeatKernel` | `Parking/External/SRWLocalCLT.lean` |
| `External.contFiniteGreen` | `Parking/External/LinearFieldScaling.lean` |
| `IsSpatialGreenPairing` | `Parking/Support/SpatialGreenPairing.lean` |
| `IsQuarterBrownian`, `IsContStopping` | `Parking/Support/ContOrientedLimit.lean` |
| `contPayoffs`, `contValue` | `Parking/Support/ContStopGeneral.lean` |
| `IsSpatialContStopping`, `spatialContPayoffs`, `spatialContValue`, `ofBrownianSpace` | `Parking/Support/ContSpatialValue.lean` |
| `contUc` | `Parking/Support/ContUc.lean` |
| `binomLaw` | `Parking/Support/Oriented.lean` |
| `orientedPath` | `Parking/Support/OrientedMaximum.lean` |
| `orientedTerminalValue`, `orientedTerminalValues`, `orientedStoppingSup` | `Parking/Support/OrientedTerminal.lean` |
| `orientedScaledSite` | `Parking/Support/OrientedScaling.lean` |
| `nearRate` | `Parking/Support/Near.lean` |
| `threePointLaw` | `Parking/Support/ThreePointLaw.lean` |
| `CriticalScale.relax`, `.odometer`, `.centeredMassLaw`, `.heatKernel`, `.greenTime`, `.varianceRate`, `.corrRate`, `.windowKernel`, `.gram`, `.coeffNorm`, `.quadForm`, `.lowerTailRemainder` | `Parking/Support/NearestCriticalModel.lean` |
| `External.meanSandpileReal`, `External.SandpileGrowth`; `External.Bernstein`; `External.DonskerVaradhanRange`; `External.SpatialOdometerScaling`; `External.HeatInteriorRegularity`; `External.HeatCompactness`; `External.MultivariateBerryEsseen`; `External.OrientedStoppingStability` | `Parking/External/{SandpileGrowth,Bernstein,DonskerVaradhan,SpatialOdometerScaling,HeatInteriorRegularity,HeatCompactness,MultivariateBerryEsseen,OrientedStoppingStability}.lean` |

The copies sit in sections that open the same namespaces as their source
files, wherever the copied text relies on them.  No source file opens `Classical`, so every
decidability instance inside a copied definition is found the same way as in
the repository; the one explicit instance, the decidability of `labelLT`, is
copied as `Classical.decRel`.

## Solutions

Each `Solution.lean` imports the repository together with
`ParkingAudit/Support/ParkingVocabulary.lean`, a verbatim copy of the vocabulary block that
imports only Mathlib, and proves the byte-identical statement from the
corresponding theorem of `Parking/MainTheorems.lean` through the bridges in
`ParkingAudit/Support/Bridge.lean` (see [`DESIGN.md`](DESIGN.md)).

`ParkingAudit/StatementRegression.lean` is a local check of the statement-identity
part of the comparator: it elaborates each statement in the challenge
environment (`ParkingAudit/Support/Statements.lean`, which imports only Mathlib and
the vocabulary), checks that each solution theorem has exactly that type and
the same universe parameters, and that it mentions no constant of the
namespaces `Parking`, `LatticeProb` or `Sandpile`, and prints the axioms of
each solution theorem.

The audit modules live under the root `ParkingAudit`, and the library's own audit
surface under `LatticeProbAudit`, so the two cannot collide.

## Reproducing The Checks

The comparator configurations permit only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and set `enable_nanoda: false`.  Each challenge elaborates standalone against
this repository's Mathlib toolchain, e.g.

```bash
bash ParkingAudit/check_standalone.sh ParkingAudit/Master/Challenge.lean
bash ParkingAudit/check_standalone.sh --vocabulary
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'`
warning per challenge; the second command checks that the vocabulary block is
the same in every challenge and in `ParkingAudit/Support/ParkingVocabulary.lean`.  The
solutions and the regression build with

```bash
lake build ParkingAudit.StatementRegression
```

which prints, for each of the eight theorems, that it is identical to the
challenge statement and depends only on `propext`, `Classical.choice` and
`Quot.sound`.

**Status.**  All eight solutions build, and the statement regression and the
axiom prints pass locally.  `leanprover/comparator` passes on every pair, with
the Lean kernel and again with the independent nanoda kernel.  See
[`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md) for the results and the steps to
reproduce them.  The workflow
[`.github/workflows/comparator.yml`](../.github/workflows/comparator.yml) runs
it on request.
