# Comparator design memo: vocabulary, bridges, deltas

This memo records how the eight comparator pairs are built, for whoever checks
or extends them.  The files are `ParkingAudit/<Thm>/Challenge.lean`,
`ParkingAudit/<Thm>/Solution.lean`, `ParkingAudit/Support/ParkingVocabulary.lean` (the
Mathlib-only copy of the vocabulary), `ParkingAudit/Support/Bridge.lean` (the
identifications), `ParkingAudit/Support/Statements.lean` and
`ParkingAudit/StatementRegression.lean` (the local statement check).

## 0. Solution architecture

The comparator checks that the solution theorem has the same elaborated type
as the challenge theorem, constant by constant through the whole dependency
closure.  So the vocabulary constants must elaborate in the solution exactly
as in the challenge.  As in the comparator pattern of the `CoarseGraining` and
`Superdiffusion` repositories, the vocabulary is therefore compiled in a module
that imports **only Mathlib** (`ParkingAudit/Support/ParkingVocabulary.lean`, the analogue
of their per-challenge `SolutionBasic.lean`), and `Solution.lean` imports the
repository, that module, and the bridges, and states the theorem with the
challenge's bytes.

The eight challenges share one vocabulary block, byte-identical in each
(`bash ParkingAudit/check_standalone.sh --vocabulary`), so one `ParkingVocabulary.lean`
serves all eight solutions.  The block contains definitions that a given
challenge does not use (for instance the continuum objects in the challenges
that do not mention the scaling limit); they do not enter that theorem's
dependency closure.

The vocabulary is collected mechanically: starting from the types of the
eight theorems of `Parking/MainTheorems.lean`, every constant of the
namespaces `Parking`, `LatticeProb` and `Sandpile` is followed through the
values of definitions and the constructors of structures, and each constant
reached is copied from its source file.  No `Sandpile` constant is reached.

## 1. Definitionally shared vocabulary

Every definition of the vocabulary that is neither a structure nor recursive,
and does not unfold to one, is a token-for-token copy of its source over
Mathlib types, and is definitionally equal to its counterpart.  Examples are
`law`, `orientedLaw`, `walkLaw`, `iidLaw`, `stackLaw`, `rankLaw`, `contOp`,
`IsSpatialWhiteNoise`, `contValue`, `spatialContValue`, `binomLaw`,
`nearRate` and `threePointLaw`, and the cited results `External.Bernstein`,
`External.HeatInteriorRegularity`, `External.HeatCompactness` and
`External.MultivariateBerryEsseen`, each of which `Bridge.lean` identifies by
`rfl`.  The solutions use these definitionally, with no rewriting.

## 2. Recursive copies and structure copies

Nine vocabulary definitions are recursive, hence new recursive definitions:
`u`, `uOriented`, `walkPath`, `orientedPath`, `heat`, `kIter`, `kSol`,
`LocalCLT.heatKernel` and `CriticalScale.odometer`.  Each is proved equal to
its counterpart, as a function of all its arguments, by induction on the
recursion variable (`Bridge.u_eq` and so on).

Four vocabulary declarations are structures, hence new inductive types:

- `Driver` and `State`, the data and the state of the particle–hole process.
  They occur only inside the definitions of the process.  `Bridge.toDriverLP`
  and `Bridge.toStateLP` convert them field by field, and `Bridge.state_eq`
  proves by induction on the round that the converted state of the vocabulary
  process is the library's state of the converted driver.  From it,
  `Bridge.U_eq`, `A_eq`, `H_eq` and `survivorsFrom_eq` identify the odometer,
  the active particles, the unfilled holes and the survivors.
- `CriticalLaw` and `IsBrownianSpace`, which are propositions.
  `Bridge.criticalLaw_eq` and `Bridge.isBrownianSpace_eq` prove them equal to
  their counterparts by propositional extensionality, field by field in both
  directions, since `CriticalLaw` occurs both as a premise and inside a
  conclusion (the `d = 4` part of Theorem 1.4), and `IsBrownianSpace` inside a
  cited result.

## 3. Composite identifications

Every other vocabulary constant that differs from its counterpart does so only
because it unfolds to one of the declarations of Section 2.  `Bridge.lean`
proves each such constant equal to its counterpart by unfolding it with
`delta`, rewriting the constants of Section 2, and closing the goal by
definitional equality: `meanU`, `meanu`, `uOf`, `S`, `Ulimit`, `meanUlimit`,
`meanuOriented`, `HoleCloser`, and the cited results
`External.SandpileGrowth`, `External.DonskerVaradhanRange`,
`External.SpatialOdometerScaling` and `External.OrientedStoppingStability`.
Each identification is an equality of
constants, so that a single `rw` replaces every occurrence, whatever its
polarity.

## 4. Theorem-level bridges

Each solution reverts its hypotheses, so that the goal is the whole statement,
rewrites with the equalities of Sections 2 and 3 that occur in it, and closes
the goal with the theorem of `Parking/MainTheorems.lean`.  What is left after
the rewrites (the laws, the Green and heat objects that are plain
definitions, the Mathlib types) is identified definitionally by that final
`exact`.

## 5. Presentation deltas

At the level of the displayed statements, each challenge theorem is the
statement of the corresponding theorem of `Parking/MainTheorems.lean` with
every repository and library name replaced by its vocabulary copy.  Two of
those theorems differ from their certified counterparts in `Parking/Frozen/`:
`Parking.Frozen.trichotomy` and `Parking.Frozen.near` also take
`Parking.External.Stopping`, which `Parking.External.stopping` proves from the
shared library, and `Parking.trichotomy` and `Parking.near` discharge it.  The
vocabulary therefore does not copy `External.Stopping` or the walk-stopping
vocabulary of the library it is stated in.

How each statement reads the paper is recorded in
[`CORRESPONDENCE.md`](../CORRESPONDENCE.md) and [`PROOF.md`](../PROOF.md).  The
comparator does not check that reading: it checks that the library proves
exactly the displayed statement, over definitions that can be read without the
library.

## 6. What the comparator does not certify

- The cited results.  The challenges take them as hypotheses, restated in the
  vocabulary.  A proof conditional on a proposition does not show that the
  proposition is a faithful rendering of the cited theorem; that reading is
  the subject of `ASSUMPTIONS.md`.
- The faithfulness of the vocabulary to the paper.  The vocabulary is a copy
  of the definitions the repository uses, so the comparator shows that nothing
  in the statements depends on the library beyond what the vocabulary
  displays; a reader still has to check the vocabulary against the paper.

## 7. Remaining points

- **U1 (instance environments).**  The solutions import both the repository
  and the vocabulary.  The one instance the vocabulary declares, the
  decidability of `labelLT`, has a counterpart of the same value in the
  library.  `ParkingAudit/StatementRegression.lean` checks that no solution statement
  picked up a repository or library constant, in particular not the library's
  instance.
- **U2 (comparator).**  `leanprover/comparator` passes on every pair, with the
  Lean kernel and again with the independent nanoda kernel.  See
  [`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md) for the results and the
  reproduction steps.  The local regression compares the solution types with
  the challenge-environment types up to the auxiliary proof lemmas that a
  `def` abstracts; the comparator's own closure check is stricter.
- **U3 (vocabulary size).**  The vocabulary is about 1,200 lines, because the
  cited results of Theorems 1.5 and 1.8 are stated over the continuum objects
  of the scaling limits.  Most of it is read only by those two challenges.
