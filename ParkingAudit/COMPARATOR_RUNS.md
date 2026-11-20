# Comparator runs

The official `leanprover/comparator` was run on all sixteen pairs in this directory, against the statements in this repository and the dependency revisions pinned in `lake-manifest.json` (Lattice-Probability `89de1230d02e1a737a9c7ecd776d34070be014ee`, Divisible-Sandpile-Percolation `e14e9d87adb65456761d1939fb7cedc49e57f5c5`), on a local machine (Linux 6.17), with the Lean kernel and the independent `nanoda` kernel both enabled (every committed `comparator.json` sets `"enable_nanoda": true`).

| Tool | Revision |
|---|---|
| leanprover/comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| leanprover/lean4export | `v4.35.0-rc2` (`6cea97789dc088ea47fcea15692db85685aedac5`) |
| Zouuup/landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (v0.1.18) |
| ammkrn/nanoda_lib | `6ae1f0cd962f081f6c423454c5da729d841236a7` |

A pass means the comparator printed `nanoda kernel accepts the solution`, `Lean default kernel accepts the solution` and `Your solution is okay!`: the solution proves a theorem whose statement and full dependency closure match the challenge's, using only the permitted axioms.  The host kernel supports an older Landlock interface than the one `landrun` requests, so `landrun` ran in its best-effort mode and its filesystem restriction was not enforced in these runs; the statement, closure, axiom and kernel checks do not depend on it.  The times are wall-clock times, including the builds of the challenge and solution modules.

## `Growth`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (260 s) |

## `GrowthUnconditional`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (433 s) |

## `Master`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (247 s) |

## `MasterUnconditional`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (445 s) |

## `Near`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (290 s) |

## `NearUnconditional`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (559 s) |

## `Nearest`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (404 s) |

## `NearestCounterexample`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (232 s) |

## `NearestCounterexampleUnconditional`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (293 s) |

## `NearestUnconditional`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (649 s) |

## `OrientedWalk`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (425 s) |

## `OrientedWalkUnconditional`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (495 s) |

## `SubcriticalTail`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (177 s) |

## `SubcriticalTailUnconditional`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (215 s) |

## `Trichotomy`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (276 s) |

## `TrichotomyUnconditional`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (431 s) |

To reproduce one pair, from the repository root:

```
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator ParkingAudit/<Pair>/comparator.json
```
