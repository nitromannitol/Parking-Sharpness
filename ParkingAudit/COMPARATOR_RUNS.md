# Comparator runs

The official `leanprover/comparator` was run on every pair in this directory, against the statements in this repository and the Lattice-Probability revision pinned in `lake-manifest.json`, on a local machine (Linux 6.17), with the Lean kernel and the independent `nanoda` kernel both enabled (every committed `comparator.json` sets `"enable_nanoda": true`).

| Tool | Revision |
|---|---|
| leanprover/comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| leanprover/lean4export | `v4.32.0` (`4e7915201d3f9f04470d9eae002fa695f7cdc589`) |
| Zouuup/landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (v0.1.18) |
| ammkrn/nanoda_lib | `6ae1f0cd962f081f6c423454c5da729d841236a7` |

A pass means the comparator printed `nanoda kernel accepts the solution`, `Lean default kernel accepts the solution` and `Your solution is okay!`: the solution proves a theorem whose statement and full dependency closure match the challenge's, using only the permitted axioms.

## `Growth`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (413 s) |

## `Master`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (273 s) |

## `Near`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (394 s) |

## `Nearest`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (350 s) |

## `NearestCounterexample`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (188 s) |

## `OrientedWalk`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (393 s) |

## `SubcriticalTail`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (126 s) |

## `Trichotomy`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (238 s) |

To reproduce one pair, from the repository root:

```
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator ParkingAudit/<Pair>/comparator.json
```
