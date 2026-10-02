# Comparator runs

The official `leanprover/comparator` was run on every pair in this directory, against the statements in this repository and the Lattice-Probability revision pinned in `lake-manifest.json`, on a local machine (Linux 6.17). Each pair was checked twice: once with the Lean kernel, and once more with the independent `nanoda` kernel enabled (a temporary copy of `comparator.json` with `"enable_nanoda": true`). The committed configurations keep `enable_nanoda` false so that a reproduction needs only three tools.

| Tool | Revision |
|---|---|
| leanprover/comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| leanprover/lean4export | `v4.32.0` (`4e7915201d3f9f04470d9eae002fa695f7cdc589`) |
| Zouuup/landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (v0.1.18; Linux 5.15, Landlock ABI 1 in best-effort mode) |
| ammkrn/nanoda_lib | `6ae1f0cd962f081f6c423454c5da729d841236a7` |

| Pair | Lean kernel | Lean and nanoda kernels |
|---|---|---|
| `Growth` | passed (180 s) | passed (229 s) |
| `Master` | passed (181 s) | passed (216 s) |
| `Near` | passed (187 s) | passed (237 s) |
| `Nearest` | passed (248 s) | passed (388 s) |
| `NearestCounterexample` | passed (241 s) | passed (208 s) |
| `OrientedWalk` | passed (232 s) | passed (472 s) |
| `SubcriticalTail` | passed (121 s) | passed (140 s) |
| `Trichotomy` | passed (180 s) | passed (212 s) |

A pass means the comparator printed `Your solution is okay!`: the solution proves a theorem whose statement and full dependency closure match the challenge's, using only the permitted axioms.

To reproduce one pair, from the repository root:

```
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> \
  lake env <comparator>/.lake/build/bin/comparator ParkingAudit/<Pair>/comparator.json
```
