# Comparator runs

The official `leanprover/comparator` was run on every pair in this directory on 2026-09-24, at commit `9c18636`, on a local machine. Each pair was checked twice: once with the Lean kernel, and once more with the independent `nanoda` kernel enabled (a temporary copy of `comparator.json` with `"enable_nanoda": true`). The committed configurations keep `enable_nanoda` false so that a reproduction needs only three tools.

| Tool | Revision |
|---|---|
| leanprover/comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| leanprover/lean4export | `v4.32.0` (`4e7915201d3f9f04470d9eae002fa695f7cdc589`) |
| Zouuup/landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (v0.1.18; Linux 5.15, Landlock ABI 1 in best-effort mode) |
| ammkrn/nanoda_lib | `6ae1f0cd962f081f6c423454c5da729d841236a7` |

| Pair | Lean kernel | Lean and nanoda kernels |
|---|---|---|
| `Growth` | passed (278 s) | passed (316 s) |
| `Master` | passed (218 s) | passed (289 s) |
| `Near` | passed (277 s) | passed (353 s) |
| `Nearest` | passed (320 s) | passed (424 s) |
| `NearestCounterexample` | passed (202 s) | passed (286 s) |
| `SubcriticalTail` | passed (143 s) | passed (187 s) |
| `OrientedWalk` | passed (338 s) | passed (401 s) |
| `Trichotomy` | passed (275 s) | passed (344 s) |

A pass means the comparator printed `Your solution is okay!`: the solution proves a theorem whose statement and full dependency closure match the challenge's, using only the permitted axioms.

To reproduce one pair, from the repository root:

```
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> \
  lake env <comparator>/.lake/build/bin/comparator ParkingAudit/<Pair>/comparator.json
```

## 2026-09-27

The comparator was run again on every pair on 2026-09-27, after the audit library was renamed from `Audit` to `ParkingAudit` and Lattice-Probability and the sandpile repository were pinned at `720e65e` and `cd8b15a`. The run used the Lean sources of commit `5683887`, which differ from those of the commit that records this run only in this file. The tools, their revisions and the machine were those of the first run, and each pair was again checked with the Lean kernel and then with the nanoda kernel enabled.

| Pair | Lean kernel | Lean and nanoda kernels |
|---|---|---|
| `Growth` | passed (315 s) | passed (314 s) |
| `Master` | passed (294 s) | passed (386 s) |
| `Near` | passed (300 s) | passed (401 s) |
| `Nearest` | passed (336 s) | passed (480 s) |
| `NearestCounterexample` | passed (220 s) | passed (304 s) |
| `SubcriticalTail` | passed (168 s) | passed (185 s) |
| `OrientedWalk` | passed (401 s) | passed (506 s) |
| `Trichotomy` | passed (256 s) | passed (318 s) |

## 2026-09-27 (second)

The comparator was run again on every pair on 2026-09-27, on a second local machine (Linux 6.17), with the same tool revisions as above. The run used the Lean sources of commit `028f718`, after the U-concentration, Green-norms, strong-minimum-principle, variance-scale, critical-scale lower-tail and binomial local CLT vocabulary copies and bridge lemmas were removed. Each pair was again checked with the Lean kernel and then with the nanoda kernel enabled.

| Pair | Lean kernel | Lean and nanoda kernels |
|---|---|---|
| `Growth` | passed (162 s) | passed (198 s) |
| `Master` | passed (194 s) | passed (209 s) |
| `Near` | passed (190 s) | passed (230 s) |
| `Nearest` | passed (234 s) | passed (391 s) |
| `NearestCounterexample` | passed (194 s) | passed (199 s) |
| `SubcriticalTail` | passed (110 s) | passed (119 s) |
| `OrientedWalk` | passed (228 s) | passed (315 s) |
| `Trichotomy` | passed (171 s) | passed (224 s) |
