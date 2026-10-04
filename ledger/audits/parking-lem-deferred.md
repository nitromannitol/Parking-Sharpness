# Audit report -- `lem-deferred`

| field | value |
|---|---|
| manifest id | `lem-deferred` |
| version / kind / state | `4` / `theorem` / `SEALED` |
| Lean export | `Parking.Frozen.deferred` |
| source | `parking.tex:659-667 (label lem:deferred)` |
| file | `Parking/Frozen/Deferred.lean` |
| frozen SHA-256 | `e4984c1e6330387bca5665fe675d68516549cabec6d207182e59213c7af18240` |
| paper label | `lem:deferred` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

`lem:deferred` (`parking.tex:659-667`) is transcribed with the paper's `j >= 1` reindexed to Lean's `j : ℕ` with `j + 1 <= U omega n y` and stack entry `(y, j)`.  The first conjunct is the measurability claim, expressed as pathwise invariance of the event under changing the instruction at `(y,j)` while holding the configuration, the uniforms and the other instructions fixed; the second is the displayed identity `P(U_n(y) >= j, rho_j(y) = x | eta) = P(y,x) P(U_n(y) >= j | eta)` with `kern d y x = 1{x ~ y}/(2d)`.

## 2. Proof

In-repo; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.Frozen.deferred` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

The identity holds for every fixed configuration, including the case where `probGiven` is `0`; both sides are nonnegative reals, no junk value.

## 4. Citations

None.

## Machine evidence

```
$ cd ~/lean/Parking-Sharpness
$ sha256sum paper/parking.tex
4aa03aee7c30e24bffc9a4e8220f775b5c71706e694dcd9bcffc865c8135d3a0  paper/parking.tex
$ python3 tools/check_manifest.py
check_manifest: OK (62 nodes, 0 unsealed; ... 658 Parking declarations indexed)          [exit 0]
$ python3 tools/check_axioms.py
62 clean, 0 depend on sorryAx, 0 unresolved                                              [exit 0]
$ python3 tools/check_constants.py
check_constants: OK (62 statements; every existential constant is bound before every paper parameter ...)  [exit 0]
$ python3 tools/check_coverage.py
check_coverage: OK ... every theorem, lemma and proposition in the paper is formalized        [exit 0]
$ python3 tools/check_clauses.py
check_clauses: OK (48 statements, each read against the paper and its correspondence recorded ...) [exit 0]
$ python3 tools/check_exponents.py
check_exponents: OK (62 statements; every paper exponent appears in its Lean statement or is explained) [exit 0]
$ python3 tools/paper_anchors.py
paper_anchors: OK (48 anchors resolved, 14 nodes carry no paper label)                    [exit 0]
$ python3 tools/check_warnings.py
check_warnings: OK (0 registered sorry warnings)                                         [exit 0]
```

Targeted axiom probe (Batch A exports, run through `lake env lean`):

```
'Parking.Frozen.deferred' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
