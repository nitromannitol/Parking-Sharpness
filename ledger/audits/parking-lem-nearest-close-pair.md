# Audit report -- `lem-nearest-close-pair`

| field | value |
|---|---|
| manifest id | `lem-nearest-close-pair` |
| version / kind / state | `2` / `theorem` / `SEALED` |
| Lean export | `Parking.Frozen.nearest_close_pair` |
| source | `parking.tex:2199-2204 (label lem:nearest-close-pair)` |
| file | `Parking/Frozen/NearestClosePair.lean` |
| frozen SHA-256 | `1a2588c5c66410e9fd0aff6c7f477c8c46eaa4ef8fe49970fa209d7504007288` |
| paper label | `lem:nearest-close-pair` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

`lem:nearest-close-pair` (`parking.tex:2199-2204`) is transcribed with the section's setting made explicit: `5 <= d`, `0 < p <= 1/4`, i.i.d. `threePointLaw p` (mass `p` at `±1`, `1-2p` at `0`), `x != z`, and `P(H_t(x)=1 and H_t(z)=1) <= 2 p h_t` with `h_t = holeProb = P(H_t(0) = 1)`.  The explicit constant `2` is preserved.

## 2. Proof

In-repo; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.Frozen.nearest_close_pair` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

`p = 1/4` satisfies all hypotheses; both sides are genuine probabilities and `h_t` is a hole probability, not a junk value.

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
'Parking.Frozen.nearest_close_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
