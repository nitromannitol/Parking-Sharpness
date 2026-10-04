# Audit report -- `ext-green-norms`

| field | value |
|---|---|
| manifest id | `ext-green-norms` |
| version / kind / state | `2` / `theorem` / `SEALED` |
| Lean export | `Parking.External.greenNorms` |
| source | `parking.tex:1383-1400 (label eq:green-norms); no longer assumed, discharged from LatticeProb.Walk.VarianceScale and LatticeProb.Walk.SRWGreenSup, with the max-norm lower bound proved here from LatticeProb.Walk.SRWDiag.exists_srwHeat_diag_lower` |
| file | `Parking/External/GreenNormsProved.lean` |
| frozen SHA-256 | `b3b650d756d9f8218c5f50ebea09861e8c7b459b4a1dae1cd95682bcb7ab0e34` |
| paper label | `eq:green-norms` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

The frozen block is `theorem Parking.External.greenNorms : Parking.External.GreenNorms`; the Prop (unfrozen `Parking/External/GreenNorms.lean`) states both halves of `eq:green-norms` with their own `exists c C, 0 < c, 0 < C`, inside `forall d, 1 <= d`, for all `n >= 2`.  The piecewise rates are `n^{3/4}, n^{1/2}, n^{1/4}, sqrt(log n), 1` (l2) and `n^{1/2}, log n, 1` (max) exactly as in the paper.  The range `n >= 2` is stronger than the paper's asymptotic reading and equivalent for these positive rates.  Quantifier order makes `c, C` depend on `d` only.

## 2. Proof

Companion `Parking.External.greenNorms` proved from the shared library's Green-kernel estimates (and an internal max-norm lower bound); closure `[propext, Classical.choice, Quot.sound]`.

`Parking.External.greenNorms` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

Both displayed quantities are positive finite for every `n >= 2`; the two-sided bounds are genuine.  `l2Norm` is `sqrt` of a finite sum of squares and `greenMax` an `iSup` of nonnegative terms, so neither is a junk `tsum`/`sInf`.

## 4. Citations

Genuine cited input: Bou-Rabee-Panagiotis Section 3.1, as the paper says.

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
'Parking.External.greenNorms' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
