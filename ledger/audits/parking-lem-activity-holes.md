# Audit report -- `lem-activity-holes`

| field | value |
|---|---|
| manifest id | `lem-activity-holes` |
| version / kind / state | `2` / `theorem` / `SEALED` |
| Lean export | `Parking.Frozen.activity_holes` |
| source | `parking.tex:776-782 (label lem:activity-holes)` |
| file | `Parking/Frozen/ActivityHoles.lean` |
| frozen SHA-256 | `365a9628b28180cb58ed3d8828bbf94e377d2dd0362c8fe0b155ff7e09954052` |
| paper label | `lem:activity-holes` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

`lem:activity-holes` (`parking.tex:776-782`) is transcribed with the paper's hypotheses (`eta` translation invariant, `E|eta(0)| < inf`) as `μ` a probability measure, `TranslationInvariant μ`, `Integrable (|η 0|) μ`, and, for every `t`, `E A_t(0) - E H_t(0) = E eta(0)`.  The paper's display is exactly the third conjunct; the two leading `Integrable` conjuncts are junk-value guards.  `A`, `H` are the active and hole counts of the driver built from the data.

## 2. Proof

In-repo; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.Frozen.activity_holes` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

Take `μ` the law of a constant configuration; then both counts are finite and the identity holds.  The guards make the differences genuine, not junk integrals.

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
'Parking.Frozen.activity_holes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
