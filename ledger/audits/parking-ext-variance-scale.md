# Audit report -- `ext-variance-scale`

| field | value |
|---|---|
| manifest id | `ext-variance-scale` |
| version / kind / state | `2` / `theorem` / `SEALED` |
| Lean export | `Parking.External.varianceScale` |
| source | `parking.tex:1822-1848 (critical_toppling input, sandpile.tex:1117-1240); proved from the shared library Lattice-Probability (LatticeProb.Walk.VarianceScale, LatticeProb.Walk.Correlation, LatticeProb.Walk.WindowD4)` |
| file | `Parking/External/VarianceScale.lean` |
| frozen SHA-256 | `5ad03a7dbc301ede04678dd9bcf379e7ec8c2b56ce36c83f773c6daa854b1ab0` |
| paper label | `(none)` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

The node's frozen block is `theorem Parking.External.varianceScale : Parking.External.VarianceScale`.  Its Prop (unfrozen) is the sandpile variance/correlation input: (1) the finite-time variance scale `eq:Qt-table`; (2) the membrane correlation bound `eq:corr-bound`; (3) the `d = 4` window and tail bounds.  `parking.tex:1822-1848` does not display these estimates -- it is the place where the critical-scale lower-tail estimate of BP is *used* -- so the manifest source string honestly records the provenance `(critical_toppling input, sandpile.tex:1117-1240)`.  The statement is read against the sibling sandpile statement, not against a `parking.tex` display.

## 2. Proof

Proved from `LatticeProb.exists_tsum_srwGreen_sq_bounds`, `exists_tsum_srwGreen_mul_le`, `exists_tsum_srwWindow_sq_le` and `exists_tsum_srwGreen_four_sq_le`; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.External.varianceScale` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

The sums are `tsum`s of nonnegative Green-kernel squares with explicit positive rates; satisfiable and finite.  No junk `tsum` value is accepted because each clause is two-sided or an explicit bound.

## 4. Citations

Genuine cited input: Lawler-Limic Propositions 2.4.1/2.4.4/2.4.6 and Theorem 4.3.1, as the file documents.

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
'Parking.External.varianceScale' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
