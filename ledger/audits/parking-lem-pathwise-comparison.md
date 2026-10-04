# Audit report -- `lem-pathwise-comparison`

| field | value |
|---|---|
| manifest id | `lem-pathwise-comparison` |
| version / kind / state | `2` / `theorem` / `SEALED` |
| Lean export | `Parking.Frozen.pathwise_comparison` |
| source | `parking.tex:976-985 (label lem:pathwise-comparison)` |
| file | `Parking/Frozen/PathwiseComparison.lean` |
| frozen SHA-256 | `915149f5d65bc6b8d1fa9861b133ea97fab7889ca86689141bdaf6cf6455c266` |
| paper label | `lem:pathwise-comparison` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

`lem:pathwise-comparison` (`parking.tex:976-985`) is transcribed as the conjunction of the two displays `|U_n(x) - w_n(x) - u_n(x)| <= w*_n(x)` and `|U_n(x) - u_n(x)| <= 2 w*_n(x)`, for every `n` and `x`, with `U_n` cast to `ℝ`.  `w*_n(x) = E_x max_{0<=j<=n} |w_{n-j}(X_j)|` matches `parking.tex:972`, and the model realization hypothesis `hstep` is the same one as in `lem:parallel`.

## 2. Proof

In-repo; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.Frozen.pathwise_comparison` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

`wStar` is an `iSup` of absolute values, hence nonnegative and real; `eta = 0` makes both sides `0`, so the statement is satisfiable and non-vacuous.

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
'Parking.Frozen.pathwise_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
