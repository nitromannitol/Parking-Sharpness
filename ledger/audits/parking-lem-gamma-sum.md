# Audit report -- `lem-gamma-sum`

| field | value |
|---|---|
| manifest id | `lem-gamma-sum` |
| version / kind / state | `2` / `theorem` / `SEALED` |
| Lean export | `Parking.Frozen.gamma_sum` |
| source | `parking.tex:1057-1062 (label lem:gamma-sum)` |
| file | `Parking/Frozen/GammaSum.lean` |
| frozen SHA-256 | `692c19d009a8409875839f82436d7074482d48dd1e17c3a87163c889dc36c5a5` |
| paper label | `lem:gamma-sum` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

`lem:gamma-sum` (`parking.tex:1057-1062`) is transcribed as `exists C > 0` before `n >= 1` with the paper's bound `sum_y sup_{m <= n} Gamma_m(y) <= C kappa_d(n)`, plus a `Summable` guard so that the `tsum` is not junk.  `Gamma_m = Parking.gamma`, `sup_{m<=n} = ⨆ m ∈ Set.Iic n` (the `m = 0` term is `Gamma_0 = 0`, harmless), and `kappa d n` is `sqrt n`, `log(n+2)`, `1` for `d = 1, 2, >= 3`, matching the paper's `kappa_d(n)`.  The hypothesis `hgrad : 2 <= d -> GreenGradient d` is a cited input.

## 2. Proof

In-repo; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.Frozen.gamma_sum` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

`gamma` is a finite nonnegative sum of squares, so the `iSup` is genuinely nonnegative; `kappa` is positive for `n >= 1`; the statement is satisfiable.

## 4. Citations

`GreenGradient` is a genuine cited input (Lawler-Limic, via the paper's `eq:green-gradient`).

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
'Parking.Frozen.gamma_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
