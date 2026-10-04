# Audit report -- `ext-sandpile-growth-proved`

| field | value |
|---|---|
| manifest id | `ext-sandpile-growth-proved` |
| version / kind / state | `1` / `theorem` / `SEALED` |
| Lean export | `Parking.External.sandpileGrowth` |
| source | `parking.tex:929-943 (label thm:BP); proved from the divisible sandpile formalization rather than assumed, modulo the three continuum inputs that formalization itself assumes` |
| file | `Parking/External/SandpileGrowthProved.lean` |
| frozen SHA-256 | `bd913fdcd168ef2387445166f62509244e7d87fa92072980ef3b4189dd94e254` |
| paper label | `thm:BP` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

`thm:BP` (`parking.tex:929-943`) is transcribed clause by clause: (1) `d <= 3` gives `c n^{(4-d)/4} <= E u_n(0) <= C n^{(4-d)/4}` for `n >= 2`; (2) `d = 4` gives `c log n <= ... <= C log n`; (3) `5 <= d` gives `c (log n)^{2/d} <= ... <= C log(n+1)`; (4) if `eta(0)` is bounded below (Lean: `exists b, b <= z` a.e.) the same two-sided `(log n)^{2/d}` holds; (5) `d <= 3` gives `exists L > 0, n^{-(4-d)/4} E u_n(0) -> L`.  The standing hypotheses are explicit `d >= 1`, `nu` a probability measure on `ℝ` with mean `0`, `0 < evariance < top` and `exists theta > 0, E e^{theta|z|} < inf`.  The reindexing is faithful and the range `n >= 2` matches the paper.

## 2. Proof

The frozen block proves the Prop from `Sandpile.Frozen.mean_growth_le_three`, `mean_growth_four`, `high_first_order`, `exists_crude_log_upper` and `dgt4_height_upper_tail`, carrying the three continuum inputs the sandpile formalization itself assumes (`Sandpile.External.LocalCLT`, `ContinuumStoppingStability`, `ContinuumOptimalStopping`).  Closure `[propext, Classical.choice, Quot.sound]`.

`Parking.External.sandpileGrowth` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

The hypotheses are satisfiable (e.g. a centred non-degenerate law with an exponential moment); the `c, C` are positive and `L > 0`, so no conclusion collapses to a junk value.

## 4. Citations

The three hypotheses are genuine cited inputs of the divisible-sandpile formalization, not steps of `parking.tex`.

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
'Parking.External.sandpileGrowth' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
