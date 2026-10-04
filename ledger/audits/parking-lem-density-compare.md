# Audit report -- `lem-density-compare`

| field | value |
|---|---|
| manifest id | `lem-density-compare` |
| version / kind / state | `3` / `theorem` / `SEALED` |
| Lean export | `Parking.Frozen.density_compare` |
| source | `parking.tex:811-821 (label lem:density-compare)` |
| file | `Parking/Frozen/DensityCompare.lean` |
| frozen SHA-256 | `3bafe868c95ca2cc78df469dad40bc17036ae2e6e2052e98e5e3ce7ac4e9cc96` |
| paper label | `lem:density-compare` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

`lem:density-compare` (`parking.tex:811-821`) is transcribed with two finite-first-moment hypotheses, a probability coupling `Q` with marginals `μ, μ'`, invariance under the diagonal shift and `η <= η~` `Q`-a.e., and the conclusion `0 <= S~_t - S_t <= E η~(0) - E η(0)` for every `t`.  The two leading `Integrable` conjuncts are junk-value guards; the two inequalities are exactly the display.

## 2. Proof

In-repo; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.Frozen.density_compare` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

Take `μ = μ'` and `Q` the diagonal coupling; then `0 <= 0 <= 0`.  With distinct laws the bound is the paper's genuine inequality between survivor expectations.

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
'Parking.Frozen.density_compare' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
