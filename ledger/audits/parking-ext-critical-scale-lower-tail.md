# Audit report -- `ext-critical-scale-lower-tail`

| field | value |
|---|---|
| manifest id | `ext-critical-scale-lower-tail` |
| version / kind / state | `4` / `theorem` / `SEALED` |
| Lean export | `Parking.External.criticalScaleLowerTail` |
| source | `parking.tex:1822-1848 (the critical-scale lower tail estimate of Bou-Rabee-Panagiotis, sandpile.tex:1696-1720); proved outright from the statement's own VarianceScale and MultivariateBerryEsseen hypotheses` |
| file | `Parking/External/CriticalScaleLowerTailProved.lean` |
| frozen SHA-256 | `5653f1d4fcb7df65fc6bfa43a6e283bed798a75f7cd6a78924bbecb733aa07d3` |
| paper label | `(none)` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

The frozen block is `theorem Parking.External.criticalScaleLowerTail : Parking.External.CriticalScaleLowerTail`; the Prop (unfrozen) is an implication from `VarianceScale` and `MultivariateBerryEsseen`, then a mean-zero finite-variance law `nu` with `int |z|^3 <= M var^{3/2}`, and `P(odometer_t(0) <= t^{(4-d)/4}/L) <= ofReal(C L^{-c} + C * lowerTailRemainder d t L a)` for `3 <= t`, `2 <= L`, `L^a <= t/2`, `1 <= d <= 3`, `0 < a < 4/(4-d)`.  This is the BP critical-scale lower-tail estimate (sandpile.tex:1696-1720) that `parking.tex:1822-1848` invokes; the manifest records that provenance, and the cited lines contain no display of it.

## 2. Proof

Proved outright from the two named antecedent Props in the same file; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.External.criticalScaleLowerTail` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

The constraints `L^a <= t/2` are satisfiable for every `t >= 3` by `L = 2` for small `a`; the conclusion is a probability upper bound, not a junk constant.

## 4. Citations

Genuine cited input (BP critical-scale lower-tail), reconstructed from the sibling paper because `parking.tex` only cites it.

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
'Parking.External.criticalScaleLowerTail' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
