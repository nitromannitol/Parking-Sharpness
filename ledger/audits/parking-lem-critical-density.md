# Audit report -- `lem-critical-density`

| field | value |
|---|---|
| manifest id | `lem-critical-density` |
| version / kind / state | `3` / `theorem` / `SEALED` |
| Lean export | `Parking.Frozen.critical_density` |
| source | `parking.tex:1255-1263 (label lem:critical-density)` |
| file | `Parking/Frozen/CriticalDensity.lean` |
| frozen SHA-256 | `4fd9afa48921b4bf2018aa051fdba74b19897b07946ee002ba036e2530d140da` |
| paper label | `lem:critical-density` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

`lem:critical-density` (`parking.tex:1255-1263`) has a universal `c` and a finite `C`.  Lean binds `c` outside `d` and `nu`, then the paper's hypotheses (`nu` probability, nonconstant via `forall k, nu {k} != 1`, `Integrable |k|`, mean `0`), then asserts `eventually t, c <= t * S_t` (the eventual form implies the paper's `liminf >= c` with the same `c`) and `exists C > 0, forall n >= 2, c log n - C <= meanU`.  `C` is bound after `d, nu`; the positivity of `C` is harmless because `max(C,1)` still satisfies the inequality.

## 2. Proof

In-repo; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.Frozen.critical_density` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

`CriticalLaw`-style hypotheses are satisfiable (e.g. the symmetric `±1` law); `c > 0` and the eventual/`forall n >= 2` lower bounds are genuine.

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
'Parking.Frozen.critical_density' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
