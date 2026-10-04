# Audit report -- `lem-near-tilt`

| field | value |
|---|---|
| manifest id | `lem-near-tilt` |
| version / kind / state | `3` / `theorem` / `SEALED` |
| Lean export | `Parking.Frozen.near_tilt` |
| source | `parking.tex:2599-2604 (label lem:near-tilt)` |
| file | `Parking/Frozen/NearTilt.lean` |
| frozen SHA-256 | `53b268f22492b9a63b9dedbc45dd7e2be3fc2e8a9945e0036053d022279f372c` |
| paper label | `lem:near-tilt` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

`lem:near-tilt` (`parking.tex:2599-2604`) is transcribed as `exists c C > 0, exists δ₁ in (0, δ₀], forall δ in (0, δ₁], forall t, S_t^δ <= C E_0 e^{-c δ² |R_t|}`, with an added integrability guard.  "For all sufficiently small `δ`" is the explicit `δ₁`; `S_t^δ` is `S (law d (ν δ)) t` and `E_0 e^{-a|R_t|}` is `rangeExp d a t`; `c, C, δ₁` are chosen after the family, so they may depend on it but not on `δ` or `t`.

## 2. Proof

In-repo; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.Frozen.near_tilt` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

`NearFamily` is satisfiable; `rangeExp` is a genuine nonnegative walk average; no junk `0`/`sInf ∅` can satisfy the bound trivially because `C > 0` and the right side is a genuine exponential moment.

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
'Parking.Frozen.near_tilt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
