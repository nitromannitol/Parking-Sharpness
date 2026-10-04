# Audit report -- `ext-heat-strong-minimum`

| field | value |
|---|---|
| manifest id | `ext-heat-strong-minimum` |
| version / kind / state | `4` / `theorem` / `SEALED` |
| Lean export | `Parking.External.heatStrongMinimum` |
| source | `parking.tex:1800-1820 (prop:spatial-scaling, Step 4, strong minimum principle); proved from the shared library strong minimum principle of Nirenberg 1953 Theorem 1` |
| file | `Parking/External/HeatStrongMinimumProved.lean` |
| frozen SHA-256 | `e00ed4b883e8b685cb5fa85d5eb6476e6d1b2de62127d3c6775652a869235e10` |
| paper label | `(none)` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

The paper never *states* the strong minimum principle; it invokes it in Step 4 (`parking.tex:1800-1820`) at `v(s0,x0)=0` on `(tau,s0] x {x0} subset O`.  The frozen Prop `Parking.External.HeatStrongMinimum` is exactly the general principle: for open `U`, `ContDiffOn` nonnegative `v` with `HasDerivAt (s |-> v(s,x)) (contOp d v(s,.) x) s` (`contOp = (2d)^{-1} Delta`), if `v(s0,x0)=0` and `(Ioc tau s0) x {x0} subset U`, then `v(s,x0)=0` for all `s in (tau,s0]`.  This is the form the paper uses.

## 2. Proof

Companion `Parking.External.heatStrongMinimum` proved from the shared library's Nirenberg-1953 strong minimum principle; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.External.heatStrongMinimum` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

`v = 0` satisfies every hypothesis and the conclusion; the conclusion is an identity on an interval, not a junk value.

## 4. Citations

Genuine cited input (classical Nirenberg 1953), not a step of `parking.tex`.

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
'Parking.External.heatStrongMinimum' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
