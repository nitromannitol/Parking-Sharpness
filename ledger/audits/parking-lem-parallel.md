# Audit report -- `lem-parallel`

| field | value |
|---|---|
| manifest id | `lem-parallel` |
| version / kind / state | `3` / `theorem` / `SEALED` |
| Lean export | `Parking.Frozen.parallel` |
| source | `parking.tex:647-653 (label lem:parallel)` |
| file | `Parking/Frozen/Parallel.lean` |
| frozen SHA-256 | `ee000c2b7ec706b4f32ff4a5059cdd6e38438d920f437f4cd092312cf1bd44ec` |
| paper label | `lem:parallel` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

`lem:parallel` (`parking.tex:647-653`) is transcribed as `(forall x, U omega 0 x = 0)` and, for every `n, x`, `(U omega (n+1) x : ℤ) = max 0 (ω.1 x + sum_{y ∈ nbrFinset x} arrivals omega.2.1 y x (U omega n y))`.  `(+)^+` is `max 0` on `ℤ`, and the paper's sum over all `y` is restricted to the lattice neighbours; the hypothesis `hstep` (every instruction is a neighbour of its site) is exactly the model's realization assumption that makes the two sums agree.

## 2. Proof

In-repo; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.Frozen.parallel` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

`hstep` is satisfiable for every `d >= 1` (choose one neighbour of each site for each stack entry); the conclusion is an integer identity, not a junk value.  For `d = 0` the hypothesis is empty and the statement is vacuously true, but `d = 0` is outside the paper's setting.

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
'Parking.Frozen.parallel' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
