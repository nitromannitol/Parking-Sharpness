# Audit report -- `lem-one-particle`

| field | value |
|---|---|
| manifest id | `lem-one-particle` |
| version / kind / state | `2` / `theorem` / `SEALED` |
| Lean export | `Parking.Frozen.one_particle` |
| source | `parking.tex:682-692 (label lem:one-particle)` |
| file | `Parking/Frozen/OneParticle.lean` |
| frozen SHA-256 | `bdcb454c0bcecd8cf2864cdd618aa51d43b0dd162dc862fd834ec9882d88aaff` |
| paper label | `lem:one-particle` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

`lem:one-particle` (`parking.tex:682-692`) is transcribed as the announced disjunction: either `H~_t = H_t` and `A~_t - A_t = 1` at a single `z` and `0` elsewhere, or `A~_t = A_t` and `H_t - H~_t = 1` at a single `z`.  `addParticleDriver x₀ D` raises the configuration by one at `x₀` and shares everything else, which is the coupling of the paper's construction; the statement is pathwise over every `PDriver`.

## 2. Proof

In-repo; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.Frozen.one_particle` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

The disjunction is genuinely satisfiable: either branch can hold depending on the driver, and the `+1`/`0 elsewhere` clauses are explicit.  No junk value.

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
'Parking.Frozen.one_particle' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
