# Audit report -- `lem-exposure`

| field | value |
|---|---|
| manifest id | `lem-exposure` |
| version / kind / state | `2` / `theorem` / `SEALED` |
| Lean export | `Parking.Frozen.exposure` |
| source | `parking.tex:1107-1115 (label lem:exposure)` |
| file | `Parking/Frozen/Exposure.lean` |
| frozen SHA-256 | `deba2db53944b19ca4eed91c4d6f789a208153d286b29ce83b1a602a23d5aed3` |
| paper label | `lem:exposure` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

`lem:exposure` (`parking.tex:1107-1115`) is transcribed with `G_k = expFiltration d k`.  The first conjunct is a.e. measurability of `U omega (k+1) x` with respect to `G_k`; the second is the conditional-independence product rule for the unread instructions, reindexed so the paper's `rho_{j+1}(y)` is `omega.2.1 (y,j)` and `j+1 > U_k(y)` is `U omega k y <= j`.  This is the standard `sigma`-algebra formulation of the paper's conditional law `P(y,·)`.

## 2. Proof

In-repo; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.Frozen.exposure` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

The conditional-expectation identity of the second conjunct is a genuine identity of the `law d ν` a.e.-classes; the first is an a.e. equality.  No junk value is asserted.

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
'Parking.Frozen.exposure' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
