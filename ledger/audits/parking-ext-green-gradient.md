# Audit report -- `ext-green-gradient`

| field | value |
|---|---|
| manifest id | `ext-green-gradient` |
| version / kind / state | `2` / `definition` / `SEALED` |
| Lean export | `Parking.External.GreenGradient` |
| source | `parking.tex:1030-1034 (label eq:green-gradient, proved in the shared library)` |
| file | `Parking/External/GreenGradient.lean` |
| frozen SHA-256 | `41340ef1abd269fe9cda495a1b59c3c1392c591cc1c704da479a0349f700028f` |
| paper label | `eq:green-gradient` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

The displayed `eq:green-gradient` has two relations, `|g_m(y)-g_m(z)| <= C(1+|y|)^{1-d}` and ("hence") `Gamma_m(y) <= C(1+|y|)^{2-2d}`.  The frozen Prop `Parking.External.GreenGradient d` transcribes the first faithfully: `exists C > 0` before `m, y, z`, `1 <= m`, `z in nbrFinset y`, exponent `1 - (d:ℝ)` with `|y| = graphNorm y`.  The second (Gamma) relation is *not* in the node; this is a deliberate weakening recorded in `tools/check_clauses.py` and is harmless because the only dependent node, `lem-gamma-sum`, carries this gradient bound as its hypothesis `hgrad` and proves the Gamma bound from it.  No `d >= 2` restriction is imposed (the bound is meaningful for `d >= 1` and vacuous for `d = 0`, which is outside the paper's setting).

## 2. Proof

The companion theorem `Parking.External.greenGradient` (same file) proves the Prop; the targeted probe reports its closure as `[propext, Classical.choice, Quot.sound]`.

`Parking.External.GreenGradient` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

Satisfiable for every `d >= 1` (Green's function is finite and the neighbour sum is over `2d` sites); the conclusion is a real inequality between finite reals, not a junk value.

## 4. Citations

A genuine cited input: the docstring attributes it to Lawler-Limic; the paper's "hence" is a consequence, not the source of the node.

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
'Parking.External.GreenGradient' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
