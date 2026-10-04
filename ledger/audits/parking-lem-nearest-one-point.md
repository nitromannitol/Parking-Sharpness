# Audit report -- `lem-nearest-one-point`

| field | value |
|---|---|
| manifest id | `lem-nearest-one-point` |
| version / kind / state | `4` / `theorem` / `SEALED` |
| Lean export | `Parking.Frozen.nearest_one_point` |
| source | `parking.tex:1882-1891 (label lem:nearest-one-point)` |
| file | `Parking/Frozen/NearestOnePoint.lean` |
| frozen SHA-256 | `ad47a2d8c2e972a16d012a10af516cdc05393b88fe5a1cd72714c7822425d071` |
| paper label | `lem:nearest-one-point` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

`lem:nearest-one-point` (`parking.tex:1882-1891`) is transcribed as `exists C > 0` before `p in (0,1/4]` (so `C` depends on `d` only), with the moment bound `(E U_t(x)^r)^{1/r} <= C (m_t + r)` for all `t, x, r >= 2`, the mean bound `m_t <= C log(1/h_t)`, `Antitone h` and `Tendsto h atTop (nhds 0)`.  Here `m_t = meanU = E U_t(0)` and `h_t = holeProb = P(H_t(0) = 1)`, matching `parking.tex:1873`; the added `Integrable` conjunct is a junk-value guard.  The paper's "`h_t ↓ 0`" is split into the `Antitone` and `Tendsto` conjuncts.

## 2. Proof

In-repo from the cited Bernstein inequality; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.Frozen.nearest_one_point` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

`p = 1/4` is admissible; the four conjuncts are genuine (the `1/h_t` denominator would only make the bound easier, and `h_t -> 0` is the paper's `h_t ↓ 0`).

## 4. Citations

`hBernstein : Bernstein` is a genuine cited input.

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
'Parking.Frozen.nearest_one_point' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
