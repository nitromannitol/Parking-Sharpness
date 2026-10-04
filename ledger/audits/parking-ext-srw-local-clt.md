# Audit report -- `ext-srw-local-clt`

| field | value |
|---|---|
| manifest id | `ext-srw-local-clt` |
| version / kind / state | `2` / `theorem` / `SEALED` |
| Lean export | `Parking.External.srwLocalCLT` |
| source | `parking.tex:1756-1767 (prop:spatial-scaling, quoted from BP eq. (25), citing Lawler-Limic Thm 2.1.3 Eq. (2.8)); proved from the local central limit theorem of the divisible sandpile formalization, Sandpile.External.localCLT, via the heat-kernel identification` |
| file | `Parking/External/SRWLocalCLTBridge.lean` |
| frozen SHA-256 | `e5ec13cee5a5a6f90b0aaa7e8ec6351dc9e22c49827305b88452c30d25182f46` |
| paper label | `(none)` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

The paper's Step 1 (`parking.tex:1756-1767`) only *cites* BP eq. (25); the frozen Prop `Parking.External.SRWLocalCLT` is that uniform local CLT unfolded: `forall d >= 1, delta T C0` with `0 < delta <= T`, `0 <= C0`, then `forall eps > 0, exists R0, forall R >= R0`, for all layers `delta R^2 <= l <= T R^2` and sites `|x-y|^2 <= (C0 R)^2` with positive heat, `R^d |srwHeat d l (x-y) - 2 R^{-d} contHeatKernel d (l/R^2) (x/R) (y/R)| < eps`.  The factor `2` is the bipartite parity correction and `contHeatKernel` is the `(2d)^{-1}Delta` heat kernel, matching BP eq. (25) as recorded in `tools/check_clauses.py`.  The `eps`-uniform form is the standard unfolding of `lim R^d sup ... = 0`.

## 2. Proof

Companion `Parking.External.srwLocalCLT` proved from the local CLT of the divisible sandpile formalization through the heat-kernel identification; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.External.srwLocalCLT` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

Satisfiable (e.g. `delta = T = 1`, `C0 = 1`); the inequality is between finite reals and carries no junk value.

## 4. Citations

Genuine cited input: BP eq. (25), citing Lawler-Limic Thm 2.1.3 Eq. (2.8).

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
'Parking.External.srwLocalCLT' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
