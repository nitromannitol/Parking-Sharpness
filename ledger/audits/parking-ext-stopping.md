# Audit report -- `ext-stopping`

| field | value |
|---|---|
| manifest id | `ext-stopping` |
| version / kind / state | `2` / `definition` / `SEALED` |
| Lean export | `Parking.External.Stopping` |
| source | `parking.tex:876-884 (label lem:stopping, quoted from BPRS Theorem 3.2, proved in the shared library)` |
| file | `Parking/External/Stopping.lean` |
| frozen SHA-256 | `6ba333d59e5f37993fb576c66dab3f8c71fb5d8d3aa31ba9ff9375ee9b7cd731` |
| paper label | `lem:stopping` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

`lem:stopping` (`parking.tex:876-884`, quoted from BPRS Thm 3.2) is transcribed as the Prop `Parking.External.Stopping`: for `d >= 1`, every real configuration `eta`, `n >= 0` and `x`, `IsLUB (zdStopValues eta n x) (Parking.u eta n x)`.  `zdStopValues` is the set of `E_x sum_{k<tau} eta(X_k)` over walk stopping times `tau <= n`; writing the sup as a least upper bound is faithful and excludes an unattained/unbounded junk supremum.  The normalisation (`u` from `u_{n+1} = max 0 (eta + walkOp u_n)`) matches the paper's divisible odometer.

## 2. Proof

Companion `Parking.External.stopping` (same file) proves it via `LatticeProb.Graph.Zd.parkingStopping'`; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.External.Stopping` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

`eta = 0` makes `u_n = 0` and `zdStopValues = {0}`, whose lub is `0`, so the statement is satisfiable and non-vacuous.

## 4. Citations

Genuine cited input: BPRS Theorem 3.2, as the paper says.

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
'Parking.External.Stopping' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
