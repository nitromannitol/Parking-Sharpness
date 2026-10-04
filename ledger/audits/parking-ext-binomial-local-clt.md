# Audit report -- `ext-binomial-local-clt`

| field | value |
|---|---|
| manifest id | `ext-binomial-local-clt` |
| version / kind / state | `3` / `theorem` / `SEALED` |
| Lean export | `Parking.External.binomialLocalCLT` |
| source | `parking.tex:3207-3218 (proved from LatticeProb.BinomialLCLT.exists_binomPMF_localCLT)` |
| file | `Parking/External/BinomialLocalCLTProved.lean` |
| frozen SHA-256 | `ee97bed17735cd5eb5a558342738d1436f6f7b1bf4f2b18c910a2a56b2e4875b` |
| paper label | `(none)` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

The paper at `parking.tex:3207-3218` states no formula: it only says that "the binomial local central limit theorem gives convergence of the convolved potentials".  The node's frozen block is `theorem Parking.External.binomialLocalCLT : Parking.External.BinomialLocalCLT`, and the Prop body (unfrozen, `Parking/External/BinomialLocalCLT.lean`) is the explicit quantitative statement it consumes: `exists C > 0, forall m >= 1, forall j : Z` with `(j - m) % 2 = 0`, `|sqrt m * binomLaw m ((j+m)/2) - 2 exp(-(j/sqrt m)^2/2)/sqrt(2*pi)| <= C/m`.  This is exactly the `C/m` error that the proof sums over the `O(n)` layers; the parity hypothesis is necessary because the walk is bipartite.  The reading is against the cited local CLT, not against a `parking.tex` display, and the manifest says so.

## 2. Proof

The companion proof `binomialLocalCLT_proof` derives it from `LatticeProb.BinomialLCLT.exists_binomPMF_localCLT` and an elementary Gaussian tail bound; the frozen theorem is proved by it.

`Parking.External.binomialLocalCLT` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

The left-hand side is a genuine lattice probability and `binomLaw` is honestly zero off `[0,m]`; `C = C0 + 4/sqrt(2*pi)` is explicit and the bound is non-trivial at `j` even with `|j| <= m`.  No `0`, `sInf ∅`, non-summable `tsum` or `True` appears.

## 4. Citations

This is claimed as the cited binomial local CLT (docstring: Lawler-Limic Thm 2.1.1 / Spitzer P7.6), a genuine external input, not a step of `parking.tex`.

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
'Parking.External.binomialLocalCLT' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
