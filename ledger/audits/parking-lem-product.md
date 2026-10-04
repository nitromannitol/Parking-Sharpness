# Audit report -- `lem-product`

| field | value |
|---|---|
| manifest id | `lem-product` |
| version / kind / state | `5` / `theorem` / `SEALED` |
| Lean export | `Parking.Frozen.product` |
| source | `parking.tex:2336-2347 (label lem:product)` |
| file | `Parking/Frozen/Product.lean` |
| frozen SHA-256 | `392b048bfd4663cfadbe590a17abefc0c755213a60698da1d2bbbb452a08f12a` |
| paper label | `lem:product` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

`lem:product` (`parking.tex:2336-2347`) is transcribed with the tilted-law hypotheses, the finitely many sites `N`, the conditioning data `ω₀`, `F` in `[0,1]`, nondecreasing under `addAt`, `Z >= 0`, integrable, nonincreasing and `1`-Lipschitz under `addAt`/`delAt`, relabel invariance and dependence on `N`; the derivative `∂_λ E_λ F` is the hypothesis `hD : HasDerivAt (...) D lam`, and the conclusion is the paper's covariance bound `|Cov_λ(F,Z)| <= 3 D` (written as `|∫ FZ - ∫F ∫Z| <= 3 D`), plus an `Integrable (F*Z)` guard.  The one-sided exponential-moment hypothesis `Integrable (exp (θ k))` is weaker than the paper's `E e^{θ|η|}` and only restricts the family, never enlarges it.

## 2. Proof

In-repo; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.Frozen.product` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

Satisfiable with `F = Z = 0` (then `D = 0` and `|Cov| = 0 <= 0`); the covariance is a genuine real because of the `Integrable` guard.

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
'Parking.Frozen.product' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
