# Audit report -- `lem-mean-horizon`

| field | value |
|---|---|
| manifest id | `lem-mean-horizon` |
| version / kind / state | `7` / `theorem` / `SEALED` |
| Lean export | `Parking.Frozen.mean_horizon` |
| source | `parking.tex:2779-2785 (label lem:mean-horizon); the GreenNorms hypothesis is dropped, discharged internally from Parking.External.greenNorms; the UConcentration hypothesis is likewise dropped, discharged internally from Parking.External.uConcentration` |
| file | `Parking/Frozen/MeanHorizon.lean` |
| frozen SHA-256 | `6926d5da22d72c7279aabddf848e96799375c655fc22a0e8f519e174cddc9b2c` |
| paper label | `lem:mean-horizon` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

`lem:mean-horizon` (`parking.tex:2779-2785`) is transcribed with the family hypotheses `NearFamily δ₀ ν θ M K`, a bounded walk stopping time `σ eta` with `σ eta X <= n`, measurability in `eta`, `Mσ = ∫ η ∫ X σ η X`, and the conclusion `E_eta E_walk sum_{j<σ} ξ_δ(X_j) <= C φ_d(Mσ)`, with an added `Integrable` guard.  `ξ_δ = Parking.xi δ η` and `φ_d` is `(s+1)^{(4-d)/4}` for `d <= 3` and `log(s+2)` otherwise, matching the paper.  `C` is bound after the whole family and before `δ, n, σ, Mσ`.

## 2. Proof

In-repo from the two cited inputs; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.Frozen.mean_horizon` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

`NearFamily` is satisfiable; `σ = 0` gives the empty sum `0 <= C φ_d(0)`, so the statement has content and no junk integral is asserted.

## 4. Citations

`SandpileGrowth` and `Stopping` are genuine cited inputs.

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
'Parking.Frozen.mean_horizon' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
