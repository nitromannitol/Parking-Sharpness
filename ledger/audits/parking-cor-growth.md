# Audit report -- `cor-growth`

| field | value |
|---|---|
| manifest id | `cor-growth` |
| version / kind / state | `6` / `theorem` / `SEALED` |
| Lean export | `Parking.Frozen.growth` |
| source | `parking.tex:174-188 (label cor:growth); the GreenNorms hypothesis is dropped, discharged internally from Parking.External.greenNorms; the UConcentration hypothesis is likewise dropped, discharged internally from Parking.External.uConcentration` |
| file | `Parking/Frozen/Growth.lean` |
| frozen SHA-256 | `d1da411ce4edb3c61a1e43d3461c5fde454e68ffe39f5ceda220466ea45414fa` |
| paper label | `cor:growth` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

`cor:growth` (`parking.tex:174-188`) is transcribed as two implications, `d <= 3` and `4 <= d`; each holds the two-sided `E U_n(0)` bound (exponent `(4-d)/4` resp. `log n`) and the `S_t` bound (`c (t+1)^{-d/4} <= S_t <= C (t+1)^{-d/4}` resp. `c/(t+1) <= S_t <= C log(t+2)/(t+1)`), for `n >= 2` and every `t`.  The paper's `asymp` is expanded into the explicit two-sided form; the single shared pair `0 < c <= C` is equivalent to separate constants by `min`/`max`.  `c, C` are bound after `d, nu`, so they depend on the dimension and the law only.

## 2. Proof

Proved in-repo from `Parking.External.SandpileGrowth`, `Parking.External.Bernstein` and the internal `meanU`/`S` bounds; frozen block proved.  Closure `[propext, Classical.choice, Quot.sound]`.

`Parking.Frozen.growth` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

`CriticalLaw nu` is satisfiable (e.g. `(+1)`/`(-1)` with probability `1/2`); all constants are positive and the `S` bounds are genuine (the `S_t` value is a finite expectation).

## 4. Citations

The two cited inputs `hGrowth : SandpileGrowth` and `hBernstein : Bernstein` are genuine external inputs; both are marked cited.

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
'Parking.Frozen.growth' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
