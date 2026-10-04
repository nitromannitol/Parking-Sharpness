# Audit report -- `ext-u-concentration`

| field | value |
|---|---|
| manifest id | `ext-u-concentration` |
| version / kind / state | `2` / `theorem` / `SEALED` |
| Lean export | `Parking.External.uConcentration` |
| source | `parking.tex:1402-1413 (label lem:u-concentration, quoted from BP Remark 3.4); proved outright from the coordinate-Lipschitz bound with the Green function as weights and the library's weighted exponential concentration, no longer assumed` |
| file | `Parking/External/UConcentrationProved.lean` |
| frozen SHA-256 | `bad8609416d0b1a54c0482b313694c8f3974b12104a5e8ba02e9f5e5eb3a4be8` |
| paper label | `lem:u-concentration` |
| auditor | BATCH A, independent; leaf-first topological half. Date 2026-10-04. |
| verdict | **PASS** |

## 1. Statement integrity

`lem:u-concentration` (`parking.tex:1402-1413`, BP Remark 3.4) is transcribed by `Parking.External.UConcentration`: `d >= 1`, a finite-range translation-invariant kernel `r, K`, `nu` a probability law on `ℝ` with `theta > 0` and `E e^{theta|z|} < inf`, then `exists C > 0` before `n >= 1` and the real moment order `q >= 2`, with `(E |v_n(0) - E v_n(0)|^q)^{1/q} <= C (sqrt q ||g_n^K||_2 + q ||g_n^K||_inf)`.  The Lean `r` is the kernel range and `q` the moment order; `v_n = kSol`, `g_n^K = kGreen`, the two norms are `l2Norm`/`supAbs`.  The paper's "for some `theta > 0`" is the universal `theta` binder, which is equivalent because `C` is chosen after `theta`.

## 2. Proof

Companion `Parking.External.uConcentration` proved from the coordinate-Lipschitz bound with Green weights and the library's weighted exponential concentration; closure `[propext, Classical.choice, Quot.sound]`.

`Parking.External.uConcentration` is in the manifest's exported surface and its axiom closure is exactly
`{propext, Classical.choice, Quot.sound}`; `python3 tools/check_axioms.py` exits 0.

## 3. Non-vacuity / junk

Satisfiable with the simple-random-walk kernel (`r = 1`) and a centred law with an exponential moment; `v_n(0)` reads only finitely many sites, so the integrals are not junk.

## 4. Citations

Genuine cited input: BP Remark 3.4.

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
'Parking.External.uConcentration' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Full output is in `ledger/audits/parking-2026-10-04.md` under "Gate commands".

---
*This report was produced by an independent auditor (BATCH A).  It contains no edit to any
Lean file and does not change any manifest state.*
