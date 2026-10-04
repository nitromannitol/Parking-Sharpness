# Audit — `ext-green-norms`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `ext-green-norms` |
| version | 2 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.External.greenNorms` |
| file | `Parking/External/GreenNormsProved.lean` |
| paper source | parking.tex:1383-1400 (label eq:green-norms); no longer assumed, discharged from LatticeProb.Walk.VarianceScale and LatticeProb.Walk.SRWGreenSup, with the max-norm lower bound proved here from LatticeProb.Walk.SRWDiag.exists_srwHeat_diag_lower |
| frozen sha256 | `b3b650d756d9f8218c5f50ebea09861e8c7b459b4a1dae1cd95682bcb7ab0e34` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `no` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
/-- The two-sided rates of `eq:green-norms`, proved rather than assumed. -/
theorem Parking.External.greenNorms : Parking.External.GreenNorms
```

Cited `parking.tex` statement:

```latex
\begin{equation}\label{eq:green-norms}
	\|g_n\|_2\asymp
	\begin{cases}
		n^{3/4}&d=1\\
		n^{1/2}&d=2\\
		n^{1/4}&d=3\\
		\sqrt{\log n}&d=4\\
		1&d\geq5
	\end{cases}
	\qquad
	\max_xg_n(x)\asymp
	\begin{cases}
		n^{1/2}&d=1\\
		\log n&d=2\\
		1&d\geq3
	\end{cases}
	\,.
\end{equation}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> cited input (Bou-Rabee-Panagiotis Section 3.1), proved rather than assumed (`Parking.External.greenNorms`, from the shared library's Green kernel estimates); the display holds two relations `asymp` and Lean has two conjuncts, each with its own `exists c C > 0`, inside `forall d >= 1` so the constants depend on d only, each valid for all `n >= 2` (the paper's 'throughout the range'); l2 rates n^{3/4}, n^{1/2}, n^{1/4}, sqrt(log n), 1 for d = 1, 2, 3, 4, >=5; max rates n^{1/2}, log n, 1 for d = 1, 2, >=3; g_n = sum_{j<n} P^j(0,.) is `green d n`, `l2Norm` is sqrt of the tsum of squares (finite support), `greenMax` the iSup

The statement-integrity checks that matter here are: hypotheses, quantifier order,
domains, exponents and units. `tools/check_constants.py` reports `no` for this
node (every existential constant is bound before every paper parameter, so it is a
genuine constant). `tools/check_exponents.py` reports every paper exponent either present
in the Lean statement or explicitly explained. `tools/paper_anchors.py` resolves the
source line range from its LaTeX label.

No discrepancy with the paper statement was found in hypotheses, quantifier order, domains, exponents or units.

## 2. Proof and axiom closure

The proof compiles (`lake build Parking`, 10371 jobs) and its axiom closure is exactly the
three standard foundational axioms:

```
'Parking.External.greenNorms' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.External.greenNorms` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

The frozen statement asserts the full structure `Parking.External.GreenNorms`, whose two `≍` displays are two-sided bounds between strictly positive finite quantities for `n≥2`; it is not `True`.

## 4. Citations

`External` hypotheses carried by the frozen block:

| External | manifest node | paper origin | state |
|---|---|---|---|
| `Parking.External.GreenNorms` | `ext-green-norms` | parking.tex:1383-1400 (eq:green-norms, proved in GreenNormsProved.lean) | SEALED |
| `Parking.External.greenNorms` | (not a manifest node) | - | - |

Each is a genuine cited input (a result the paper cites or quotes, not a step the paper
itself proves in the cited range). The frozen block itself has no hypothesis; it proves the `GreenNorms` structure. The `Parking.External.GreenNorms` mention is the target proposition being discharged, not an assumed input.

## Refutation attempts

- Re-derived the paper statement from `parking.tex` and compared hypotheses, quantifier
  order, domains, exponents and units clause by clause; no weakening of the conclusion was
  found.
- Re-ran the frozen-statement hash, the axiom-closure gate, the constant-order gate, the
  exponent gate, the clause gate, the coverage gate and the warning gate; all pass.
- Looked for an unsatisfiable hypothesis or a junk conclusion (`0`, `sInf ∅`, a non-summable
  `tsum`, `Set.ncard` on an infinite set, `True`); none found.
- Checked that every `External` is a quoted input rather than a paper step.

No confirmed defect. Verdict: **PASS**.

