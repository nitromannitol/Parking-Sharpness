# Audit — `lem-gamma-sum`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `lem-gamma-sum` |
| version | 2 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.gamma_sum` |
| file | `Parking/Frozen/GammaSum.lean` |
| paper source | parking.tex:1057-1062 (label lem:gamma-sum) |
| frozen sha256 | `692c19d009a8409875839f82436d7074482d48dd1e17c3a87163c889dc36c5a5` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.gamma_sum (d : ℕ) (hd : 1 ≤ d)
    (hgrad : 2 ≤ d → Parking.External.GreenGradient d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Summable (fun y : Parking.Site d => ⨆ m ∈ Set.Iic n, Parking.gamma d m y) ∧
        ∑' y : Parking.Site d, (⨆ m ∈ Set.Iic n, Parking.gamma d m y)
          ≤ C * Parking.kappa d n
```

Cited `parking.tex` statement:

```latex
\begin{lemma}\label{lem:gamma-sum}
	For every $n\geq1$,
	\begin{equation}\label{eq:gamma-sum}
		\sum_y\sup_{m\leq n}\Gamma_m(y)\leq C\kappa_d(n)\,.
	\end{equation}
\end{lemma}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> one display; Lean asserts two conjuncts (`Summable` of y |-> sup_{m<=n} Gamma_m(y), and tsum <= C kappa_d(n)) with `exists C` (0<C) outside `forall n>=1`, so C depends on d only; sup over m<=n is `⨆ m ∈ Set.Iic n` (m=0 contributes 0, no junk effect since Gamma>=0), Gamma_m = `gamma d m y` = sum_{z~y}(1/2d)(g_m(z)-(Pg_m)(y))^2 with g_m = `green`, kappa = `kappa` (sqrt n, log(n+2), 1); extra hypothesis not in the lemma: `hgrad : 2<=d -> GreenGradient d` (eq:green-gradient, cited from Lawler-Limic; proved as External.greenGradient)

The statement-integrity checks that matter here are: hypotheses, quantifier order,
domains, exponents and units. `tools/check_constants.py` reports `yes` for this
node (every existential constant is bound before every paper parameter, so it is a
genuine constant). `tools/check_exponents.py` reports every paper exponent either present
in the Lean statement or explicitly explained. `tools/paper_anchors.py` resolves the
source line range from its LaTeX label.

No discrepancy with the paper statement was found in hypotheses, quantifier order, domains, exponents or units.

## 2. Proof and axiom closure

The proof compiles (`lake build Parking`, 10371 jobs) and its axiom closure is exactly the
three standard foundational axioms:

```
'Parking.Frozen.gamma_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.gamma_sum` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

`gamma d m y ≥ 0`; the supremum over `m ∈ Iic n` is nonnegative, the summands are nonnegative, and `kappa` is positive, so the `tsum ≤ C κ` is a real two-sided content statement and the `Summable` conjunct rules out the junk `0`.

## 4. Citations

`External` hypotheses carried by the frozen block:

| External | manifest node | paper origin | state |
|---|---|---|---|
| `Parking.External.GreenGradient` | `ext-green-gradient` | parking.tex:1030-1034 (eq:green-gradient, Lawler-Limic, proved in the shared library) | SEALED |

Each is a genuine cited input (a result the paper cites or quotes, not a step the paper
itself proves in the cited range). 

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

