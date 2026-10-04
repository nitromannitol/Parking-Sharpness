# Audit — `cor-growth`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `cor-growth` |
| version | 6 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.growth` |
| file | `Parking/Frozen/Growth.lean` |
| paper source | parking.tex:174-188 (label cor:growth); the GreenNorms hypothesis is dropped, discharged internally from Parking.External.greenNorms; the UConcentration hypothesis is likewise dropped, discharged internally from Parking.External.uConcentration |
| frozen sha256 | `d1da411ce4edb3c61a1e43d3461c5fde454e68ffe39f5ceda220466ea45414fa` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.growth (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    (d ≤ 3 → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      (∀ n : ℕ, 2 ≤ n →
        c * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) ≤ Parking.meanU (Parking.law d ν) n ∧
          Parking.meanU (Parking.law d ν) n ≤ C * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) ∧
      (∀ t : ℕ,
        c * ((t : ℝ) + 1) ^ (-((d : ℝ) / 4)) ≤ Parking.S (Parking.law d ν) t ∧
          Parking.S (Parking.law d ν) t ≤ C * ((t : ℝ) + 1) ^ (-((d : ℝ) / 4)))) ∧
    (4 ≤ d → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      (∀ n : ℕ, 2 ≤ n →
        c * Real.log n ≤ Parking.meanU (Parking.law d ν) n ∧
          Parking.meanU (Parking.law d ν) n ≤ C * Real.log n) ∧
      (∀ t : ℕ,
        c / ((t : ℝ) + 1) ≤ Parking.S (Parking.law d ν) t ∧
          Parking.S (Parking.law d ν) t ≤ C * Real.log ((t : ℝ) + 2) / ((t : ℝ) + 1)))
```

Cited `parking.tex` statement:

```latex
\begin{corollary}[Growth at the critical density]\label{cor:growth}
	Under the assumptions of Theorem~\ref{thm:master},
	\begin{equation}\label{eq:growth}
		\E U_n(0)\asymp
		\begin{cases}
			n^{(4-d)/4}&d\leq3\,,\\
			\log n&d\geq4\,.
		\end{cases}
	\end{equation}
	When $d\leq3$, we have $S_t\asymp (t+1)^{-d/4}$ for every $t\geq0$.
	When $d\geq4$, there are $0<c\leq C<\infty$ such that, for every $t\geq0$,
	\begin{equation}\label{eq:activity}
		\frac{c}{t+1}\leq S_t\leq\frac{C\log(t+2)}{t+1}\,.
	\end{equation}
\end{corollary}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> paper makes four relations: E U_n(0) ≍ n^{(4-d)/4} (d<=3), E U_n(0) ≍ log n (d>=4), S_t ≍ (t+1)^{-d/4} (d<=3), and c/(t+1) <= S_t <= C log(t+2)/(t+1) (d>=4); Lean has two top-level conjuncts `d <= 3 -> exists c C ...` and `4 <= d -> exists c C ...`, each holding the E U_n bound (two-sided, forall n >= 2, the range of n is not stated in the paper and is taken as that of thm:master) and the S_t bound (forall t >= 0) with ONE shared pair 0 < c <= C (equivalent to the paper's separate constants, by taking min and max); c, C come after d and nu, so they depend on the dimension and the law only; the assumptions of thm:master are `CriticalLaw nu` (probability, nonconstant, mean zero, exponential moment) and d >= 1; Lean also takes the two cited externals hGrowth, hBernstein as hypotheses, which the paper's proof invokes but its statement does not list; UConcentration and GreenNorms are proved internally (`Parking.External.uConcentration`, `Parking.External.greenNorms`) and are not among the hypotheses; S_t is `Parking.S (law d nu) t`

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
'Parking.Frozen.growth' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.growth` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

All four relations are two-sided with `0<c≤C`; `S_t` is a genuine integral of a bounded survivor count.

## 4. Citations

`External` hypotheses carried by the frozen block:

| External | manifest node | paper origin | state |
|---|---|---|---|
| `Parking.External.Bernstein` | `ext-bernstein` | parking.tex:1175-1188 (lem:bernstein, Pinelis Theorems 4.1 and 3.3) | FROZEN |
| `Parking.External.SandpileGrowth` | `ext-sandpile-growth` | parking.tex:929-943 (thm:BP, Bou-Rabee-Panagiotis) | FROZEN |

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

