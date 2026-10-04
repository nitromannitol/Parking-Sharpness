# Audit — `prop-resolvent`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `prop-resolvent` |
| version | 2 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.resolvent` |
| file | `Parking/Frozen/Resolvent.lean` |
| paper source | parking.tex:2643-2663 (label prop:resolvent) |
| frozen sha256 | `904a892b5eb0c60d3b5f46918ea0554afefae252290a309362a97d3333a5363b` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.resolvent (d : ℕ) (hd : 1 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ a : ℝ, 0 < a → a ≤ 1 → ∀ t : ℕ, 1 ≤ t →
        (d = 1 → Parking.rangeExp d a t
            ≤ C * Real.exp (-(c * a ^ ((2 : ℝ) / 3) * (t : ℝ) ^ ((1 : ℝ) / 3)))) ∧
        (d = 2 → Real.exp 1 / a ≤ (t : ℝ) → Parking.rangeExp d a t
            ≤ C * Real.exp (-(c * Real.sqrt (a * t / Real.log ((t : ℝ) + 2))))) ∧
        (3 ≤ d → Parking.rangeExp d a t ≤ C * Real.exp (-(c * Real.sqrt (a * t))))) ∧
      ∀ a : ℝ, 0 < a → a ≤ 1 →
        Summable (fun t : ℕ => if Parking.resolventThreshold d C a < (t : ℝ)
            then Parking.rangeExp d a t else 0) ∧
          ∑' t : ℕ, (if Parking.resolventThreshold d C a < (t : ℝ)
            then Parking.rangeExp d a t else 0) ≤ 1
```

Cited `parking.tex` statement:

```latex
\begin{proposition}\label{prop:resolvent}
	There are $c,C>0$ such that, for $0<a\leq1$ and $t\geq1$,
	\begin{equation}\label{eq:resolvent-pointwise}
		\E_0e^{-a|R_t|}\leq C
		\begin{cases}
			\exp\{-ca^{2/3}t^{1/3}\}&d=1\,,\\
			\exp\{-c\sqrt{at/\log(t+2)}\}&d=2,\ t\geq e/a\,,\\
			\exp\{-c\sqrt{at}\}&d\geq3\,.
		\end{cases}
	\end{equation}
	Moreover, with $\Lambda=\log(e/a)$ and
	\begin{equation}\label{eq:range-threshold}
		T=C
		\begin{cases}
			a^{-2}\Lambda^3&d=1\,,\\
			a^{-1}\Lambda^3&d=2\,,\\
			a^{-1}\Lambda^2&d\geq3\,,
		\end{cases}
	\end{equation}
	the sum $\sum_{t>T}\E_0e^{-a|R_t|}$ is at most one.
\end{proposition}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> two assertions (pointwise bound, then tail sum <= 1); Lean is `exists c C, 0 < c, 0 < C` after d (so c and C may depend on d) then two conjuncts: (A) forall a in (0,1], forall t >= 1, three implications: d = 1 -> E_0 e^{-a|R_t|} <= C exp(-c a^(2/3) t^(1/3)); d = 2 -> e/a <= t -> ... <= C exp(-c sqrt(a t / log(t+2))); 3 <= d -> ... <= C exp(-c sqrt(a t)); (B) forall a in (0,1], Summable (guard, not in the paper) and sum over t > T of E_0 e^{-a|R_t|} <= 1, where T = `resolventThreshold d C a` is the SAME C times a^(-2) L^3 (d = 1), a^(-1) L^3 (d = 2), a^(-1) L^2 (d >= 3), L = log(e/a); the paper's C in T is read as the same C (equivalent to a possibly larger one, both bounds being monotone in C); E_0 e^{-a|R_t|} is `rangeExp d a t`, an integral over `walkLaw d`

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
'Parking.Frozen.resolvent' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.resolvent` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

`rangeExp` is a nonnegative integral of `exp(-a·rangeCard)`; both inequalities are finite and the `Summable` guard precludes a junk `tsum` (the `if` has finite support only if the exponential decays, which is asserted).

## 4. Citations

No `Parking.External` hypothesis; depends on the internal support file `Parking.Support.RangeResolvent`.

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

