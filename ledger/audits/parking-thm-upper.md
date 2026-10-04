# Audit — `thm-upper`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `thm-upper` |
| version | 6 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.upper` |
| file | `Parking/Frozen/Upper.lean` |
| paper source | parking.tex:1418-1431 (label thm:upper); the GreenNorms hypothesis is dropped, discharged internally from Parking.External.greenNorms; the UConcentration hypothesis is likewise dropped, discharged internally from Parking.External.uConcentration |
| frozen sha256 | `4fd27b4c786aaaec3fde52cb928b0383b1df8d58ca056f5e17152ca8ddeafbad` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.upper (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    ∃ C : ℝ, 0 < C ∧
      (∀ n : ℕ, 2 ≤ n → Integrable (fun ω => (Parking.U ω n 0 : ℝ)) (Parking.law d ν) ∧
        Parking.meanU (Parking.law d ν) n
          ≤ C * (Parking.meanu (Parking.law d ν) n + Real.log n)) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
        Integrable (fun ω => (Parking.U ω n 0 : ℝ) ^ r) (Parking.law d ν) ∧
        (∫ ω, (Parking.U ω n 0 : ℝ) ^ r ∂(Parking.law d ν)) ^ (1 / r)
          ≤ C * (Parking.meanu (Parking.law d ν) n
              + Real.sqrt r * Parking.l2Norm (Parking.green d n)
              + r * Parking.greenMax d n
              + r * ((n : ℝ) + 1) ^ (2 / r) * Parking.kappa d n))
```

Cited `parking.tex` statement:

```latex
\begin{theorem}[Critical upper bound]\label{thm:upper}
	Let $\eta=(\eta(x))_{x\in\Z^d}$ be independent copies of a nonconstant integer-valued
	$\eta(0)$ which has mean zero and satisfies $\E e^{\theta|\eta(0)|}<\infty$ for
	some $\theta>0$. There is $C<\infty$ such that, for every $n\geq2$,
	\begin{equation}\label{eq:target}
		\E U_n(0)\leq C\bigl(\E u_n(0)+\log n\bigr)\,.
	\end{equation}
	More generally, for every $r\geq2$,
	\begin{equation}\label{eq:critical-moment}
		\bigl(\E U_n(0)^r\bigr)^{1/r}
		\leq C\bigl(\E u_n(0)+\sqrt r\,\|g_n\|_2+r\max_xg_n(x)
		+r(n+1)^{2/r}\kappa_d(n)\bigr)\,.
	\end{equation}
\end{theorem}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> two displays (eq:target for n>=2, eq:critical-moment for r>=2); Lean has one `exists C` (0<C, after d and nu, so depends on d and the law) outside two conjuncts, each carrying an added `Integrable` fact next to the inequality: (i) forall n>=2, meanU <= C(meanu + log n); (ii) forall n>=1, forall real r>=2, (int U^r)^{1/r} <= C(meanu + sqrt r ||g_n||_2 + r max g_n + r(n+1)^{2/r} kappa_d(n)) (n-range widened from the paper's n>=2, same C for both displays); ||g_n||_2 = `l2Norm (green d n)`, max_x g_n = `greenMax`, E U_n(0) = `meanU`, E u_n(0) = `meanu`; hypotheses 'nonconstant, integer valued, mean zero, exponential moment' = `CriticalLaw nu`; two extra hypotheses hGrowth, hBernstein are the cited results the proof quotes; UConcentration and GreenNorms are proved internally and are not among the hypotheses

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
'Parking.Frozen.upper' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.upper` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

`C` is bound before `n` and `r`; all terms on the right are finite nonnegative quantities and the `Integrable` conjuncts guard the left sides. The `n≥1` range for the moment bound is only wider than the paper's `n≥2`.

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

