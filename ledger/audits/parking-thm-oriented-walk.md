# Audit — `thm-oriented-walk`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `thm-oriented-walk` |
| version | 6 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.oriented_walk` |
| file | `Parking/Frozen/OrientedWalk.lean` |
| paper source | parking.tex:363-380 (label thm:oriented-walk; binomial LCLT hypothesis discharged); the UConcentration hypothesis is likewise dropped, discharged internally from Parking.External.uConcentration |
| frozen sha256 | `72bc687530f00063c740a0cda60862370b3314efbdb74a347315d0f0a0995bfe` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.oriented_walk (hBern : Parking.External.Bernstein)
    (hStability : Parking.External.OrientedStoppingStability)
    (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ)
    (hν : Parking.CriticalLaw ν) :
    (d = 2 → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ Parking.meanU (Parking.orientedLaw d ν) n ∧
        Parking.meanU (Parking.orientedLaw d ν) n ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4)) ∧
    (3 ≤ d → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * Real.log n ≤ Parking.meanU (Parking.orientedLaw d ν) n ∧
        Parking.meanU (Parking.orientedLaw d ν) n ≤ C * Real.log n) ∧
    (d = 2 →
      Tendsto (fun n : ℕ => Parking.meanU (Parking.orientedLaw d ν) n /
        Parking.meanuOriented (Parking.orientedLaw d ν) n) atTop (𝓝 1) ∧
      ∃ μ : ℝ, 0 < μ ∧
        Tendsto (fun n : ℕ => Parking.meanU (Parking.orientedLaw d ν) n /
          (μ * (n : ℝ) ^ ((1 : ℝ) / 4))) atTop (𝓝 1) ∧
        Tendsto (fun t : ℕ => Parking.S (Parking.orientedLaw d ν) t /
          (μ / 4 * (t : ℝ) ^ (-(3 : ℝ) / 4))) atTop (𝓝 1))
```

Cited `parking.tex` statement:

```latex
\begin{theorem}[Oriented walk]\label{thm:oriented-walk}
	Let $\eta=(\eta(x))_{x\in\Z^d}$ have i.i.d.\ integer-valued coordinates.
	Suppose that $\eta(0)$ is nonconstant, $\E\eta(0)=0$, and
	$\E e^{\theta|\eta(0)|}<\infty$ for some $\theta>0$. Then
	\[
		\E \vec U_n(0)\asymp
		\begin{cases}
			n^{1/4}&d=2\,,\\
			\log n&d\geq3\,.
		\end{cases}
	\]
	When $d=2$, the order $n^{1/4}$ sharpens to an asymptotic: the ratio $\E \vec U_n(0)/\E \vec u_n(0)$ tends to one, and there is $\mu\in(0,\infty)$ such that
	\[
		\E \vec U_n(0)\sim\mu n^{1/4}
		\qquad\text{and}\qquad
		\vec S_t\sim\frac{\mu}{4}t^{-3/4}\,.
	\]
\end{theorem}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> five assertions: (a) E U_n(0) asymp n^{1/4} for d=2; (b) asymp log n for d>=3; (c) E U_n/E u_n -> 1 for d=2; (d) exists mu in (0,inf) with E U_n ~ mu n^{1/4}; (e) S_t ~ (mu/4) t^{-3/4}, here U, u, S are the oriented-walk quantities; Lean has three top-level conjuncts: (a) as `d=2 -> exists c C` (0<c<=C, forall n>=2, exponent 1/4); (b) as `3<=d ->` the same with Real.log n; (c),(d),(e) together under one `d=2 ->`, (c) first, then `exists mu>0` scoping over both (d) and (e); ~ is written as ratio -> 1, with S_t/((mu/4) t^{-3/4}), exponent (-(3:R))/4; hypotheses: 2<=d (the paper's cases start at d=2) and CriticalLaw nu (integer-valued probability law, nonconstant, mean 0, exponential moment); the walk is `orientedLaw` (steps +e_i with probability 1/d), u is `uOriented` with P f(x) = (1/d) sum_i f(x-e_i), meanU and meanuOriented are taken under `orientedLaw d nu`; hBern, hStability are cited inputs, not in the paper's statement; UConcentration and the binomial local CLT `prop:oriented-scaling` also cites are each proved internally, discharged from `Parking.External.uConcentration` and `Parking.External.binomialLocalCLT` respectively, and are not among the hypotheses

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
'Parking.Frozen.oriented_walk' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.oriented_walk` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

The `~` are stated as ratios tending to `1` with an explicit positive `μ`; `S_t` is a genuine survivor expectation and the exponent `−3/4` is present.

## 4. Citations

`External` hypotheses carried by the frozen block:

| External | manifest node | paper origin | state |
|---|---|---|---|
| `Parking.External.Bernstein` | `ext-bernstein` | parking.tex:1175-1188 (lem:bernstein, Pinelis Theorems 4.1 and 3.3) | FROZEN |
| `Parking.External.OrientedStoppingStability` | `ext-oriented-stopping-stability` | parking.tex:3214-3218 (cutoff and stability of the parabolic scaling limit) | FROZEN |

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

