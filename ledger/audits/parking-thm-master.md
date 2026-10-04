# Audit — `thm-master`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `thm-master` |
| version | 7 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.master` |
| file | `Parking/Frozen/Master.lean` |
| paper source | parking.tex:159-168 (label thm:master); the GreenNorms hypothesis is dropped, discharged internally from Parking.External.greenNorms; the UConcentration hypothesis is likewise dropped, discharged internally from Parking.External.uConcentration |
| frozen sha256 | `5c61e58f3c26c9676c32158f4f7a27a0bfc8487d0d696bda8e44cb8c9726224e` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.master (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    (hnonconst : ∀ k : ℤ, ν {k} ≠ 1) (hmean : ∫ k, (k : ℝ) ∂ν = 0)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * (Parking.meanu (Parking.law d ν) n + Real.log n) ≤ Parking.meanU (Parking.law d ν) n ∧
        Parking.meanU (Parking.law d ν) n ≤ C * (Parking.meanu (Parking.law d ν) n + Real.log n)
```

Cited `parking.tex` statement:

```latex
\begin{theorem}[Comparison of the two expected odometers]\label{thm:master}
	Let $\eta=(\eta(x))_{x\in\Z^d}$ have i.i.d.\ integer-valued coordinates.
	Suppose that $\eta(0)$ is nonconstant, $\E\eta(0)=0$, and
	$\E e^{\theta|\eta(0)|}<\infty$ for some $\theta>0$. Then there are
	$0<c\leq C<\infty$ such that, for every $n\geq2$,
	\begin{equation}\label{eq:master}
		c\bigl(\E u_n(0)+\log n\bigr)\leq\E U_n(0)
		\leq C\bigl(\E u_n(0)+\log n\bigr)\,.
	\end{equation}
\end{theorem}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> one display = two inequalities; Lean `exists c c` with 0<c and c<=C outside `forall n, 2<=n`, then the conjunction c(E u_n(0)+log n) <= E U_n(0) and E U_n(0) <= C(E u_n(0)+log n); hypotheses as explicit binders: nu a probability measure on Z, nonconstant as `forall k, nu {k} <> 1`, mean 0, exists theta>0 (theta, hθ, hexp) with E e^{theta|k|}<inf, 1<=d; E U_n(0), E u_n(0) are meanU, meanu under `law d nu`; hGrowth, hBernstein are cited inputs the proof uses, not in the paper's statement; UConcentration and GreenNorms are proved internally and are not among the hypotheses; the remark after the display (lower bound needs no exponential moment) lies outside the source range and is not in Lean

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
'Parking.Frozen.master' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.master` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

`∃c C, 0<c ∧ c≤C` before `n`; both inequalities are two-sided and the lower bound forces `E U_n` to grow at least like `E u_n + log n`.

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

