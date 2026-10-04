# Audit — `thm-oriented`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `thm-oriented` |
| version | 4 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.oriented` |
| file | `Parking/Frozen/Oriented.lean` |
| paper source | parking.tex:3072-3085 (label thm:oriented) |
| frozen sha256 | `8ae751db70d9861676a438b36775eb8ac512779db25209095fc10934e6eae2f2` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.oriented (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ)
    (hprob : IsProbabilityMeasure ν) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν = 0) :
    (d = 2 → ∀ r : ℝ, 4 < r → Integrable (fun k : ℤ => |(k : ℝ)| ^ r) ν →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        Parking.meanuOriented (Parking.orientedLaw d ν) n ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4)) ∧
    (3 ≤ d → ∀ θ : ℝ, 0 < θ → Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        Parking.meanuOriented (Parking.orientedLaw d ν) n ≤ C * Real.log ((n : ℝ) + 1)) ∧
    (0 < evariance (fun k : ℤ => (k : ℝ)) ν → evariance (fun k : ℤ => (k : ℝ)) ν < ⊤ →
      ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
        c * Real.sqrt (Parking.orientedKappa d n)
          ≤ Parking.meanuOriented (Parking.orientedLaw d ν) n)
```

Cited `parking.tex` statement:

```latex
\begin{theorem}[Divisible odometer]\label{thm:oriented}
	Let $\eta=(\eta(x))_{x\in\Z^d}$ be i.i.d.\ with mean zero, and let $\vec u_n$
	obey \eqref{eq:oriented-divisible}. The following bounds hold for $n\geq1$.
	If $d=2$ and $\E|\eta(0)|^r<\infty$ for some $r>4$, then
	\[
		\E \vec u_n(0)\leq Cn^{1/4}.
	\]
	If $d\geq3$ and $\E e^{\theta|\eta(0)|}<\infty$ for some $\theta>0$, then
	\[
		\E \vec u_n(0)\leq C\log(n+1).
	\]
	If $\eta(0)$ has positive finite variance, then
	$\E \vec u_n(0)\geq c\sqrt{\vec\kappa_d(n)}$.
\end{theorem}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> three assertions as three conjuncts (d = 2 upper, d >= 3 upper, lower); `2 <= d` as in the section; the law is `nu : Measure ℤ`, integer-valued only (see MISMATCHES); standing hypotheses `hprob`, `hint` (|k| integrable, implicit in 'mean zero') and `hmean`; d = 2: `forall r > 4` with the r-th moment finite, `exists C`, `E u_n(0) <= C n^{1/4}` for all n >= 1; d >= 3: `forall theta > 0` with exponential moment, `exists C`, `<= C log(n+1)`; lower: `0 < evariance < top` gives `exists c > 0`, `c sqrt(kappa_d(n)) <= E u_n(0)` for all n >= 1, with kappa = sqrt n (d = 2), log(n+1) (d = 3), 1 (d >= 4) as `orientedKappa`, no exponential-moment hypothesis; `forall r/theta` then `exists C` equals the paper's 'for some r/theta' since the conclusion does not mention them; C may depend on d, nu (and r, theta); `E u_n(0)` is `meanuOriented (orientedLaw d nu) n` with `(P f)(x) = (1/d) sum_i f(x - e_i)`

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
'Parking.Frozen.oriented' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.oriented` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

Positive finite variance is required for the lower bound; the upper bounds are on a nonnegative `meanuOriented`; the quantifier order (`∃C` after `r`/`θ`) matches the paper's 'for some r/θ'.

## 4. Citations

No `Parking.External` hypothesis; depends on internal support files.

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

