# Audit — `thm-subcritical-tail`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `thm-subcritical-tail` |
| version | 3 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.subcritical_tail` |
| file | `Parking/Frozen/SubcriticalTail.lean` |
| paper source | parking.tex:123-135 (label thm:subcritical-tail) |
| frozen sha256 | `e712ea0a1a96aa7a7a17e8ef1442bf6d1032ead517a7d344b8834c997dae4138` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.subcritical_tail
    (hDV : Parking.External.DonskerVaradhanRange)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν < 0)
    (hpos : 0 < ν (Set.Ioi 0))
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
      C⁻¹ * Real.exp (-(C * (t : ℝ) ^ ((d : ℝ) / (d + 2)))) ≤ Parking.S (Parking.law d ν) t ∧
        Parking.S (Parking.law d ν) t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((d : ℝ) / (d + 2))))
```

Cited `parking.tex` statement:

```latex
\begin{theorem}[Stretched-exponential settling time]\label{thm:subcritical-tail}
	Let $\eta=(\eta(x))_{x\in\Z^d}$ have i.i.d.\ integer-valued coordinates,
	with
	\[
		\E|\eta(0)|<\infty\,,\qquad \E\eta(0)<0\,,\qquad \P(\eta(0)>0)>0\,,
	\]
	and suppose that $\E e^{\theta\eta(0)}<\infty$ for some $\theta>0$. Then there are
	$0<c\leq C<\infty$ such that, for every $t\geq1$,
	\begin{equation}\label{eq:sharpness}
		\frac1C\exp\bigl\{-Ct^{d/(d+2)}\bigr\}\leq S_t\leq
		C\exp\bigl\{-ct^{d/(d+2)}\bigr\}\,.
	\end{equation}
\end{theorem}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> one display = two bounds; Lean `exists c C` with 0<c and c<=C before `forall t, 1<=t`, then the conjunction C^{-1} exp(-C t^{d/(d+2)}) <= S_t and S_t <= C exp(-c t^{d/(d+2)}), with exponent (d:R)/(d+2); hypotheses: nu an integer-valued probability law with integrable |k|, integral of k < 0, nu(0,inf)>0, exists theta>0 with E e^{theta k}<inf (one-sided, no absolute value, as in the paper), 1<=d; S_t is `S (law d nu) t`; hDV (Donsker-Varadhan) is a cited input used in the proof, not in the paper's statement

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
'Parking.Frozen.subcritical_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.subcritical_tail` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

Both bounds have explicit positive constants and exponents `d/(d+2)`; `1/C · exp(−C t^{d/(d+2)}) ≤ S_t` is a genuine lower bound, ruling out a junk `0`.

## 4. Citations

`External` hypotheses carried by the frozen block:

| External | manifest node | paper origin | state |
|---|---|---|---|
| `Parking.External.DonskerVaradhanRange` | `ext-donsker-varadhan` | parking.tex:117-121 (Donsker-Varadhan 1979, Theorem 1) | FROZEN |

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

