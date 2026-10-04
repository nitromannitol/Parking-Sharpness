# Audit — `prop-w-moment`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `prop-w-moment` |
| version | 5 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.w_moment` |
| file | `Parking/Frozen/WMoment.lean` |
| paper source | parking.tex:1202-1215 (label prop:w-moment) |
| frozen sha256 | `ddde27a9a9b8ee94a38ac0fe2bfa7103ced6eba69b883f493f20e12fb1cbb535` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.w_moment (hBernstein : Parking.External.Bernstein) (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : Measure ℤ, IsProbabilityMeasure ν → ∀ θ : ℝ, 0 < θ →
      Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν →
      ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
      (∀ m ≤ n, Integrable (fun ω => |Parking.wErr ω m 0| ^ r) (Parking.law d ν)) ∧
      Integrable (fun ω => Parking.wStar ω n 0 ^ r) (Parking.law d ν) ∧
      (⨆ m ∈ Set.Iic n,
          (∫ ω, |Parking.wErr ω m 0| ^ r ∂(Parking.law d ν)) ^ (1 / r))
        ≤ C * (Real.sqrt (r * Parking.kappa d n *
            (∫ ω, (Parking.U ω n 0 : ℝ) ^ r ∂(Parking.law d ν)) ^ (1 / r)) + r) ∧
      (∫ ω, Parking.wStar ω n 0 ^ r ∂(Parking.law d ν)) ^ (1 / r)
        ≤ ((n : ℝ) + 1) ^ (1 / r) * ⨆ m ∈ Set.Iic n,
            (∫ ω, |Parking.wErr ω m 0| ^ r ∂(Parking.law d ν)) ^ (1 / r)
```

Cited `parking.tex` statement:

```latex
\begin{proposition}\label{prop:w-moment}
	Let $\eta=(\eta(x))_{x\in\Z^d}$ have i.i.d.\ integer-valued coordinates,
	with $\E e^{\theta\eta(0)^+}<\infty$ for some $\theta>0$. There is a
	dimension-dependent $C<\infty$ such that, for every $n\geq1$ and $r\geq2$,
	\[
		\max_{m\leq n}\bigl(\E|w_m(0)|^r\bigr)^{1/r}
		\leq C\Bigl(\sqrt{r\kappa_d(n)\bigl(\E U_n(0)^r\bigr)^{1/r}}
		+r\Bigr)\,,
	\]
	\[
		\bigl(\E w_n^\star(0)^r\bigr)^{1/r}
		\leq(n+1)^{1/r}\max_{m\leq n}\bigl(\E|w_m(0)|^r\bigr)^{1/r}\,.
	\]
\end{proposition}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> two displays (max_{m<=n}(E|w_m(0)|^r)^{1/r} <= C(sqrt(r kappa_d(n)(E U_n(0)^r)^{1/r}) + r), and (E w*_n(0)^r)^{1/r} <= (n+1)^{1/r} max_{m<=n}(E|w_m(0)|^r)^{1/r}, no constant); Lean has `exists C` (0<C, d only, bound before nu, theta, n, r, matching 'dimension-dependent') and four conjuncts: added `Integrable` of |w_m(0)|^r for all m<=n and of w*_n(0)^r, then the two displays, max over m<=n as `⨆ m ∈ Set.Iic n` (values >=0, no junk effect); 'E e^{theta eta(0)^+}<infty' = `Integrable (exp(theta * max k 0)) nu` with nu an integer probability law; w_m = `wErr`, w*_n = `wStar` (average over the independent walk); integrability of U_n(0)^r is not asserted, and a junk 0 there would only strengthen the claim; extra hypothesis `hBernstein`

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
'Parking.Frozen.w_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.w_moment` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

'Integrable' conjuncts guard both sides; the bound is on the `⨆` of nonnegative quantities, so it cannot be satisfied by a junk value.

## 4. Citations

`External` hypotheses carried by the frozen block:

| External | manifest node | paper origin | state |
|---|---|---|---|
| `Parking.External.Bernstein` | `ext-bernstein` | parking.tex:1175-1188 (lem:bernstein, Pinelis Theorems 4.1 and 3.3) | FROZEN |

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

