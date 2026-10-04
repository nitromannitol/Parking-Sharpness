# Audit — `prop-near-divisible`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `prop-near-divisible` |
| version | 5 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.near_divisible` |
| file | `Parking/Frozen/NearDivisible.lean` |
| paper source | parking.tex:2844-2860 (label prop:near-divisible); the GreenNorms hypothesis is dropped, discharged internally from Parking.External.greenNorms; the UConcentration hypothesis is likewise dropped, discharged internally from Parking.External.uConcentration |
| frozen sha256 | `0a66e2a630ac012e90900b5b264d3dd297be2bee2a72649a9502e9e527b718a6` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.near_divisible (hGrowth : Parking.External.SandpileGrowth)
    (hStopping : Parking.External.Stopping)
    (d : ℕ) (hd : 1 ≤ d) (δ₀ : ℝ) (ν : ℝ → Measure ℤ)
    (θ M K : ℝ) (hfam : Parking.NearFamily δ₀ ν θ M K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ δ₀ ∧
      ∀ δ ∈ Set.Ioc (0 : ℝ) δ₁,
        Parking.meanuLimit (Parking.law d (ν δ))
            ≤ ENNReal.ofReal (C * Parking.nearRate d δ) ∧
          (d ≤ 4 → ENNReal.ofReal (c * Parking.nearRate d δ)
            ≤ Parking.meanuLimit (Parking.law d (ν δ))) ∧
          (5 ≤ d → ENNReal.ofReal (c * Real.log (Real.exp 1 / δ) ^ ((2 : ℝ) / d))
            ≤ Parking.meanuLimit (Parking.law d (ν δ))) ∧
          (5 ≤ d → (∃ B : ℤ, ∀ δ' ∈ Set.Icc (0 : ℝ) δ₀, ν δ' {k : ℤ | B < |k|} = 0) →
            ENNReal.ofReal (c * Real.log (Real.exp 1 / δ) ^ ((2 : ℝ) / d))
                ≤ Parking.meanuLimit (Parking.law d (ν δ)) ∧
              Parking.meanuLimit (Parking.law d (ν δ))
                ≤ ENNReal.ofReal (C * Real.log (Real.exp 1 / δ) ^ ((2 : ℝ) / d)))
```

Cited `parking.tex` statement:

```latex
\begin{proposition}\label{prop:near-divisible}
	  For all
	sufficiently small $\delta>0$,
	\begin{equation}\label{eq:near-divisible-upper}
		\E u_\infty^\delta(0)\leq C
		\begin{cases}
			\delta^{-3}&d=1\,,\\
			\delta^{-1}&d=2\,,\\
			\delta^{-1/3}&d=3\,,\\
			\log(e/\delta)&d\geq4.
		\end{cases}
	\end{equation}
	The reverse inequality holds when $d\leq4$, and when $d\geq5$ the lower bound
	is $c[\log(e/\delta)]^{2/d}$. If in addition $\eta_\delta(0)$ is bounded
	uniformly in $\delta$, then $\E u_\infty^\delta(0)\asymp[\log(e/\delta)]^{2/d}$
	when $d\geq5$.
\end{proposition}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> two cited inputs as hypotheses (SandpileGrowth, Stopping); UConcentration and GreenNorms are proved internally and are not among the hypotheses; the assumptions of thm:near are `NearFamily delta0 nu theta M K` (mean -delta, nonconstant nu 0, exponential moment <= M, coupling with `E|eta_delta - eta_0| <= K delta`); four assertions as four conjuncts: (a) upper bound C*`nearRate` for all d (delta^-3, delta^-1, delta^-1/3, log(e/delta) for d = 1, 2, 3, >=4); (b) reverse bound c*`nearRate` for d <= 4; (c) for d >= 5 lower bound c [log(e/delta)]^{2/d}; (d) for d >= 5 and support in [-B,B] for every delta' in [0,delta0] two-sided [log(e/delta)]^{2/d}; `exists c C > 0, exists delta1 <= delta0` outside `forall delta in (0, delta1]` ('sufficiently small'), constants may depend on d and the whole family; E u_infty is `meanuLimit` in ENNReal (sup of E u_n) compared through `ENNReal.ofReal`

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
'Parking.Frozen.near_divisible' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.near_divisible` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

`meanuLimit` is in `ℝ≥0∞`; the upper bound `≤ ofReal(C·nearRate)` forces finiteness, so the lower bounds are not vacuous; `nearRate d δ > 0` for `δ>0`.

## 4. Citations

`External` hypotheses carried by the frozen block:

| External | manifest node | paper origin | state |
|---|---|---|---|
| `Parking.External.SandpileGrowth` | `ext-sandpile-growth` | parking.tex:929-943 (thm:BP, Bou-Rabee-Panagiotis) | FROZEN |
| `Parking.External.Stopping` | `ext-stopping` | parking.tex:876-884 (lem:stopping, BPRS Theorem 3.2, proved in the shared library) | SEALED |

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

