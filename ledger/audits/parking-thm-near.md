# Audit — `thm-near`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `thm-near` |
| version | 5 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.near` |
| file | `Parking/Frozen/Near.lean` |
| paper source | parking.tex:314-335 (label thm:near); the GreenNorms hypothesis is dropped, discharged internally from Parking.External.greenNorms; the UConcentration hypothesis is likewise dropped, discharged internally from Parking.External.uConcentration |
| frozen sha256 | `3cfbdef34edf26b68b42fd592f3c539666231efe0e541460abca96e34bf350c3` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.near (hGrowth : Parking.External.SandpileGrowth)
    (hStopping : Parking.External.Stopping)
    (hBernstein : Parking.External.Bernstein)
    (d : ℕ) (hd : 1 ≤ d) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (ν : ℝ → Measure ℤ)
    (hprob : ∀ δ ∈ Set.Icc 0 δ₀, IsProbabilityMeasure (ν δ))
    (hmean : ∀ δ ∈ Set.Icc 0 δ₀, ∫ k, (k : ℝ) ∂(ν δ) = -δ)
    (hnonconst : ∀ k : ℤ, ν 0 {k} ≠ 1)
    (θ M : ℝ) (hθ : 0 < θ)
    (hexp : ∀ δ ∈ Set.Icc 0 δ₀, Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) (ν δ) ∧
      ∫ k, Real.exp (θ * |(k : ℝ)|) ∂(ν δ) ≤ M)
    (K : ℝ) (hcouple : ∀ δ ∈ Set.Ioc 0 δ₀, ∃ π : Measure (ℤ × ℤ), IsProbabilityMeasure π ∧
      π.map Prod.fst = ν δ ∧ π.map Prod.snd = ν 0 ∧
      ∫ p, |((p.1 : ℝ) - p.2)| ∂π ≤ K * δ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ ∈ Set.Ioc 0 δ₁,
      ENNReal.ofReal (c * Parking.nearRate d δ) ≤ Parking.meanUlimit (Parking.law d (ν δ)) ∧
        Parking.meanUlimit (Parking.law d (ν δ)) ≤ ENNReal.ofReal (C * Parking.nearRate d δ)
```

Cited `parking.tex` statement:

```latex
\begin{theorem}[Near criticality]\label{thm:near}
	Let $\delta_0>0$. For each $0\leq\delta\leq\delta_0$, let
	$\eta_\delta=(\eta_\delta(x))_{x\in\Z^d}$ have independent and identically
	distributed integer-valued coordinates of mean $-\delta$. Suppose that
	$\eta_0(0)$ is nonconstant. Let $U^\delta$ be the particle odometer started
	from $\eta_\delta$.
	Suppose that, for some $\theta>0$, the expectations
	$\E e^{\theta|\eta_\delta(0)|}$ are bounded uniformly over
	$0\leq\delta\leq\delta_0$. Suppose also that, for a constant $K<\infty$ and every
	$0<\delta\leq\delta_0$, the variables $\eta_\delta(0)$ and $\eta_0(0)$ admit a coupling
	with $\E|\eta_\delta(0)-\eta_0(0)|\leq K\delta$. Then, as
	$\delta\downarrow0$,
	\begin{equation}\label{eq:near}
		\E U_\infty^\delta(0)\asymp
		\begin{cases}
			\delta^{-3}&d=1\,,\\
			\delta^{-1}&d=2\,,\\
			\delta^{-1/3}&d=3\,,\\
			\log(e/\delta)&d\geq4\,.
		\end{cases}
	\end{equation}
\end{theorem}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> one asymptotic-equivalence display (four dimension cases), formalised as `exists c C, 0 < c <= C, exists delta1 > 0, forall delta in (0, delta1]`: ofReal(c * rate) <= E U_inf^delta(0) <= ofReal(C * rate) in ENNReal, so the upper bound also asserts finiteness; rate = delta^(-3), delta^(-1), delta^(-1/3), log(e/delta) for d = 1, 2, 3, >= 4 (`nearRate`); c, C, delta1 are chosen after d, delta0, nu, theta, M, K, so they may depend on the whole family and its parameters, not on delta; the family is `nu : R -> Measure Z`: for delta in [0, delta0] probability with mean -delta, nu 0 nonconstant, Integrable e^{theta|k|} with integral <= M (explicit uniform bound M, integrability added as a junk-value guard), and for delta in (0, delta0] a coupling pi on Z x Z with marginals nu delta, nu 0 and integral of |p.1 - p.2| <= K delta; E U_inf^delta(0) is `meanUlimit (law d (nu delta))`, a lintegral of the supremum in N-infinity; the three cited inputs SandpileGrowth, Stopping, Bernstein enter as explicit hypotheses; UConcentration and GreenNorms are proved internally and are not among the hypotheses

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
'Parking.Frozen.near' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.near` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

`ENNReal.ofReal(c·nearRate) ≤ meanUlimit ≤ ENNReal.ofReal(C·nearRate)` with `0<c≤C`: the upper bound forces finiteness and the lower bound forces positivity, so `≍` is genuine.

## 4. Citations

`External` hypotheses carried by the frozen block:

| External | manifest node | paper origin | state |
|---|---|---|---|
| `Parking.External.Bernstein` | `ext-bernstein` | parking.tex:1175-1188 (lem:bernstein, Pinelis Theorems 4.1 and 3.3) | FROZEN |
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

