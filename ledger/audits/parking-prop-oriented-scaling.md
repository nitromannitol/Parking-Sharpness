# Audit — `prop-oriented-scaling`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `prop-oriented-scaling` |
| version | 6 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.oriented_scaling` |
| file | `Parking/Frozen/OrientedScaling.lean` |
| paper source | parking.tex:3166-3174 (label prop:oriented-scaling; binomial LCLT hypothesis discharged) |
| frozen sha256 | `d90fd89c7cbb286fac1ed47a97b7cbcc2bcb9b5e2f4723063e5957f49b6d640d` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `no` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.oriented_scaling
    (hStability : Parking.External.OrientedStoppingStability)
    (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
      (Uc : ℝ → Ω → ℝ) (μ : ℝ),
      (∀ T : ℝ, 0 < T → Measurable (Uc T)) ∧
      (∀ T : ℝ, 0 < T → ∀ F : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n : ℕ => ∫ w, F ((n : ℝ) ^ (-(1 : ℝ) / 4) *
              Parking.uOriented (fun y => (w.1 y : ℝ)) ⌊(n : ℝ) * T⌋₊ 0)
            ∂(Parking.orientedLaw 2 ν)) atTop (𝓝 (∫ ω, F (Uc T ω) ∂Q))) ∧
      (∀ T : ℝ, 0 < T → Q.map (Uc T) = Q.map fun ω => T ^ ((1 : ℝ) / 4) * Uc 1 ω) ∧
      Integrable (Uc 1) Q ∧ μ = ∫ ω, Uc 1 ω ∂Q ∧ 0 < μ ∧
      Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 4) *
        Parking.meanuOriented (Parking.orientedLaw 2 ν) n) atTop (𝓝 μ)
```

Cited `parking.tex` statement:

```latex
\begin{proposition}\label{prop:oriented-scaling}
	Let $d=2$, and let $\eta=(\eta(x))_{x\in\Z^2}$ have i.i.d.\ coordinates.
	Suppose that $\eta(0)$ is nonconstant, $\E\eta(0)=0$, and
	$\E e^{\theta|\eta(0)|}<\infty$ for some $\theta>0$. Let $\vec P(x,x-e_i)=1/2$ for $i=1,2$, and let $\vec u_0=0$ and $\vec u_{n+1}=(\eta+\vec P\vec u_n)^+$. Then, for every
	$T>0$, $n^{-1/4}\vec u_{\lfloor nT\rfloor}(0)$ converges in distribution to a random variable $\mathcal U(T)$ defined in the proof. Moreover, $\mathcal U(T)\stackrel d=T^{1/4}\mathcal U(1)$, $\mu\coloneqq\E\mathcal U(1)\in(0,\infty)$, and
	\[
		\lim_{n\to\infty}n^{-1/4}\E \vec u_n(0)=\mu\,.
	\]
\end{proposition}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> four assertions (convergence in distribution for every T>0; U(T) =d T^{1/4} U(1); mu = E U(1) in (0,inf); n^{-1/4} E u_n(0) -> mu) mapped onto Lean conjuncts under `exists (Omega, Q probability, Uc : R -> Omega -> R, mu)`: measurability of `Uc T` for T>0 (added, so the law is genuine); convergence via bounded continuous F, `int F(n^{-1/4} uOriented eta (floor(nT)) 0) d orientedLaw 2 nu -> int F(Uc T) dQ`; `Q.map (Uc T) = Q.map (T^{1/4} * Uc 1)`; `Integrable (Uc 1)`, `mu = int Uc 1 dQ`, `0 < mu` (this is mu in (0,inf)); `n^{-1/4} meanuOriented (orientedLaw 2 nu) n -> mu`; the limit is asserted to exist and is not identified with the proof's construction; d=2 is fixed by `orientedLaw 2`, with orientedOp f x = (1/d) sum_i f(x-e_i), i.e. 1/2 each; hypothesis `CriticalLaw nu` = probability on Z (integer-valued, not in the proposition's own text), nonconstant, mean 0, exp(theta|k|) integrable; carries an EXTRA hypothesis `hStability` (a cited input from Step 1) not in the paper's statement; the binomial local CLT Step 1 also cites is no longer carried as a hypothesis, discharged internally from `Parking.External.binomialLocalCLT`

The statement-integrity checks that matter here are: hypotheses, quantifier order,
domains, exponents and units. `tools/check_constants.py` reports `no` for this
node (every existential constant is bound before every paper parameter, so it is a
genuine constant). `tools/check_exponents.py` reports every paper exponent either present
in the Lean statement or explicitly explained. `tools/paper_anchors.py` resolves the
source line range from its LaTeX label.

No discrepancy with the paper statement was found in hypotheses, quantifier order, domains, exponents or units.

## 2. Proof and axiom closure

The proof compiles (`lake build Parking`, 10371 jobs) and its axiom closure is exactly the
three standard foundational axioms:

```
'Parking.Frozen.oriented_scaling' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.oriented_scaling` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

`μ = ∫ Uc 1 ∂Q` with `0 < μ` and `Integrable (Uc 1)`; convergence is through all bounded continuous test functions, and `n^{-1/4} meanuOriented → μ` is a genuine limit.

## 4. Citations

`External` hypotheses carried by the frozen block:

| External | manifest node | paper origin | state |
|---|---|---|---|
| `Parking.External.OrientedStoppingStability` | `ext-oriented-stopping-stability` | parking.tex:3214-3218 (cutoff and stability of the parabolic scaling limit) | FROZEN |

Each is a genuine cited input (a result the paper cites or quotes, not a step the paper
itself proves in the cited range). Carries `OrientedStoppingStability`, a genuine cited Step-1 input (parking.tex:3214-3218). The binomial LCLT is discharged internally and is correctly absent.

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

