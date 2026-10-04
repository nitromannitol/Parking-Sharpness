# Audit — `thm-trichotomy`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `thm-trichotomy` |
| version | 6 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.trichotomy` |
| file | `Parking/Frozen/Trichotomy.lean` |
| paper source | parking.tex:207-238 (label thm:trichotomy); the GreenNorms hypothesis is dropped, discharged internally from Parking.External.greenNorms; the UConcentration hypothesis is likewise dropped, discharged internally from Parking.External.uConcentration |
| frozen sha256 | `44d2c93d31c0c17bb2726330f1486138ad80514f9aa1875d0d79da8c5ff36239` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.trichotomy (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hStopping : Parking.External.Stopping) (d : ℕ) (hd : 1 ≤ d) :
    (d ≤ 3 → ∀ (ν : Measure ℤ), Parking.CriticalLaw ν →
      (∀ᵐ ω ∂(Parking.law d ν),
        Tendsto (fun n : ℕ => ((Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0) /
          Parking.meanu (Parking.law d ν) n) atTop (𝓝 0)) ∧
      (∀ r : ℝ, 1 ≤ r →
        (∀ n : ℕ, Integrable (fun ω => |((Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0) /
          Parking.meanu (Parking.law d ν) n| ^ r) (Parking.law d ν)) ∧
        Tendsto (fun n : ℕ => ∫ ω, |((Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0) /
          Parking.meanu (Parking.law d ν) n| ^ r ∂(Parking.law d ν)) atTop (𝓝 0)) ∧
      Tendsto (fun n : ℕ => Parking.meanU (Parking.law d ν) n /
        Parking.meanu (Parking.law d ν) n) atTop (𝓝 1) ∧
      ∃ L : ℝ, 0 < L ∧ Tendsto (fun n : ℕ =>
        (n : ℝ) ^ (-((4 - (d : ℝ)) / 4)) * Parking.meanU (Parking.law d ν) n) atTop (𝓝 L)) ∧
    (d = 4 → (∀ (ν : Measure ℤ), Parking.CriticalLaw ν →
      (∀ n : ℕ, 1 ≤ n → 1 ≤ Parking.meanU (Parking.law d ν) n / Parking.meanu (Parking.law d ν) n) ∧
      ∃ B : ℝ, ∀ n : ℕ, 1 ≤ n →
        Parking.meanU (Parking.law d ν) n / Parking.meanu (Parking.law d ν) n ≤ B) ∧
      ∀ B : ℝ, 0 < B → ∃ ν : Measure ℤ, Parking.CriticalLaw ν ∧
        B ≤ liminf (fun n : ℕ => Parking.meanU (Parking.law d ν) n /
          Parking.meanu (Parking.law d ν) n) atTop) ∧
    (5 ≤ d → ∀ (ν : Measure ℤ), Parking.CriticalLaw ν → (∃ b : ℤ, ν (Set.Iio b) = 0) →
      (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
        c * Real.log n ≤ Parking.meanU (Parking.law d ν) n ∧
          Parking.meanU (Parking.law d ν) n ≤ C * Real.log n ∧
        c * Real.log n ≤ ∫ ω, |(Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0| ∂(Parking.law d ν) ∧
          ∫ ω, |(Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0| ∂(Parking.law d ν) ≤ C * Real.log n) ∧
      Tendsto (fun n : ℕ => Parking.meanU (Parking.law d ν) n /
        Parking.meanu (Parking.law d ν) n) atTop atTop)
```

Cited `parking.tex` statement:

```latex
\begin{theorem}[Quenched odometer comparison]\label{thm:trichotomy}
	Let $\eta=(\eta(x))_{x\in\Z^d}$ have i.i.d.\ integer-valued coordinates.
	Suppose that $\eta(0)$ is nonconstant, $\E\eta(0)=0$, and
	$\E e^{\theta|\eta(0)|}<\infty$ for some $\theta>0$.
	All limits below are as $n\to\infty$.
	\begin{enumerate}[label=\textup{(\roman*)}]
		\item \underline{\textup{Dimensions one, two, and three.}}  The two
		odometers agree to leading order: almost surely and in $L^r$ for every
		$r\geq1$,
		\[
			\frac{U_n(0)-u_n(0)}{\E u_n(0)}\longrightarrow0\,.
		\]
		Consequently $\E U_n(0)/\E u_n(0)\to1$, and $n^{-(4-d)/4}\E U_n(0)$
		converges to a limit in $(0,\infty)$.

		\item \underline{\textup{Dimension four.}}  For every $n\geq1$, the
		ratio $\E U_n(0)/\E u_n(0)$ is at least one. For each fixed law this
		ratio is bounded above uniformly in $n$, but no such upper bound is
		uniform over the laws in this theorem: for every $B>0$ there is a law
		satisfying its hypotheses with
		\begin{equation}\label{eq:four-ratio}
			\liminf_{n\to\infty}\frac{\E U_n(0)}{\E u_n(0)}\geq B\,.
		\end{equation}

		\item \underline{\textup{Dimensions five and higher.}}  If in addition
		$\eta(0)$ is bounded below, then $\E U_n(0)\asymp\log n$ and
		$\E|U_n(0)-u_n(0)|\asymp\log n$, while
		\[
			\frac{\E U_n(0)}{\E u_n(0)}\longrightarrow\infty\,.
		\]
	\end{enumerate}
\end{theorem}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> three cited inputs as explicit hypotheses (SandpileGrowth, Bernstein, Stopping); UConcentration and GreenNorms are proved internally and are not among the hypotheses; `1 <= d` and three conjuncts by d (`d <= 3`, `d = 4`, `5 <= d`); the theorem's hypotheses are `CriticalLaw nu` (probability, non-Dirac, mean zero, exponential moment for some theta) quantified inside each part; (i) four assertions: a.s. convergence of (U_n(0)-u_n(0))/E u_n(0) to 0; L^r convergence for every r >= 1 written as integrability for every n plus E|.|^r -> 0; E U_n/E u_n -> 1; n^{-(4-d)/4} E U_n -> L with 0 < L real; (ii) three assertions: ratio >= 1 for n >= 1 and `exists B` bounding it for n >= 1 (both under forall nu, B depends on nu), then forall B > 0 exists a critical nu with `B <= liminf` (real liminf, not a junk escape since the ratio is >= 1 and bounded for each nu); the paper's 'no uniform bound' sentence is that last clause; (iii) for nu bounded below (`exists b, nu (Iio b) = 0`): one shared `exists c C`, `0 < c <= C`, for n >= 2 giving c log n <= E U_n <= C log n and c log n <= E|U_n-u_n| <= C log n (positive lower bounds rule out the junk zero of a Bochner integral), plus ratio -> infinity; U is `U omega n 0`, u_n is `uOf omega n 0`, expectations are `meanU`, `meanu`

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
'Parking.Frozen.trichotomy' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.trichotomy` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

Every part has either an explicit positive lower bound, a `liminf`/`Tendsto` to a genuine limit, or `atTop`; none is a junk value. The `d=4` `liminf` is over a ratio shown to be `≥1` and bounded.

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

