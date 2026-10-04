# Audit — `prop-discrepancy`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `prop-discrepancy` |
| version | 5 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.discrepancy` |
| file | `Parking/Frozen/Discrepancy.lean` |
| paper source | parking.tex:1566-1583 (label prop:discrepancy); the GreenNorms hypothesis is dropped, discharged internally from Parking.External.greenNorms; the UConcentration hypothesis is likewise dropped, discharged internally from Parking.External.uConcentration |
| frozen sha256 | `bf2a8090dcc44e729ebf0ccdff43a6f2676ae0adaad2c023683a5003f8a68f4c` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.discrepancy (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    ∃ C : ℝ, 0 < C ∧
      (∀ n : ℕ, 1 ≤ n →
        Integrable (fun ω => |(Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0|
            ^ Parking.discrepancyExponent n) (Parking.law d ν) ∧
        (∫ ω, |(Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0| ^ Parking.discrepancyExponent n
            ∂(Parking.law d ν)) ^ (1 / Parking.discrepancyExponent n)
          ≤ C * (if d = 1 then (n : ℝ) ^ ((5 : ℝ) / 8) * Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4)
              else if d = 2 then (n : ℝ) ^ ((1 : ℝ) / 4) * Real.log ((n : ℝ) + 1) ^ ((5 : ℝ) / 4)
              else (n : ℝ) ^ ((1 : ℝ) / 8) * Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ((Parking.law d ν) {ω | ε * Parking.meanu (Parking.law d ν) n
            < |(Parking.U ω n 0 : ℝ) - Parking.uOf ω n 0|}).toReal
          ≤ Real.exp (-(c * Real.log n ^ 2))
```

Cited `parking.tex` statement:

```latex
\begin{proposition}\label{prop:discrepancy}
	Under the assumptions of Theorem~\ref{thm:master}, suppose $d\leq3$. For
	$n\geq1$, let $r=2\vee\lceil\log(n+1)\rceil$. Then
	\begin{equation}\label{eq:discrepancy}
		\bigl(\E|U_n(0)-u_n(0)|^r\bigr)^{1/r}\leq C
		\begin{cases}
			n^{5/8}[\log(n+1)]^{3/4}&d=1\,,\\
			n^{1/4}[\log(n+1)]^{5/4}&d=2\,,\\
			n^{1/8}[\log(n+1)]^{3/4}&d=3\,.
		\end{cases}
	\end{equation}
	Consequently, for every $\eps>0$, there is $c>0$ such that, for all
	sufficiently large $n$,
	\begin{equation}\label{eq:discrepancy-tail}
		\P\bigl(|U_n(0)-u_n(0)|>\eps\E u_n(0)\bigr)
		\leq e^{-c(\log n)^2}\,.
	\end{equation}
\end{proposition}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> two assertions (moment bound with three dimension cases, then the tail bound); Lean is `exists C, 0 < C` (after d, nu, so C may depend on d and nu, not n) then two conjuncts: (i) forall n >= 1, Integrable (guard, not in the paper) and (E|U_n(0) - u_n(0)|^r)^(1/r) <= C * (if d = 1 then n^(5/8) log(n+1)^(3/4) else if d = 2 then n^(1/4) log(n+1)^(5/4) else n^(1/8) log(n+1)^(3/4)), with r = `discrepancyExponent n` = max 2 (ceil (log(n+1))) read as a real; (ii) forall eps > 0, exists c > 0, exists N, forall n >= N, P(eps * E u_n(0) < |U_n(0) - u_n(0)|) <= exp(-(c (log n)^2)), 'sufficiently large n' is an explicit N depending on eps; 'assumptions of thm:master' is `CriticalLaw nu` (probability, nonconstant, mean 0, E e^{theta |eta(0)|} < inf), with 1 <= d <= 3 as hypotheses; the two cited inputs SandpileGrowth, Bernstein enter as explicit hypotheses; UConcentration and GreenNorms are proved internally and are not among the hypotheses

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
'Parking.Frozen.discrepancy' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.discrepancy` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

Both `Integrable` conjuncts guard the moment, the `r`-th root is a real power of a nonnegative quantity, and the tail bound is an explicit positive exponential. `liminf`/`Tendsto` are not encoded as junk values.

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

