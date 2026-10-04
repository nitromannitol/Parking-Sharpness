# Audit — `lem-w-martingale`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `lem-w-martingale` |
| version | 3 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.w_martingale` |
| file | `Parking/Frozen/WMartingale.lean` |
| paper source | parking.tex:1135-1148 (label lem:w-martingale) |
| frozen sha256 | `19085718db23e23209170003e6e975ce7af8f9eb04d9057db68fd5d2bc608082` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `no` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.w_martingale (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ)
    (hprob : IsProbabilityMeasure ν) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (F : ℕ → MeasurableSpace (Parking.Data d)) (ξ : ℕ → Parking.Data d → ℝ),
      Monotone F ∧ (∀ i, F i ≤ inferInstanceAs (MeasurableSpace (Parking.Data d))) ∧ (∀ i, Measurable[F (i + 1)] (ξ i)) ∧
      (∀ i, Integrable (ξ i) (Parking.law d ν)) ∧
      (∀ᵐ ω ∂(Parking.law d ν), ∃ N, ∀ i, N ≤ i → ξ i ω = 0) ∧
      (∀ᵐ ω ∂(Parking.law d ν), Parking.wErr ω n 0 = ∑' i, ξ i ω) ∧
      (∀ i, (Parking.law d ν)[ξ i | F i] =ᵐ[Parking.law d ν] 0) ∧
      (∀ i, ∀ ω, |ξ i ω| ≤ Parking.greenIncrement d n) ∧
      (∀ᵐ ω ∂(Parking.law d ν),
        Summable (fun i => ((Parking.law d ν)[fun ω' => ξ i ω' ^ 2 | F i]) ω) ∧
        ∀ s : ℕ, Summable fun y : Parking.Site d =>
          (Parking.A ω (s - 1) y : ℝ) * Parking.gamma d (n - s) y) ∧
      (fun ω => ∑' i, ((Parking.law d ν)[fun ω' => ξ i ω' ^ 2 | F i]) ω)
        =ᵐ[Parking.law d ν] fun ω => ∑ s ∈ Finset.Icc 1 (n - 1), ∑' y : Parking.Site d,
          (Parking.A ω (s - 1) y : ℝ) * Parking.gamma d (n - s) y
```

Cited `parking.tex` statement:

```latex
\begin{lemma}\label{lem:w-martingale}
	Fix $n\geq2$. There are a filtration $(\mathcal F_i)_{i\geq0}$ and random
	variables $(\xi_i)_{i\geq1}$, only finitely many of which are nonzero almost
	surely, such that $w_n(0)=\sum_i\xi_i$ and, for every $i\geq1$,
	\[
		\E[\xi_i\mid\mathcal F_{i-1}]=0\,,\qquad
		|\xi_i|\leq\max_{m<n}\max_y\max_{z\sim y}|g_m(z)-(Pg_m)(y)|\,.
	\]
	Moreover
	\begin{equation}\label{eq:qv}
		\sum_i\E[\xi_i^2\mid\mathcal F_{i-1}]
		=\sum_{s=1}^{n-1}\sum_yA_{s-1}(y)\Gamma_{n-s}(y)\,.
	\end{equation}
\end{lemma}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> paper: one existence claim with five assertions (w_n(0)=sum xi_i; finitely many xi_i nonzero a.s.; E[xi_i|F_{i-1}]=0; the bound |xi_i| <= max_{m<n} max_y max_{z~y}|g_m(z)-(Pg_m)(y)|; the quadratic-variation identity); Lean: `exists F xi` then ten conjuncts: F monotone; F i below the ambient sigma-algebra; xi i is F(i+1)-measurable; xi i integrable; a.e. `exists N, forall i>=N, xi i = 0`; a.e. `wErr omega n 0 = tsum_i xi i omega`; `condExp[xi i | F i] =ae 0`; `forall i omega, |xi i omega| <= greenIncrement d n` (everywhere, not only a.e.); a.e. summability of `i |-> condExp[xi_i^2|F i]` and, for every `s : N`, of `y |-> A omega (s-1) y * gamma d (n-s) y`; the a.e. identity of `tsum_i condExp[xi_i^2|F i]` with `sum_{s in Icc 1 (n-1)} tsum_y A_{s-1}(y) Gamma_{n-s}(y)`; the filtration properties, adaptedness, integrability and summability conjuncts are not in the paper (implicit or junk-value guards); reindexing: xi is indexed from 0, Lean `xi i` is the paper's xi_{i+1} and the filtration is NOT shifted (Lean `F i` is the paper's F_i), so `condExp[xi i|F i]` is E[xi_{i+1}|F_i]; the file header's 'paper's F_{i-1} is F i' is off by one but the statement is as described here; setting: `law d ν` with ν a probability measure on Z (i.i.d. eta, stacks, uniforms), `1 <= d`, `2 <= n`, `wErr omega n 0` is w_n(0), `gamma` is Gamma

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
'Parking.Frozen.w_martingale' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.w_martingale` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

The statement asserts a.s. eventual vanishing of `ξ`, which makes the `tsum` genuinely summable on the full-measure set where it is used; the quadratic-variation identity is asserted as an a.e. equality, not a junk `0 = 0`.

## 4. Citations

No `Parking.External` hypothesis; the only dependencies are the internal support file `Parking.Support.WQuadratic`.

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

