# Audit — `lem-transport`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `lem-transport` |
| version | 3 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.transport` |
| file | `Parking/Frozen/Transport.lean` |
| paper source | parking.tex:741-753 (label lem:transport) |
| frozen sha256 | `d87638fae420f9e5fc99c76f576675788433806d8409d291fafc0bbfe023c10a` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `no` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.transport (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ)
    (hprob : IsProbabilityMeasure ν) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) :
    (∀ t : ℕ, Integrable (fun ω => (Parking.A ω t 0 : ℝ)) (Parking.law d ν) ∧
        Integrable (fun ω => (LatticeProb.survivorsFrom (Parking.toDriver ω) t 0 : ℝ))
          (Parking.law d ν) ∧
        ∫ ω, (Parking.A ω t 0 : ℝ) ∂(Parking.law d ν) = Parking.S (Parking.law d ν) t) ∧
    (∀ n : ℕ, Parking.meanU (Parking.law d ν) n
        = ∑ s ∈ Finset.range n, Parking.S (Parking.law d ν) s) ∧
    (∀ k : ℕ, 1 ≤ k → ν {(k : ℤ)} ≠ 0 → ∀ σ : Equiv.Perm ℕ, (∀ i, k ≤ i → σ i = i) →
        ((Parking.law d ν).restrict {ω : Parking.Data d | ω.1 0 = (k : ℤ)}).map
            (fun ω : Parking.Data d => fun q : ℕ × ℕ =>
              (LatticeProb.state (Parking.toDriver ω) q.1).active (0, σ q.2))
          = ((Parking.law d ν).restrict {ω : Parking.Data d | ω.1 0 = (k : ℤ)}).map
            (fun ω : Parking.Data d => fun q : ℕ × ℕ =>
              (LatticeProb.state (Parking.toDriver ω) q.1).active (0, q.2))) ∧
    (∀ t : ℕ, Summable (fun k : ℕ => ((k : ℝ) + 1) *
          ((Parking.law d ν) {ω | ω.1 0 = (k : ℤ) + 1 ∧
            (LatticeProb.state (Parking.toDriver ω) t).active (0, 0) = true}).toReal) ∧
        Parking.S (Parking.law d ν) t = ∑' k : ℕ, ((k : ℝ) + 1) *
          ((Parking.law d ν) {ω | ω.1 0 = (k : ℤ) + 1 ∧
            (LatticeProb.state (Parking.toDriver ω) t).active (0, 0) = true}).toReal)
```

Cited `parking.tex` statement:

```latex
\begin{lemma}\label{lem:transport}
	For every $t\geq0$ and every $n\geq0$,
	\begin{equation}\label{eq:transport}
		\E A_t(0)=S_t\,,
		\qquad
		\E U_n(0)=\sum_{s<n}S_s\,,
	\end{equation}
	and, for every $k\geq1$ with $\P(\eta(0)=k)>0$, the $k$ particles at the
	origin are exchangeable conditionally on $\eta(0)=k$, so that
	\begin{equation}\label{eq:S-expand}
		S_t=\sum_{k\geq1}k\,\P(\eta(0)=k)\,\P(\tau_1>t\mid\eta(0)=k)\,.
	\end{equation}
\end{lemma}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> paper makes four assertions (E A_t(0)=S_t; E U_n(0)=sum_{s<n} S_s; exchangeability of the k origin particles given eta(0)=k; the expansion S_t = sum_{k>=1} k P(eta(0)=k) P(tau_1>t|eta(0)=k)), mapped in that order to the four top-level Lean conjuncts; conjunct 1 also asserts integrability of A_t(0) and of the survivor count, and conjunct 4 also asserts summability (strengthenings that exclude junk integral/tsum values); MISMATCH: Lean adds the hypothesis E|eta(0)| < inf (`hint`), which the paper does not state; law is `Parking.law d nu` (i.i.d. integer eta, stacks, uniforms); A_t(0) = `activeCount`, which equals U_{t+1}-U_t by the definition of a round; S_t = E of the number of labels (0,i), i < eta(0)^+, active after round t, so paper particle i is Lean label (0,i-1) and 'tau_i > t' is 'active after round t'; exchangeability is read as invariance of the joint law of the activity histories (t,i) |-> active_t(0,i) under every permutation of N fixing all i >= k, for the law restricted to {eta(0)=k}, for k >= 1 with nu{k} != 0 (activity histories only, not positions); the expansion is written with joint probabilities and reindexed, as sum'_{k>=0} (k+1) P(eta(0)=k+1, active_t(0,0)), the same identity without conditioning on null events

The statement-integrity checks that matter here are: hypotheses, quantifier order,
domains, exponents and units. `tools/check_constants.py` reports `no` for this
node (every existential constant is bound before every paper parameter, so it is a
genuine constant). `tools/check_exponents.py` reports every paper exponent either present
in the Lean statement or explicitly explained. `tools/paper_anchors.py` resolves the
source line range from its LaTeX label.

**Documented discrepancy (conservative).** The paper's `lem:transport` is stated for an i.i.d. integer-valued configuration with no finite-mean hypothesis; the frozen statement adds `hint : Integrable (fun k => |k|) ν`. This is an extra hypothesis, so the frozen statement is weaker than the paper's, not stronger; it is exactly the condition under which the real-valued identities and the `tsum` expansion are meaningful. All four paper assertions are otherwise present, in order, with the same quantifiers and with integrability/summability guards. `tools/check_clauses.py` records the same MISMATCH. No false strengthening.

## 2. Proof and axiom closure

The proof compiles (`lake build Parking`, 10371 jobs) and its axiom closure is exactly the
three standard foundational axioms:

```
'Parking.Frozen.transport' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.transport` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

The four conjuncts are genuine equalities of real expectations and of push-forward laws, guarded by `Integrable`/`Summable` conjuncts that exclude junk integrals and `tsum`s. The added hypothesis `hint` (finite first moment) is satisfiable and is the standing assumption under which the paper's real-valued identities are stated.

## 4. Citations

The frozen block carries no `External` hypothesis.

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

