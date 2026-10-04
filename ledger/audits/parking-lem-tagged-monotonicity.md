# Audit — `lem-tagged-monotonicity`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `lem-tagged-monotonicity` |
| version | 2 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.tagged_monotonicity` |
| file | `Parking/Frozen/TaggedMonotonicity.lean` |
| paper source | parking.tex:714-719 (label lem:tagged-monotonicity) |
| frozen sha256 | `839cf2a4b0fc1915fc56d25140603a39b1d22678e474c7fad4fe7ebbb7813fb3` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `no` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.tagged_monotonicity (d : ℕ) (hd : 1 ≤ d) (D : Parking.PDriver d)
    (x₀ : Parking.Site d) (t : ℕ) (p : Parking.Label d) :
    (Parking.pState D t).active p = true →
      (Parking.pState (Parking.addParticleDriver x₀ D) t).active p = true
```

Cited `parking.tex` statement:

```latex
\begin{lemma}[Tagged-particle monotonicity]\label{lem:tagged-monotonicity}
	In the coupling of Lemma~\ref{lem:one-particle}, every particle present in
	both processes
	stays active in the process started from $\widetilde\eta$ at least as long as
	in the process started from $\eta$.
\end{lemma}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> one assertion (an implication at every round: 'stays active at least as long' is read as active at round t in the first process implies active at round t in the second); Lean is a single implication, no conjunction, `forall p, forall t`; reformulation: the coupling is the particle-driven one (`PDriver` with eta, per-particle moves, per-particle ranks), the second process is `addParticleDriver x0 D` (eta raised by one at x0, everything else shared), and the statement is pathwise for every driver D and every x0, not almost sure; 'every particle present in both' is `forall p : Label d` (a label active in the first process is present in both, so quantifying over all labels is no stronger); `1 <= d` is unused

The statement-integrity checks that matter here are: hypotheses, quantifier order,
domains, exponents and units. `tools/check_constants.py` reports `no` for this
node (every existential constant is bound before every paper parameter, so it is a
genuine constant). `tools/check_exponents.py` reports every paper exponent either present
in the Lean statement or explicitly explained. `tools/paper_anchors.py` resolves the
source line range from its LaTeX label.

The paper's `lem:tagged-monotonicity` is an implication at every round in the one-particle coupling. The frozen statement is exactly that implication, pathwise for every particle-driven driver and every label; `1≤d` is a standing dimension bound. No discrepancy.

## 2. Proof and axiom closure

The proof compiles (`lake build Parking`, 10371 jobs) and its axiom closure is exactly the
three standard foundational axioms:

```
'Parking.Frozen.tagged_monotonicity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.tagged_monotonicity` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

The conclusion is a genuine implication about activity in the coupled processes, for every driver, site and label; the antecedent is satisfiable (e.g. any active label), so the statement is not vacuous. No junk value occurs.

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

