# Audit — `lem-mean-horizon`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `lem-mean-horizon` |
| version | 7 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.mean_horizon` |
| file | `Parking/Frozen/MeanHorizon.lean` |
| paper source | parking.tex:2779-2785 (label lem:mean-horizon); the GreenNorms hypothesis is dropped, discharged internally from Parking.External.greenNorms; the UConcentration hypothesis is likewise dropped, discharged internally from Parking.External.uConcentration |
| frozen sha256 | `6926d5da22d72c7279aabddf848e96799375c655fc22a0e8f519e174cddc9b2c` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.mean_horizon (hGrowth : Parking.External.SandpileGrowth)
    (hStopping : Parking.External.Stopping)
    (d : ℕ) (hd : 1 ≤ d) (δ₀ : ℝ) (ν : ℝ → Measure ℤ)
    (θ M K : ℝ) (hfam : Parking.NearFamily δ₀ ν θ M K) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Icc (0 : ℝ) δ₀, ∀ n : ℕ,
      ∀ σ : (Parking.Site d → ℤ) → (ℕ → Parking.Site d) → ℕ,
        (∀ η, LatticeProb.IsWalkStopping (σ η)) → (∀ η X, σ η X ≤ n) →
        (∀ X, Measurable fun η => σ η X) →
        ∀ Mσ : ℝ, Mσ = ∫ η, ∫ X, (σ η X : ℝ) ∂(LatticeProb.siteWalkLaw d 0)
            ∂(LatticeProb.iidLaw d (ν δ)) →
          Integrable (fun η => ∫ X, ∑ j ∈ Finset.range (σ η X),
              Parking.xi δ η (X j) ∂(LatticeProb.siteWalkLaw d 0))
              (LatticeProb.iidLaw d (ν δ)) ∧
            ∫ η, ∫ X, ∑ j ∈ Finset.range (σ η X),
                Parking.xi δ η (X j) ∂(LatticeProb.siteWalkLaw d 0)
                ∂(LatticeProb.iidLaw d (ν δ))
              ≤ C * Parking.phi d Mσ
```

Cited `parking.tex` statement:

```latex
\begin{lemma}\label{lem:mean-horizon}
	Conditionally on $\xi_\delta$, let $\sigma$ be a bounded stopping time for the
	walk. If $M=\E\sigma$, then
	\[
		\E\sum_{j<\sigma}\xi_\delta(X_j)\leq C\phi_d(M).
	\]
\end{lemma}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> one displayed inequality; Lean: `exists C>0` fixed before `forall delta in [0,delta0], forall n, forall sigma`, then two conjuncts: integrability of `eta |-> E_walk sum_{j<sigma} xi_delta(X_j)` (added, junk guard) and `E_eta E_walk sum_{j<sigma} xi_delta(X_j) <= C * phi d Mσ` (the paper's display); renaming: the paper's `M = E sigma` is `Mσ`, given by hypothesis `Mσ = int_eta int_X sigma eta X` (average over configuration and walk), while Lean's `M` (with theta, K, delta0) belongs to `NearFamily delta0 ν θ M K`, the hypotheses of thm:near (mean -delta, ν 0 nonconstant, uniform exponential moment <= M, coupling with E|.|<=K delta) which the paper leaves to its ambient setting; `xi_delta = eta_delta + delta` is `xi delta eta` with eta ~ `iidLaw d (ν delta)`; 'conditionally on xi_delta' is `sigma : config -> path -> N` with each `sigma eta` a walk stopping time, `sigma eta X <= n` for one n, and measurable in eta for each X; C may depend on d and the family but not on delta, n, sigma, Mσ; the paper's 'sufficiently small delta' is not imposed, Lean covers all delta in [0,delta0] (a stronger range); `phi d` is (s+1)^{(4-d)/4} for d<=3 and log(s+2) otherwise; two cited inputs are hypotheses (`SandpileGrowth`, `Stopping`), absent from the paper's statement; UConcentration and GreenNorms are proved internally and are not among the hypotheses

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
'Parking.Frozen.mean_horizon' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.mean_horizon` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

The integrand is finite by the asserted `Integrable` conjunct; `phi d Mσ` is positive; the bound is non-trivial and holds for every bounded stopping time.

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

