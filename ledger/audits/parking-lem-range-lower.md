# Audit — `lem-range-lower`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `lem-range-lower` |
| version | 3 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.range_lower` |
| file | `Parking/Frozen/RangeLower.lean` |
| paper source | parking.tex:2295-2303 (label lem:range-lower) |
| frozen sha256 | `9cfd7baa9db0461bf36d698689dfa67ac0f9cbe6a1bb11c60571325f6d119983` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `no` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.range_lower (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ)
    (hprob : IsProbabilityMeasure ν) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν < 0) (hpos : 0 < ν (Set.Ioi 0))
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    (∀ t : ℕ, Integrable (fun p => (ν {j : ℤ | 0 ≤ j}).toReal ^
        (Parking.rangeCard (0 : Parking.Site d) p t - 1)) (Parking.walkLaw d)) ∧
    (∀ (k : ℕ), 1 ≤ k → ν {(k : ℤ)} ≠ 0 → ∀ t : ℕ,
        ∫ p, (ν {j : ℤ | 0 ≤ j}).toReal ^ (Parking.rangeCard (0 : Parking.Site d) p t - 1)
            ∂(Parking.walkLaw d)
          ≤ Parking.survivalGiven d ν k t) ∧
      ∀ t : ℕ, (∫ k, max (k : ℝ) 0 ∂ν) *
          ∫ p, (ν {j : ℤ | 0 ≤ j}).toReal ^ (Parking.rangeCard (0 : Parking.Site d) p t - 1)
            ∂(Parking.walkLaw d)
        ≤ Parking.S (Parking.law d ν) t
```

Cited `parking.tex` statement:

```latex
\begin{lemma}\label{lem:range-lower}
	For every $k\geq1$ with
	$\P(\eta(0)=k)>0$ and every $t\geq0$,
	\[
		\P(\tau_1>t\mid\eta(0)=k)\geq\E_0\bigl[\P(\eta(0)\geq0)^{|R_t|-1}\bigr]\,,
	\]
	and consequently
	$S_t\geq\E[\eta(0)^+]\,\E_0[\P(\eta(0)\geq0)^{|R_t|-1}]$.
\end{lemma}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> two displayed relations in the paper (P(tau_1 > t | eta(0) = k) >= E_0[P(eta(0) >= 0)^(|R_t| - 1)], and 'consequently' S_t >= E[eta(0)^+] E_0[...]); Lean has three conjuncts: (1) forall t, Integrable of the range power under `walkLaw d` (junk-value guard, not in the paper); (2) forall k >= 1 with nu{k} != 0, forall t: E_0[...] <= `survivalGiven d nu k t`, which is the joint probability P(eta(0) = k and particle (0,0) active after round t) divided by nu{k} (paper's particle 1 is label (0,0), tau_1 > t is active after round t); (3) forall t: (integral of max k 0 dnu) * E_0[...] <= S_t under `law d nu`; E_0 is an integral over `walkLaw d`, |R_t| is `rangeCard 0 p t` (natural-number `- 1` is harmless since |R_t| >= 1); P(eta(0) >= 0) is `(nu {j | 0 <= j}).toReal`; all the paper's standing hypotheses are present (finite first moment, negative mean, P(eta(0) > 0) > 0, E e^{theta eta(0)} < inf with no absolute value) though the proof does not read the last three; nu is the i.i.d. one-site law, d >= 1

The statement-integrity checks that matter here are: hypotheses, quantifier order,
domains, exponents and units. `tools/check_constants.py` reports `no` for this
node (every existential constant is bound before every paper parameter, so it is a
genuine constant). `tools/check_exponents.py` reports every paper exponent either present
in the Lean statement or explicitly explained. `tools/paper_anchors.py` resolves the
source line range from its LaTeX label.

The paper's lemma states the two inequalities for every `k≥1` with `P(η(0)=k)>0` and every `t≥0`; the frozen statement keeps both inequalities as the second and third conjuncts and adds an `Integrable` guard on the walk average as the first conjunct. The section's standing hypotheses (probability, finite first moment, negative mean, positive mass on `(0,∞)`, exponential moment) are carried as explicit binders in the order the paper's section fixes them. The proof does not read `hpos`, `hθ`, `hexp`; carrying them is conservative. No quantifier-order or exponent discrepancy.

## 2. Proof and axiom closure

The proof compiles (`lake build Parking`, 10371 jobs) and its axiom closure is exactly the
three standard foundational axioms:

```
'Parking.Frozen.range_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.range_lower` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

The right-hand sides are nonnegative (a probability raised to a nonnegative integer power, and `E[η⁺]` times it); `survivalGiven` is a genuine conditional probability. The `Integrable` conjunct excludes a junk integral. The hypotheses (probability, finite first moment, negative mean, positive mass, exponential moment) are satisfiable, e.g. by a two-point law with negative mean.

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

