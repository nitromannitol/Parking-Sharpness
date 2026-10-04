# Audit — `thm-subcritical`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `thm-subcritical` |
| version | 3 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.subcritical` |
| file | `Parking/Frozen/Subcritical.lean` |
| paper source | parking.tex:2434-2447 (label thm:subcritical) |
| frozen sha256 | `4c7507c1091e653f1b747a06d1904f33f5e82f4c7365bcec0c8931fc390be950` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.subcritical (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ)
    (hprob : IsProbabilityMeasure ν) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν < 0) (hpos : 0 < ν (Set.Ioi 0))
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    (lam₁ : ℝ) (hlam₁ : 0 < lam₁) (hlam₁θ : lam₁ < θ)
    (hnonpos : ∀ s ∈ Set.Icc 0 lam₁,
      Integrable (fun k : ℤ => (k : ℝ)) (Parking.tiltLaw ν s) ∧
      ∫ k, (k : ℝ) ∂(Parking.tiltLaw ν s) ≤ 0)
    (a : ℝ) (ha : a = (1 / 3) * ∫ s in (0 : ℝ)..lam₁, Parking.drift ν s) :
    0 < a ∧
    (∀ (k : ℕ), 1 ≤ k → ν {(k : ℤ)} ≠ 0 → ∀ (t : ℕ) (w : ℕ → Fin d × Bool),
        Parking.survivalGivenWalk d ν k t w
          ≤ Real.exp ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, ∫ j, |(j : ℝ)| ∂(Parking.tiltLaw ν s))
            * Real.exp (lam₁ * ((k : ℝ) - 1) / 3
              - a * (Parking.rangeCard (0 : Parking.Site d) w t : ℝ))) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ,
      Integrable (fun ω => (LatticeProb.survivorsFrom (Parking.toDriver ω) t 0 : ℝ))
        (Parking.law d ν) ∧
      Parking.S (Parking.law d ν) t
      ≤ C * ∫ p, Real.exp (-(a * (Parking.rangeCard (0 : Parking.Site d) p t : ℝ)))
          ∂(Parking.walkLaw d)
```

Cited `parking.tex` statement:

```latex
\begin{theorem}[Subcritical settling time]\label{thm:subcritical}
	Under the assumptions and notation above, let
	\[
		a\coloneqq\frac13\int_0^{\lambda_1}\delta(\lambda)\,d\lambda\,.
	\]
	Then $a>0$ and, for every $t\geq0$ and every $k\geq1$ in the support of
	$\eta(0)$,
	\begin{equation}\label{eq:range-upper}
		\P\bigl(\tau_1>t\mid\eta(0)=k,\ X_0,\ldots,X_t\bigr)
		\leq\exp\Bigl\{\tfrac13\int_0^{\lambda_1}\E_\lambda|\eta(0)|
		\,d\lambda\Bigr\}\,e^{\lambda_1(k-1)/3-a|R_t|}\,.
	\end{equation}
	Consequently $S_t\leq C\E_0e^{-a|R_t|}$.
\end{theorem}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> three assertions, three top-level conjuncts: (i) `0 < a`; (ii) the displayed bound, for all k>=1 with `nu {k} != 0` (k in the support), all t:N and every prescribed walk w (pointwise in w, stronger than the paper's a.s. conditioning): `survivalGivenWalk d nu k t w <= exp((1/3) int_0^lam1 int |j| d tilt_s) * exp(lam1 (k-1)/3 - a * rangeCard 0 w t)`, where |R_t| = `rangeCard` counts X_0..X_t and survival is label (0,0) active after round t with its moves set to w, divided by nu{k}, in the particle-driven construction; (iii) `exists C>0` (may depend on d, nu, theta, lam1; not t) `forall t`, `S_t <= C * int exp(-a |R_t|) d walkLaw d` (S in the stack construction, E_0 the walk average), with added integrability of the survivor count; the standing setting becomes hypotheses: integer-valued nu, integrable |k|, negative mean, `0 < nu (Ioi 0)`, theta>0 with exp(theta k) integrable, lam1 in (0,theta) with tilt_s of integrable nonpositive mean for every s in [0,lam1] (lam1 universally quantified, matching 'choose lam1'), and `a = (1/3) int_0^lam1 drift s` given as a hypothesis, with `drift s = -E_s eta(0)`

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
'Parking.Frozen.subcritical' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.subcritical` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

`0 < a` is asserted as a conjunct; `survivalGivenWalk` is a genuine conditional probability (divided by `ν {k}` with `ν {k} ≠ 0`), and the bound is two exponential factors with a negative `−a |R_t|`.

## 4. Citations

No `Parking.External` hypothesis; depends on `Parking.Support.SubcriticalJointBound`.

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

