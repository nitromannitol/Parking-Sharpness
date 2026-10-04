# Audit — `prop-nearest-two-hole`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `prop-nearest-two-hole` |
| version | 3 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.nearest_two_hole` |
| file | `Parking/Frozen/NearestTwoHole.lean` |
| paper source | parking.tex:2025-2032 (label prop:nearest-two-hole) |
| frozen sha256 | `151a6b9ac7eb06f8a517fd8ea192a9a8180a30e32fde1ac9f58df2a1ddbcda5c` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.nearest_two_hole (hBernstein : Parking.External.Bernstein) (d : ℕ) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 0 < p → p ≤ 1 / 4 →
      ∀ (t : ℕ) (x z : Parking.Site d), x ≠ z →
        ((Parking.law d (Parking.threePointLaw p))
            {ω | Parking.H ω t x = 1 ∧ Parking.H ω t z = 1}).toReal
          ≤ C * Parking.holeProb d (Parking.threePointLaw p) t ^ 2 *
              Real.exp (C * Real.log (1 / Parking.holeProb d (Parking.threePointLaw p) t)
                * (1 + (Parking.graphNorm (x - z) : ℝ)) ^ (4 - (d : ℝ)))
```

Cited `parking.tex` statement:

```latex
\begin{proposition}\label{prop:nearest-two-hole}
	There is $C<\infty$, depending only on $d$, such that, for every $t\geq0$ and
	distinct $x,z\in\Z^d$,
	\begin{equation}\label{eq:nearest-two-hole}
		\P\bigl(H_t(x)=H_t(z)=1\bigr)
		\leq Ch_t^2\exp\bigl\{C\log(1/h_t)(1+|x-z|)^{4-d}\bigr\}\,.
	\end{equation}
\end{proposition}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> one display; Lean asserts it with `exists C > 0` (depends on d only) outside `forall p in (0,1/4]`, `forall t`, `forall x != z`; the setting of Section 9 is built into the statement: d >= 5, three-point law P(+-1) = p, P(0) = 1 - 2p, h_t = holeProb = P(H_t(0) = 1); probability is `.toReal` of a probability measure, exponent (4-d) a real power, |x-z| = graphNorm (x-z); extra hypothesis `hBernstein : External.Bernstein` (the martingale moment inequality of lem:bernstein, a cited input not in the paper's proposition)

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
'Parking.Frozen.nearest_two_hole' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.nearest_two_hole` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

`.toReal` of a probability is in `[0,1]`; the right side is nonnegative; `holeProb` is a genuine probability. Witness law: `threePointLaw p` with any `0<p≤1/4`.

## 4. Citations

`External` hypotheses carried by the frozen block:

| External | manifest node | paper origin | state |
|---|---|---|---|
| `Parking.External.Bernstein` | `ext-bernstein` | parking.tex:1175-1188 (lem:bernstein, Pinelis Theorems 4.1 and 3.3) | FROZEN |

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

