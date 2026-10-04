# Audit — `thm-nearest-counterexample`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `thm-nearest-counterexample` |
| version | 3 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.nearest_counterexample` |
| file | `Parking/Frozen/NearestCounterexample.lean` |
| paper source | parking.tex:289-302 (label thm:nearest-counterexample) |
| frozen sha256 | `4edb5724164ff3f61a2e6f33ddd93e1e1879dd7a37253d163a2e568c74a78987` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.nearest_counterexample (hBernstein : Parking.External.Bernstein) (d : ℕ) (hd : 5 ≤ d) :
    ∃ p : ℝ, 0 < p ∧ p < 1 / 2 ∧ ∃ c : ℝ, 0 < c ∧
      c ≤ liminf (fun t : ℕ =>
        ((Parking.law d (Parking.threePointLaw p)) {ω | Parking.HoleCloser ω t}).toReal) atTop
```

Cited `parking.tex` statement:

```latex
\begin{theorem}\label{thm:nearest-counterexample}
	For every $d\geq5$, there exist $p_d\in(0,1/2)$ and $c>0$ such that, if
	$(\eta(x))_{x\in\Z^d}$ are i.i.d.\ with
	\begin{equation}\label{eq:nearest-counterexample-law}
		\P(\eta(0)=1)=\P(\eta(0)=-1)=p_d,\qquad
		\P(\eta(0)=0)=1-2p_d\,,
	\end{equation}
	then
	     \begin{equation}\label{eq:nearest-counterexample}
		\liminf_{t\to\infty}
		\P(\text{the origin is closer to an unfilled hole than to an active
		particle at time }t)\geq c\,.
	\end{equation}
\end{theorem}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> one display; d>=5 fixed first, then `exists p in (0,1/2)`, then `exists c>0`, then `c <= liminf_{t:N}` of the real probability (values in [0,1], so the liminf is genuine); law is `threePointLaw p` (P(+-1)=p, P(0)=1-2p) i.i.d. under the stack construction `law d`; event `HoleCloser` is holeDistance < activeDistance strictly, graph (l^1) distances in N-infinity with inf over empty = top (immaterial a.s. because holes and active particles both exist a.s.); carries an EXTRA hypothesis `hBernstein : Parking.External.Bernstein` (cited martingale inequality, assumed) that the paper's statement does not have

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
'Parking.Frozen.nearest_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.nearest_counterexample` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

`p ∈ (0,1/2)`, `c>0`, and `c ≤ liminf` of a probability sequence; the liminf is over a bounded sequence and is genuine.

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

