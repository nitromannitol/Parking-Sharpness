# Audit — `thm-comparison`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `thm-comparison` |
| version | 2 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.comparison` |
| file | `Parking/Frozen/Comparison.lean` |
| paper source | parking.tex:889-895 (label thm:comparison) |
| frozen sha256 | `cba4b60e269bfc28ea466b7f369ce531a36d99ea5e3a103a6e41f11c86db499d` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `no` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.comparison (d : ℕ) (hd : 1 ≤ d) (η : Parking.Site d → ℤ)
    (n : ℕ) (x : Parking.Site d) :
    Parking.u (fun y => ((η y : ℤ) : ℝ)) n x ≤ Parking.meanUgiven d η n x
```

Cited `parking.tex` statement:

```latex
\begin{theorem}[Conditional domination]\label{thm:comparison}
	Fix an integer-valued initial configuration $\eta$. For every $n\geq0$ and
	$x\in\Z^d$,
	\begin{equation}\label{eq:comparison}
		u_n(x)\leq\E[U_n(x)\mid\eta]\,.
	\end{equation}
\end{theorem}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> one display u_n(x) <= E[U_n(x)|eta]; Lean asserts it as one inequality, for every d >= 1, every deterministic eta : Site d -> Z, every n and x (order forall eta, n, x, so it holds for each fixed eta and is not an almost-sure statement); left side is `Parking.u` of the real cast of eta (u_0 = 0, u_{n+1} = max 0 (eta + P u_n), P = walkOp); right side E[U_n(x)|eta] is realised as `meanUgiven`, the integral of U_n(x) over the stack-and-uniform law with eta held fixed (U_n(x) is bounded by an eta-dependent constant, so it is not a junk value)

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
'Parking.Frozen.comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.comparison` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

The conclusion `u_n(x) ≤ E[U_n(x)|η]` is a two-sided meaningful inequality; `meanUgiven` is a genuine integral against the stack/rank law, not `0` or `sInf ∅`. Witness: `η ≡ 0`.

## 4. Citations

No `Parking.External` hypothesis; depends on `Parking.Support.Comparison`.

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

