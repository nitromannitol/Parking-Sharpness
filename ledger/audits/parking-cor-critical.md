# Audit — `cor-critical`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `cor-critical` |
| version | 2 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.cor_critical` |
| file | `Parking/Frozen/CorCritical.lean` |
| paper source | parking.tex:1354-1361 (label cor:critical) |
| frozen sha256 | `b6c5c668802bd803f4141f55904e91d8f932d2802fc84be4710e46e88d342fd5` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.cor_critical :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (ν : Measure ℤ), IsProbabilityMeasure ν →
      (∀ k : ℤ, ν {k} ≠ 1) → Integrable (fun k : ℤ => |(k : ℝ)|) ν →
      ∫ k, (k : ℝ) ∂ν = 0 →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        max (Parking.meanu (Parking.law d ν) n) (c * Real.log n - C)
          ≤ Parking.meanU (Parking.law d ν) n
```

Cited `parking.tex` statement:

```latex
\begin{corollary}\label{cor:critical}
	Let $\eta=(\eta(x))_{x\in\Z^d}$ be independent copies of a nonconstant integer-valued
	$\eta(0)$ with mean zero. Then there are $c,C>0$, with $c$ universal, such
	that, for every $n\geq2$,
	\[
		\E U_n(0)\geq\max\bigl\{\E u_n(0),\ c\log n-C\bigr\}\,.
	\]
\end{corollary}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> one display; Lean has `exists c>0` outside `forall d>=1, forall nu` (c universal), then hypotheses nu probability on Z, nonconstant (`nu {k} != 1`), integrable |k| (added so that 'mean zero' is genuine and not a junk integral), mean zero, then `exists C>0` (may depend on d and nu) outside `forall n>=2`, and conclusion `max (meanu) (c log n - C) <= meanU`, i.e. E U_n(0) dominates both terms; meanu = E u_n(0) and meanU = E U_n(0) under `law d nu`

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
'Parking.Frozen.cor_critical' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.cor_critical` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

`c` is universal because it is bound before `d` and `ν`; the lower bound `max(E u_n, c log n − C) ≤ E U_n` cannot be satisfied by a junk value since `c log n − C → ∞`.

## 4. Citations

No `Parking.External` hypothesis; it consumes the frozen node `lem-critical-density` (Batch A), which is itself SEALED and clean.

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

