# Audit — `thm-four-sparse`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `thm-four-sparse` |
| version | 3 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.four_sparse` |
| file | `Parking/Frozen/FourSparse.lean` |
| paper source | parking.tex:1601-1610 (label thm:four-sparse) |
| frozen sha256 | `9a2e26a6ed6aa94be415e6a2f6b8fb52e15e6cf462dfcc8f4cb1c3d6f52e2a48` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.four_sparse (hGrowth : Parking.External.SandpileGrowth)
    (hStopping : Parking.External.Stopping) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∀ᶠ n : ℕ in atTop, c * Real.log (Real.exp 1 / ε) ≤
        Parking.meanU (Parking.law 4 (Parking.threePointLaw (ε / 2))) n /
          Parking.meanu (Parking.law 4 (Parking.threePointLaw (ε / 2))) n
```

Cited `parking.tex` statement:

```latex
\begin{theorem}[Rare nonzero values in dimension four]\label{thm:four-sparse}
	Let $d=4$ and, for $0<\eps\leq1/2$, let $(\eta(x))_{x\in\Z^4}$ be independent
	and identically distributed, with $\eta(0)$ taking the values $1$ and
	$-1$ with probability $\eps/2$ each and $0$ otherwise. There is
	$c>0$, independent of $\eps$, such that
	\begin{equation}\label{eq:four-sparse}
		\liminf_{n\to\infty}\frac{\E U_n(0)}{\E u_n(0)}
		\geq c\log(e/\eps).
	\end{equation}
\end{theorem}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> one display; Lean: `exists c>0` bound before `forall eps in (0,1/2]`, then `eventually n, c * log(e/eps) <= meanU/meanu` on `law 4 (threePointLaw (eps/2))` (mass eps/2 at 1, eps/2 at -1, 1-eps at 0, i.i.d. on Z^4); the paper's `liminf >= c log(e/eps)` is written as an eventual inequality, which implies the paper's liminf with the same c (the paper's implies it with a smaller c), avoiding a junk real liminf; the quotient is real division of E U_n(0) by E u_n(0), and a junk 0 from a zero denominator or non-integrable numerator is excluded because the right side is positive; `hGrowth` (`SandpileGrowth`, BP growth of the mean odometer) and `hStopping` (`Stopping`, optimal-stopping representation) are cited inputs entering as hypotheses, absent from the paper's statement; the threshold in n depends on eps, c does not

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
'Parking.Frozen.four_sparse' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.four_sparse` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

`meanu` is positive in the model (`η` has positive mass), and the inequality is eventually in `n` with a positive right side; `c` is independent of `ε` because it is bound first.

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

