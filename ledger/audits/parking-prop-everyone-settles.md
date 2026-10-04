# Audit — `prop-everyone-settles`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `prop-everyone-settles` |
| version | 5 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.everyone_settles` |
| file | `Parking/Frozen/EveryoneSettles.lean` |
| paper source | parking.tex:1501-1509 (label prop:everyone-settles); the GreenNorms hypothesis is dropped, discharged internally from Parking.External.greenNorms; the UConcentration hypothesis is likewise dropped, discharged internally from Parking.External.uConcentration |
| frozen sha256 | `830a4c0ff559f5447716ac9da3b43e0b8dc13b6e2106c44e1ce217f73c75c6b0` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `no` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.everyone_settles (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    ∀ᵐ ω ∂(Parking.law d ν),
      (∀ p : Parking.Label d, ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
          (LatticeProb.state (Parking.toDriver ω) t).active p = false) ∧
      (∀ x : Parking.Site d, ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → Parking.H ω t x = 0) ∧
      (∀ x : Parking.Site d, {p : Parking.Label d | ∃ t : ℕ,
          (LatticeProb.state (Parking.toDriver ω) t).active p = true ∧
            (LatticeProb.state (Parking.toDriver ω) t).pos p = x ∧
            (LatticeProb.state (Parking.toDriver ω) (t + 1)).pos p ≠ x}.Infinite) ∧
      (∀ x : Parking.Site d, Parking.Ulimit ω x = ⊤)
```

Cited `parking.tex` statement:

```latex
\begin{proposition}\label{prop:everyone-settles}
	Let $\eta=(\eta(x))_{x\in\Z^d}$ have i.i.d.\ integer-valued coordinates.
	Suppose that $\eta(0)$ is nonconstant, $\E\eta(0)=0$, and
	$\E e^{\theta|\eta(0)|}<\infty$ for some $\theta>0$. Then the following hold
	together on one event of probability one: every particle settles after
	finitely many rounds; every hole is filled after finitely many rounds; and
	infinitely many distinct particles leave every site, so that
	$U_\infty(x)=\infty$ for every $x\in\Z^d$.
\end{proposition}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> paper makes four assertions on one probability-one event (every particle settles in finite time; every hole is filled in finite time; infinitely many distinct particles leave every site; U_infinity(x)=infinity for all x); Lean is one `forall^m omega` of four conjuncts in that order; particle settles = `active p = false` for all t >= some t0, and the quantifier ranges over all labels, the phantom labels with index >= eta(x)^+ being trivially inactive; hole filled = for each site x, `H omega t x = 0` for all t >= some t0 (equivalent, since each site has finitely many holes); 'leave x' = label p with some t such that p is active at x after round t and stands elsewhere after round t+1, and the set of such labels is `Set.Infinite`; U_infinity is `Ulimit` in N-infinity equal to top; hypotheses are `CriticalLaw nu` and d >= 1, plus the two cited externals hGrowth, hBernstein, which the paper's proof uses but its statement does not list; UConcentration and GreenNorms are proved internally and are not among the hypotheses

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
'Parking.Frozen.everyone_settles' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.everyone_settles` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

`Ulimit` is in `ℕ∞`; the statement is a.s. and asserts `= ⊤`, not a junk finite value; `Set.Infinite` is on an infinite type but the property is non-trivial (a finite model would make it false).

## 4. Citations

`External` hypotheses carried by the frozen block:

| External | manifest node | paper origin | state |
|---|---|---|---|
| `Parking.External.Bernstein` | `ext-bernstein` | parking.tex:1175-1188 (lem:bernstein, Pinelis Theorems 4.1 and 3.3) | FROZEN |
| `Parking.External.SandpileGrowth` | `ext-sandpile-growth` | parking.tex:929-943 (thm:BP, Bou-Rabee-Panagiotis) | FROZEN |

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

