# Audit — `lem-shift`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `lem-shift` |
| version | 2 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.shift` |
| file | `Parking/Frozen/Shift.lean` |
| paper source | parking.tex:3047-3052 (label lem:shift) |
| frozen sha256 | `2d8951806eb077073b6f182baa74013a1992982ea62fd5a7b2e6f72f02b6d951` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `no` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.shift (q : ℤ) :
    (∀ l : ℕ, Summable fun j : ℤ =>
        (Parking.binomLaw l (j - q) - Parking.binomLaw l j) ^ 2) ∧
      Summable (fun l : ℕ => ∑' j : ℤ,
        (Parking.binomLaw l (j - q) - Parking.binomLaw l j) ^ 2) ∧
      ∑' l : ℕ, ∑' j : ℤ, (Parking.binomLaw l (j - q) - Parking.binomLaw l j) ^ 2
        = 4 * |(q : ℝ)|
```

Cited `parking.tex` statement:

```latex
\begin{lemma}\label{lem:shift}
	If $d=2$, then for every integer $q$,
	\[
		\sum_{\ell\geq0}\bigl\|\vec p_\ell(\cdot-q)-\vec p_\ell\bigr\|_2^2=4|q|\,.
	\]
\end{lemma}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> one display in the paper; Lean has three conjuncts: (i) for each `l` the sum over `j` of the squared difference is summable, (ii) the series over `l` of these sums is summable, (iii) the identity `tsum_l tsum_j (binomLaw l (j-q) - binomLaw l j)^2 = 4*|q|`; (iii) is the paper's display, (i) and (ii) are additions that exclude a junk `tsum`; no `d = 2` hypothesis, the layer law `vec p_l` is written directly as `binomLaw l` (Bin(l,1/2) on {0..l}, zero on the rest of Z), the norm is the l^2 norm over Z, the translate `p_l(.-q)` is `binomLaw l (j-q)`, `q : Z` is cast to R and quantified outside

The statement-integrity checks that matter here are: hypotheses, quantifier order,
domains, exponents and units. `tools/check_constants.py` reports `no` for this
node (every existential constant is bound before every paper parameter, so it is a
genuine constant). `tools/check_exponents.py` reports every paper exponent either present
in the Lean statement or explicitly explained. `tools/paper_anchors.py` resolves the
source line range from its LaTeX label.

The paper states the display under `d=2`; the two-dimensional oriented layer law is `Bin(ℓ,1/2)`, and the frozen statement writes that law directly as `binomLaw`, so no `d=2` hypothesis is needed. The paper's single display is the third conjunct; the first two `Summable` conjuncts are junk-value guards. No discrepancy in exponents or constants.

## 2. Proof and axiom closure

The proof compiles (`lake build Parking`, 10371 jobs) and its axiom closure is exactly the
three standard foundational axioms:

```
'Parking.Frozen.shift' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.shift` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

The identity has value `4|q|`, a genuine nonnegative real; the two `Summable` conjuncts make both `tsum`s genuine rather than the junk `0`. For `q=0` the value is `0`, which is the correct value. `binomLaw l` is a probability law on `ℤ` (zero outside `{0..l}`) and `q` is an arbitrary integer.

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

