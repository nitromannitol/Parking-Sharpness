# Audit — `thm-nearest`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `thm-nearest` |
| version | 14 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.nearest` |
| file | `Parking/Frozen/Nearest.lean` |
| paper source | parking.tex:266-275 (label thm:nearest); the VarianceScale hypothesis is dropped, discharged internally from Parking.External.varianceScale; the GreenNorms hypothesis is likewise dropped, discharged internally from Parking.External.greenNorms; the UConcentration hypothesis is likewise dropped, discharged internally from Parking.External.uConcentration; the HeatStrongMinimum hypothesis is likewise dropped, discharged internally from Parking.External.heatStrongMinimum; the CriticalScaleLowerTail hypothesis is likewise dropped, discharged internally from Parking.External.criticalScaleLowerTail |
| frozen sha256 | `15b063f0bbef52bec0962640dc4f5f757a34ccab2c08c824601938b029868ccc` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `no` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.nearest (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hOdometer : Parking.External.SpatialOdometerScaling)
    (hInterior : Parking.External.HeatInteriorRegularity)
    (hCompact : Parking.External.HeatCompactness)
    (hBerry : Parking.External.MultivariateBerryEsseen)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ)
    (hν : Parking.CriticalLaw ν) :
    Tendsto (fun t : ℕ => ((Parking.law d ν) {ω | Parking.HoleCloser ω t}).toReal)
      atTop (𝓝 0)
```

Cited `parking.tex` statement:

```latex
\begin{theorem}\label{thm:nearest}
	Let $d\leq3$, and let $(\eta(x))_{x\in\Z^d}$ be independent and identically
	distributed, integer-valued and nonconstant, with $\E\eta(0)=0$ and
	$\E e^{\theta|\eta(0)|}<\infty$ for some $\theta>0$. Then
	\[
		\P(\text{the origin is closer to an unfilled hole than to an active
		particle at time } t)\longrightarrow0\,,
	\]
	as $t\to\infty$.
\end{theorem}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> one assertion: `Tendsto` of `(law d nu {HoleCloser omega t}).toReal` to 0 as t : N (rounds) -> infinity; `HoleCloser` is graph (l^1) distance to the nearest unfilled hole strictly less than that to the nearest active particle, both in `N∞` (inf over empty set is top, so holes present and no active particle counts as hole closer); hypotheses `1 <= d <= 3` and `CriticalLaw nu` (integer-valued, non-Dirac, mean zero, exponential moment); the paper's statement is unconditional but Lean carries six cited inputs the proof uses as explicit hypotheses (SandpileGrowth, Bernstein, SpatialOdometerScaling, HeatInteriorRegularity, HeatCompactness, MultivariateBerryEsseen); UConcentration, GreenNorms, HeatStrongMinimum, CriticalScaleLowerTail and VarianceScale are each proved internally, discharged from Parking.External.uConcentration, greenNorms, heatStrongMinimum, criticalScaleLowerTail and varianceScale respectively, and are not among the hypotheses; conclusion unchanged

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
'Parking.Frozen.nearest' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.nearest` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

`Tendsto … atTop (𝓝 0)` of a probability in `[0,1]` is a genuine limit statement. `HoleCloser` uses `ℕ∞` with `⊤` for an absent hole/particle, avoiding junk finite distances.

## 4. Citations

`External` hypotheses carried by the frozen block:

| External | manifest node | paper origin | state |
|---|---|---|---|
| `Parking.External.Bernstein` | `ext-bernstein` | parking.tex:1175-1188 (lem:bernstein, Pinelis Theorems 4.1 and 3.3) | FROZEN |
| `Parking.External.HeatCompactness` | `ext-heat-compactness` | parking.tex:1800-1820 (prop:spatial-scaling, Step 3, parabolic compactness) | FROZEN |
| `Parking.External.HeatInteriorRegularity` | `ext-heat-interior-regularity` | parking.tex:1800-1820 (prop:spatial-scaling, Step 3, hypoelliptic interior regularity) | FROZEN |
| `Parking.External.MultivariateBerryEsseen` | `ext-multivariate-berry-esseen` | parking.tex:1822-1848 (critical_toppling, Raic Theorem 1.1) | FROZEN |
| `Parking.External.SandpileGrowth` | `ext-sandpile-growth` | parking.tex:929-943 (thm:BP, Bou-Rabee-Panagiotis) | FROZEN |
| `Parking.External.SpatialOdometerScaling` | `ext-spatial-odometer-scaling` | parking.tex:1756-1767 (BP Theorem 1.3(i)(b)) | FROZEN |

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

