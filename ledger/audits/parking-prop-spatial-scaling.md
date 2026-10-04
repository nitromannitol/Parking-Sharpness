# Audit — `prop-spatial-scaling`

Independent refute-first audit of a frozen `SEALED` node of the Parking-Sharpness
formalization. Auditor: AI worker (Batch B), independent of the Lean authors; no Lean
file and no manifest entry was modified. All findings below are reproducible from the
commands recorded in `ledger/audits/parking-2026-10-04.md`.

| field | value |
|---|---|
| node id | `prop-spatial-scaling` |
| version | 12 |
| state | `SEALED` |
| kind | `theorem` |
| export | `Parking.Frozen.spatial_scaling` |
| file | `Parking/Frozen/SpatialScaling.lean` |
| paper source | parking.tex:1694-1752 (label prop:spatial-scaling); the GreenNorms hypothesis is dropped, discharged internally from Parking.External.greenNorms; the UConcentration hypothesis is likewise dropped, discharged internally from Parking.External.uConcentration; the HeatStrongMinimum hypothesis is likewise dropped, discharged internally from Parking.External.heatStrongMinimum |
| frozen sha256 | `e02373648e37d71919ca0cce7cf96e63fc91a1215183d40c718fa74dc570c077` |
| axiom closure | `[propext, Classical.choice, Quot.sound]` |
| clause check | `check_clauses.py` records the correspondence below |
| constant-order check | `yes` |

**Verdict: PASS.**

## 1. Statement integrity

Frozen block (the contract; verified byte-for-byte by `tools/check_manifest.py`):

```lean
theorem Parking.Frozen.spatial_scaling (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hOdometer : Parking.External.SpatialOdometerScaling)
    (hInterior : Parking.External.HeatInteriorRegularity)
    (hCompact : Parking.External.HeatCompactness)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
      (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ) (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
      (v : Ω → ℝ → (Fin d → ℝ) → ℝ),
      Parking.IsSpatialWhiteNoise d (variance (fun k : ℤ => (k : ℝ)) ν) Q W ∧
      (∀ φ, Parking.IsTestFun φ → Measurable (W φ)) ∧
      (∀ s x, Measurable fun ω => Uc ω s x) ∧
      (∀ s x, Measurable fun ω => v ω s x) ∧
      (∀ ω x, Uc ω 0 x = 0) ∧
      (∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2) ∧
      (∀ ω x, Monotone fun s => Uc ω s x) ∧
      (∃ Z : Ω → ℝ → (Fin d → ℝ) → ℝ,
        Parking.IsSpatialGreenPairing d (variance (fun k : ℤ => (k : ℝ)) ν) Q W Z ∧
        (∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Z ω p.1 p.2) ∧
        ∃ (ΩB : Type) (_ : MeasurableSpace ΩB) (PB : Measure ΩB)
            (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)),
          LatticeProb.IsBrownianSpace d 0 B PB ∧
          ∀ ω T x, 0 ≤ T →
            Uc ω T x = Parking.contUc (Parking.ofBrownianSpace B) PB Z ω T x) ∧
      (∀ (m k p : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (χ : Fin p → (Fin d → ℝ) → ℝ)
          (sp : Fin k → ℝ × (Fin d → ℝ)),
        (∀ i, Parking.IsTestFun (φ i)) → (∀ l, Parking.IsTestFun (χ l)) →
        (∀ j, 0 < (sp j).1) →
        ∀ F : BoundedContinuousFunction
            ((Fin m → ℝ) × (Fin k → ℝ) × (Fin k → ℝ) × (Fin p → ℝ)) ℝ,
          Tendsto (fun R : ℝ => ∫ w, F (fun i => Parking.scenePair w R (φ i),
                fun j => Parking.barDivisible w R (sp j).1 (sp j).2,
                fun j => Parking.barOdometer w R (sp j).1 (sp j).2,
                fun l => Parking.signedPair w R (χ l)) ∂(Parking.law d ν)) atTop
            (𝓝 (∫ ω, F (fun i => W (φ i) ω,
                fun j => Uc ω (sp j).1 (sp j).2,
                fun j => Uc ω (sp j).1 (sp j).2,
                fun l => W (χ l) ω
                  + ∫ x, Uc ω 1 x * Parking.contOp d (χ l) x) ∂Q))) ∧
      (∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → (∀ p ∈ K, 0 < p.1) → ∀ ε : ℝ, 0 < ε →
        Tendsto (fun R : ℝ => ((Parking.law d ν) {w | ε < ⨆ p ∈ K,
            |Parking.barOdometer w R p.1 p.2 - Parking.barDivisible w R p.1 p.2|}).toReal)
          atTop (𝓝 0)) ∧
      (∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → (∀ p ∈ K, 0 < p.1) → ∀ ε : ℝ, 0 < ε →
        ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
          ((Parking.law d ν) {w | ε < ⨆ p ∈ K, ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ,
              |Parking.barDivisible w R p.1 p.2 - Parking.barDivisible w R q.1 q.2|}).toReal
            ≤ ε') ∧
      (∀ᵐ ω ∂Q, ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, Parking.IsSpaceTimeTest ψ →
        tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
        -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
          = (∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * Parking.contOp d (fun x => ψ (p.1, x)) p.2)
            + W (fun x => ∫ s : ℝ, ψ (s, x)) ω) ∧
      (∀ᵐ ω ∂Q, ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin d → ℝ) => v ω p.1 p.2)
          {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} ∧
        (∀ ψ : ℝ × (Fin d → ℝ) → ℝ, Parking.IsSpaceTimeTest ψ →
          tsupport ψ ⊆ {p : ℝ × (Fin d → ℝ) | 0 < Uc ω p.1 p.2} →
          -∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1
            = ∫ p : ℝ × (Fin d → ℝ), v ω p.1 p.2 * ψ p) ∧
        ∀ s x, 0 < Uc ω s x → 0 < v ω s x)
```

Cited `parking.tex` statement:

```latex
\begin{proposition}[Spatial scaling]\label{prop:spatial-scaling}
	Let $d\leq3$, and let $(\eta(x))_{x\in\Z^d}$ be independent and identically
	distributed, integer-valued and nonconstant, with $\E\eta(0)=0$ and
	$\E e^{\theta|\eta(0)|}<\infty$ for some $\theta>0$. For $R>0$,
	$s\geq0$, and $x\in\mathbb R^d$, let
	\[
		\overline U_R(s,x)\coloneqq
		R^{d/2-2}U_{\lfloor sR^2\rfloor}(\lfloor Rx\rfloor),
		\qquad
		\overline u_R(s,x)\coloneqq
		R^{d/2-2}u_{\lfloor sR^2\rfloor}(\lfloor Rx\rfloor),
	\]
	where the floor is taken coordinatewise. For $R>0$ and
	$\varphi\in C_c^\infty(\mathbb R^d)$, let
	\[
		\langle\eta_R,\varphi\rangle
		\coloneqq R^{-d/2}\sum_y\eta(y)\varphi(y/R)
	\]
	and
	\[
		\langle\nu_R,\varphi\rangle
		\coloneqq R^{-d/2}\sum_y
		\bigl(A_{\lfloor R^2\rfloor}(y)-H_{\lfloor R^2\rfloor}(y)\bigr)
		\varphi(y/R).
	\]
	Let $\mathcal W$ be a mean-zero spatial white noise with covariance
	\[
		\E\langle\mathcal W,\varphi\rangle\langle\mathcal W,\psi\rangle
		=\Var\eta(0)\int_{\mathbb R^d}\varphi(x)\psi(x)\,dx
		\qquad(\varphi,\psi\in C_c^\infty(\mathbb R^d))\,.
	\]
	Let $\mathcal U$ be the continuous Brownian optimal-stopping value driven by
	$\mathcal W$, with $\mathcal U(0,\cdot)=0$. Then, jointly,
	\begin{equation}\label{eq:space-time-scaling}
		(\eta_R,\overline u_R,\overline U_R)
		\Longrightarrow(\mathcal W,\mathcal U,\mathcal U)
	\end{equation}
	as $R\to\infty$, with the first coordinate converging as a random
	distribution and the last two locally uniformly on
	$(0,\infty)\times\mathbb R^d$.
	Let
	$\mathcal O\coloneqq\{\mathcal U>0\}$ and
	$\mathcal L\coloneqq(2d)^{-1}\Delta$. Then, in
	the sense of distributions on $\mathcal O$,
	\begin{equation}\label{eq:continuum-equation}
		\partial_s\mathcal U=\mathcal L\mathcal U+\mathcal W.
	\end{equation}
	For every $\varphi\in C_c^\infty(\mathbb R^d)$, jointly with
	\eqref{eq:space-time-scaling},
	\begin{equation}\label{eq:signed-density-limit}
		\langle\nu_R,\varphi\rangle\Longrightarrow
		\langle\mathcal W+\mathcal L\mathcal U(1,\cdot),\varphi\rangle.
	\end{equation}
	Moreover, on $\mathcal O$ the distribution
	$v=\partial_s\mathcal U$ is a smooth function and
	\begin{equation}\label{eq:strict-time-derivative}
		v(s,x)>0\qquad ((s,x)\in\mathcal O).
	\end{equation}
\end{proposition}
```

`tools/check_clauses.py` reads the paper statement against the frozen Lean statement and
records the following correspondence (verbatim):

> paper: four displays plus one sentence, five assertions after the setup (joint convergence eq:space-time-scaling; driven equation on O eq:continuum-equation; signed-density limit eq:signed-density-limit, jointly with the first; v smooth on O; v>0 on O eq:strict-time-derivative); Lean: `exists Omega Q W Uc v` (the limit objects are asserted to exist on a probability space, the paper takes W and U as given) then 13 conjuncts: (1) `IsSpatialWhiteNoise` of intensity Var nu (linear, mean 0, covariance v*int phi psi, Gaussian marginals); (2)-(4) measurability of `W phi`, `Uc s x`, `v s x`; (5)-(7) `Uc(0,.)=0`, jointly continuous, monotone in s; (8) `exists Z` a continuous Green field paired with W plus a Brownian space B with `Uc = contUc` (Z plus the Brownian optimal-stopping value) for T>=0, which is Lean's definition of 'continuous Brownian optimal-stopping value driven by W'; (9) finite-dimensional convergence, for finite families of test functions and positive-time points, of (<eta_R,phi_i>, u_R, U_R, <nu_R,chi_l>) to (W phi_i, U, U, W chi_l + int U(1,x) L chi_l(x) dx) against bounded continuous F, carrying the finite-dimensional content of eq:space-time-scaling and eq:signed-density-limit together (L U(1,.) is tested by integration by parts); (10) for compact K in (0,inf) x R^d, sup_K |U_R - u_R| -> 0 in probability; (11) equicontinuity in probability of u_R on such K; (9)-(11) are Lean's reformulation of 'converging as a random distribution / locally uniformly' (finite-dimensional convergence plus asymptotic equicontinuity plus closeness), rather than convergence in law in a topology; (12) a.e. omega, for every space-time test psi with tsupport psi inside O: `-int U d_s psi = int U L psi + W(int psi ds)`; (13) a.e. omega: v is C^infinity on O, v is the distributional d_s U on O, and `0<U s x -> 0<v s x`; rescalings: `barDivisible`, `barOdometer` are R^{d/2-2}(.)_{floor(sR^2)}(floor(Rx)), `scenePair` is <eta_R,phi>, `signedPair` is <nu_R,phi> with A-H at floor(R^2), R real to infinity, law `law d nu`, `nu : CriticalLaw` (probability, nonconstant, mean 0, exponential moment), `1<=d<=3`; five cited inputs enter as hypotheses (`SandpileGrowth`, `Bernstein`, `SpatialOdometerScaling`, `HeatInteriorRegularity`, `HeatCompactness`), absent from the paper's statement; `UConcentration`, `GreenNorms` and `HeatStrongMinimum` are proved internally and are not among the hypotheses

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
'Parking.Frozen.spatial_scaling' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(produced by `#print axioms Parking.Frozen.spatial_scaling` under `lake env lean`; the same output is
produced for all 62 manifest nodes by `python3 tools/check_axioms.py`, which reports
`62 clean, 0 depend on sorryAx, 0 unresolved`.) No `sorryAx`, no `axiom`, no `admit`.

## 3. Non-vacuity / junk

The statement asserts existence of a probability space and limit objects, convergence against all bounded continuous test functions, a.s. PDE identities on `{Uc>0}`, and `0<v` on `O`; none of this is `True` or a junk value.

## 4. Citations

`External` hypotheses carried by the frozen block:

| External | manifest node | paper origin | state |
|---|---|---|---|
| `Parking.External.Bernstein` | `ext-bernstein` | parking.tex:1175-1188 (lem:bernstein, Pinelis Theorems 4.1 and 3.3) | FROZEN |
| `Parking.External.HeatCompactness` | `ext-heat-compactness` | parking.tex:1800-1820 (prop:spatial-scaling, Step 3, parabolic compactness) | FROZEN |
| `Parking.External.HeatInteriorRegularity` | `ext-heat-interior-regularity` | parking.tex:1800-1820 (prop:spatial-scaling, Step 3, hypoelliptic interior regularity) | FROZEN |
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

