# Sharpness and critical scaling of parking

A machine-checked **Lean 4** formalization of the paper

> Ahmed Bou-Rabee and Christoforos Panagiotis,
> *Sharpness and critical scaling of parking*,
> [arXiv:2609.02820](https://arxiv.org/abs/2609.02820).

The paper's source and the list of its differences from the arXiv version are included under
[`paper/`](paper/). The 8 main results of the paper are proved, in the form in which its
introduction states them, from results cited from the literature that enter as explicit
hypotheses of the theorems that use them; see
[Assumed literature inputs](#assumed-literature-inputs). Every other theorem, lemma,
proposition and corollary of the paper is formalized as well.

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4) and on
two public libraries:
[Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability) (`LatticeProb`), a
library of lattice probability and potential theory, and
[Divisible-Sandpile-Percolation](https://github.com/nitromannitol/Divisible-Sandpile-Percolation)
(`Sandpile`), the formalization of *Quantitative explosion and percolation of the divisible
sandpile* (Bou-Rabee and Panagiotis, [arXiv:2609.02829](https://arxiv.org/abs/2609.02829)),
from which this paper quotes its growth estimate.

[![CI](https://github.com/nitromannitol/Parking-Sharpness/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Parking-Sharpness/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Parking-Sharpness/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Parking-Sharpness/actions/workflows/comparator.yml)

## What is proved

At each site of the lattice `ℤ^d` an independent random integer `η(x)` is placed, the number
of particles at `x` minus the number of holes there; in the parking model each site holds one
car or one spot. In each round every unsettled particle takes one step of a simple random
walk, and it settles when it reaches a hole that is still unfilled. The particle odometer
`U_n(x)` is the number of steps taken from `x` in the first `n` rounds, and the divisible
sandpile odometer `u_n(x)` is its deterministic analogue, `u_0 = 0` and
`u_{n+1} = (η + P u_n)⁺`, where `P` is the transition matrix of simple random walk. The main
theorem (Theorem 1.2) says that if `η(0)` is nonconstant with mean zero and
`E e^{θ|η(0)|} < ∞` for some `θ > 0`, then there are constants `0 < c ≤ C < ∞` with

    c (E u_n(0) + log n)  ≤  E U_n(0)  ≤  C (E u_n(0) + log n)      for every n ≥ 2.

With the growth of `E u_n(0)` that the paper quotes, this gives `E U_n(0) ≍ n^{(4−d)/4}` for
`d ≤ 3` and `E U_n(0) ≍ log n` for `d ≥ 4` at the critical density (Corollary 1.3). The paper
also proves a stretched-exponential bound with exponent `d/(d+2)` on the settling time below
the critical density (Theorem 1.1), a quenched comparison of the two odometers in each
dimension (Theorem 1.4), results on the nearest hole and particle (Theorems 1.5 and 1.6), the
order of divergence of `E U_∞(0)` as the mean of `η(0)` rises to zero (Theorem 1.7), and the
growth for the oriented walk (Theorem 1.8). The model is stated precisely in
[Standing assumptions and scope](#standing-assumptions-and-scope).

The 8 main results, formalized as stated in the introduction of the paper, are collected in
[`Parking/MainTheorems.lean`](Parking/MainTheorems.lean). Each is proved by `exact` of its
certified counterpart in `Parking/Frozen/`, so the statements displayed there are the
certified ones. The certified statements of Theorems 1.4 and 1.7 also take `External.Stopping`
as a hypothesis; it is proved (`Parking.External.stopping`), and the main theorems discharge
it.

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1 (label `thm:subcritical-tail`) | `Parking.subcritical_tail` | stretched-exponential bound on the settling time below the critical density |
| Theorem 1.2 (label `thm:master`) | `Parking.master` | the particle odometer is comparable to the divisible odometer plus `log n` |
| Corollary 1.3 (label `cor:growth`) | `Parking.growth` | growth of `E U_n(0)` and `S_t` at the critical density |
| Theorem 1.4 (label `thm:trichotomy`) | `Parking.trichotomy` | quenched comparison of the two odometers in each dimension |
| Theorem 1.5 (label `thm:nearest`) | `Parking.nearest` | the nearest hole versus the nearest particle, `d ≤ 3` |
| Theorem 1.6 (label `thm:nearest-counterexample`) | `Parking.nearest_counterexample` | a counterexample for `d ≥ 5` |
| Theorem 1.7 (label `thm:near`) | `Parking.near` | order of `E U_∞(0)` as the mean rises to zero |
| Theorem 1.8 (label `thm:oriented-walk`) | `Parking.oriented_walk` | growth for the oriented walk at the critical density |

**Theorem 1.1 (subcritical tail, `thm:subcritical-tail`).** For an integer one-site law with
negative mean, a positive chance of a particle and an exponential moment,
`C⁻¹ exp(-C t^{d/(d+2)}) ≤ S_t ≤ C exp(-c t^{d/(d+2)})` for `t ≥ 1`, where `S_t` is the
expected number of particles started at the origin still active after round `t`. Hypothesis:
`DonskerVaradhanRange`.

**Theorem 1.2 (master, `thm:master`).** The display above. Hypotheses: `SandpileGrowth`,
`Bernstein` (the collected Green estimates and the U-concentration estimate, `GreenNorms` and
`UConcentration`, are proved in the repository and are not hypotheses here).

**Corollary 1.3 (growth, `cor:growth`).** At the critical density:

1. *Low dimensions.* For `d ≤ 3`, `E U_n(0) ≍ n^{(4-d)/4}` and `S_t ≍ (t+1)^{-d/4}`.
2. *High dimensions.* For `d ≥ 4`, `E U_n(0) ≍ log n` and `c/(t+1) ≤ S_t ≤ C log(t+2)/(t+1)`.

Hypotheses: the same two.

**Theorem 1.4 (trichotomy, `thm:trichotomy`).**

1. *`d ≤ 3`.* The normalized difference `(U_n(0) - u_n(0)) / E u_n(0)` tends to zero almost
   surely and in every `L^r`, and `E U_n(0) / E u_n(0) → 1`.
2. *`d = 4`.* The ratio is bounded for each law and can be made arbitrarily large by the choice
   of law.
3. *`d ≥ 5`.* For a law bounded below, `E U_n(0)` and `E |U_n(0) - u_n(0)|` are of order
   `log n` and the ratio diverges.

Hypotheses: the same two.

**Theorem 1.5 (nearest hole and particle, `thm:nearest`).** For `d ≤ 3` at the critical
density, the probability that the origin is closer to an unfilled hole than to an active
particle after round `t` tends to zero. Hypotheses: the same two, the scaling limit of the
divisible odometer (`SpatialOdometerScaling`), two classical facts about the heat equation
(`HeatInteriorRegularity`, `HeatCompactness`), and the multivariate Berry-Esseen comparison
(`MultivariateBerryEsseen`). The strong minimum principle for the heat equation
(`HeatStrongMinimum`) and the critical-scale lower tail estimate (`CriticalScaleLowerTail`,
with its own `VarianceScale` input) are proved in the repository and are not hypotheses here.

**Theorem 1.6 (nearest-hole counterexample, `thm:nearest-counterexample`).** For `d ≥ 5` there
is `p ∈ (0, 1/2)` such that, for the law `P(±1) = p`, `P(0) = 1 - 2p`, that probability has a
positive lower limit. Hypothesis: `Bernstein`.

**Theorem 1.7 (near criticality, `thm:near`).** For a family of one-site laws of mean `-δ`
with uniform exponential moments, coupled to the critical law at cost `K δ`, `E U_∞(0)` is of
order `δ^{-3}`, `δ^{-1}`, `δ^{-1/3}` and `log(e/δ)` in dimensions one, two, three and four
upward. Hypotheses: `SandpileGrowth`, `Bernstein` (`UConcentration` is proved in the
repository and is not a hypothesis here).

**Theorem 1.8 (oriented walk, `thm:oriented-walk`).** For the oriented walk at the critical
density, `E U_n(0) ≍ n^{1/4}` for `d = 2` and `E U_n(0) ≍ log n` for `d ≥ 3`, and for `d = 2`
the ratio to the oriented sandpile odometer tends to one, with a constant `μ > 0` such that
`E U_n(0) ~ μ n^{1/4}` and `S_t ~ (μ/4) t^{-3/4}`. Hypotheses: `Bernstein`,
`OrientedStoppingStability` (`UConcentration` is proved in the repository and is not a
hypothesis here).

In Lean, `Parking.law d ν` is the model, `Parking.meanU` and `Parking.meanu` are the means of
the two odometers, `Parking.S` is the expected number of active particles, and
`U_∞(x)` is the supremum of `U_n(x)` in `ℕ∞`, with `E U_∞(0)` a lower integral in `ℝ≥0∞`.

This repository formalizes every theorem, lemma, proposition and corollary of the paper
(`tools/check_coverage.py`).

## Corrections to the published version

The formalization follows `paper/parking.tex`, a corrected text of the paper: it is
[arXiv:2609.02820v1](https://arxiv.org/abs/2609.02820v1) with five corrections.
[`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md) lists every change against the
arXiv version.

## Standing assumptions and scope

1. **Every theorem is about every integer law that satisfies its hypotheses.** The statements
   are for `Parking.law d ν` (`Parking/Basic.lean`) with `d ≥ 1` and an arbitrary probability
   measure `ν` on `ℤ`, as in the paper; the parking model is the case where each site is a
   car or a spot. Each theorem adds the hypotheses on `ν` that the paper states, for example a
   negative mean, a positive chance of a particle and an exponential moment in Theorem 1.1,
   and a nonconstant law of mean zero with an exponential moment in Theorem 1.2
   (`Parking.CriticalLaw ν` in Corollary 1.3). The constants are bound after `d` and `ν`, so
   they depend on them.
2. **Axioms and incomplete proofs.** The library contains no `sorry`, no `admit`, no
   `native_decide` and no new `axiom`. The axiom report of each main theorem consists of
   exactly `propext`, `Classical.choice` and `Quot.sound`. The main theorems take cited
   results as explicit hypotheses, listed under
   [Assumed literature inputs](#assumed-literature-inputs); nothing else is assumed.
3. **What is not formalized.** The proof-overview and related-work subsections, the five
   remarks, and the two figures.
4. **Model and conventions.**
   - The model is `Parking.law d ν`: an i.i.d. integer configuration with one-site law `ν`,
     independent instruction stacks for the walk, and independent uniform variables that
     order arrivals at a hole. The particle–hole process itself is
     `LatticeProb.ParticleHole` in the shared library.
   - Distances on `ℤ^d` are graph distances (`parking.tex:588-601`), so the paper's `|x|` is
     `Parking.graphNorm x`, the `ℓ¹` norm.
   - The instruction stacks are indexed from zero here and from one in the paper.
   - `U_∞(x)` is the supremum of `U_n(x)` in `ℕ∞`, and `E U_∞(0)` is a lower integral in
     `ℝ≥0∞`, so an unbounded odometer is `⊤` and not a junk value.
   - The process is built two ways: the paper's stack construction, and a particle-driven
     construction in which every particle carries its own walk and uniform variables
     (`Parking/Support/Particle.lean`). `lem:one-particle` and `lem:tagged-monotonicity` are
     stated for the particle-driven construction, and `Parking.constructionsAgree`
     (`Parking/Support/Agree.lean`) proves that the two have the same law, as the paper
     states at `parking.tex:645-646`.
5. **Explicit versus implicit.** The certified statements of Theorems 1.4 and 1.7 take
   `External.Stopping` as a hypothesis, which is proved in the repository and discharged in
   the main theorems. The nearest-hole-and-particle question is answered for `d ≤ 3` by
   Theorem 1.5 and for `d ≥ 5` by Theorem 1.6; neither covers `d = 4`, where the paper says
   only that simulations suggest the counterexample extends. The remaining formulation
   choices, and the cited inputs each node carries, are recorded in the sections "How the Lean
   statements read the paper" and "Cited inputs and formulation choices, node by node" of
   [`CORRESPONDENCE.md`](CORRESPONDENCE.md).
6. **Statements without a formal counterpart.** Every statement of the paper is registered:
   one Lean declaration per theorem, lemma, proposition or corollary, and one proposition per
   cited result. The paper-to-Lean map, node by node, is
   [`CORRESPONDENCE.md`](CORRESPONDENCE.md), and [`PROOF.md`](PROOF.md) describes the proofs
   section by section and the Lean tree that carries them.

## Assumed literature inputs

Eleven results that the paper quotes from the literature are stated in Lean as propositions in
`Parking/External/`, and every theorem whose proof uses one takes it as an explicit
hypothesis, so the statement shows exactly which of them it rests on.
[`ASSUMPTIONS.md`](ASSUMPTIONS.md) lists the eleven with their verbatim Lean statements. They
are **not proved here**. Eight of them are hypotheses of the main theorems:

| Hypothesis | Content | Source | Used by |
| --- | --- | --- | --- |
| `Parking.External.DonskerVaradhanRange` (`hDV`) | `log E_0 exp(-a\|R_t\|) ~ -k t^{d/(d+2)}` for the range `R_t` of simple random walk | Donsker and Varadhan (1979), Theorem 1 | Theorem 1.1 |
| `Parking.External.SandpileGrowth` (`hGrowth`) | growth of the mean divisible sandpile odometer `E u_n(0)`: `n^{(4-d)/4}` for `d ≤ 3`, `log n` for `d ≥ 4`, with first-order terms | Bou-Rabee and Panagiotis, *Quantitative explosion and percolation of the divisible sandpile* (arXiv:2609.02829), quoted at label `thm:BP` | Theorems 1.2, 1.3, 1.4, 1.5, 1.7 |
| `Parking.External.Bernstein` (`hBernstein`, `hBern`) | `L^r` moment bounds for martingale sums, in the bounded-increment (Rosenthal–Burkholder) form and the factorial-moment (Bernstein) form | Pinelis, Theorems 4.1 and 3.3 (label `lem:bernstein`) | Theorems 1.2 to 1.8 |
| `Parking.External.SpatialOdometerScaling` (`hOdometer`) | parabolic scaling limit of the rescaled divisible odometer: a Brownian optimal-stopping value driven by spatial white noise, jointly with the scenery | Bou-Rabee and Panagiotis, *Quantitative explosion and percolation of the divisible sandpile* (arXiv:2609.02829), Theorem 1.3(i)(b) | Theorem 1.5 |
| `Parking.External.HeatInteriorRegularity` (`hInterior`) | continuous distributional solutions of `∂_s u = (2d)⁻¹ Δu` are smooth classical solutions | classical parabolic theory (hypoelliptic interior regularity) | Theorem 1.5 |
| `Parking.External.HeatCompactness` (`hCompact`) | nonnegative smooth heat solutions with bounded local `L¹` norms have a locally uniformly convergent subsequence whose limit is a smooth heat solution | classical parabolic interior estimates | Theorem 1.5 |
| `Parking.External.MultivariateBerryEsseen` (`hBerry`) | orthant probabilities of linear forms of i.i.d. mean-zero variables compared with a centred Gaussian of the same covariance, with a Berry–Esseen error | Raič, Theorem 1.1 | Theorem 1.5 |
| `Parking.External.OrientedStoppingStability` (`hStability`) | stability of optimal-stopping values under uniform convergence of bounded rewards, and an invariance principle for the stopped oriented walk | Coquet and Toldo (2007), Theorem 3 and Corollary 4 | Theorem 1.8 |

The other three, `LinearFieldScaling`, `SpatialFixedTimeTightness` and
`SpatialStoppingStability`, are stated in `Parking/External/` and recorded in the manifest as
cited results; none of them is a hypothesis of a main theorem.

The growth of the mean divisible sandpile odometer (`SandpileGrowth`) is also proved, in
`Parking/External/SandpileGrowthProved.lean`, from the formalization of that paper; that theorem
takes three hypotheses: `Sandpile.External.LocalCLT`, which the pinned formalization proves
(`Sandpile.External.localCLT`), and two that it assumes,
`Sandpile.External.ContinuumStoppingStability` and the family
`Sandpile.External.ContinuumOptimalStopping`. Nine further results the paper quotes are
proved, mostly from the shared library, and so are not assumed: the optimal stopping
representation of the divisible odometer (`Stopping`), the Green gradient bound
(`GreenGradient`), the variance-scale hypothesis (`VarianceScale`), the binomial and
simple-random-walk local central limit theorems (`BinomialLocalCLT`, `SRWLocalCLT`), the
collected Green-function norms (`GreenNorms`), the U-concentration estimate
(`UConcentration`), the critical-scale lower tail estimate (`CriticalScaleLowerTail`), and,
from classical parabolic theory, the strong minimum principle for the heat equation
(`HeatStrongMinimum`).

## Registered statements

Every statement of the paper is registered in [`ledger/manifest.yaml`](ledger/manifest.yaml).
A registered statement's text between the lines `-- FROZEN-STATEMENT-BEGIN` and
`-- FROZEN-STATEMENT-END` is pinned by the SHA-256 of those bytes in the manifest, together
with the line range in `paper/parking.tex` and the `\label` it transcribes; the proof after
the end marker may be rewritten freely. In the manifest, a registered statement is `PROVED`
when it is proved with an axiom closure of exactly the three standard axioms, `SEALED` when it
is a definition node proved by a companion theorem, and `FROZEN` when it is a cited result
assumed rather than proved. Every registered statement is pinned by hash; only the `FROZEN`
ones are assumed.

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

Status: **62 registered statements: 49 `PROVED`, 2 `SEALED` (definition nodes proved by companion theorems), and 11 `FROZEN`, cited results that are assumed.**  The 51 proved nodes are machine-checked and no proved node's
axiom closure contains `sorryAx`.  The 2 `SEALED` nodes are proved `definition` nodes,
sealed by the companion theorem named in `CERTIFICATE.md`.  The 11 `FROZEN` nodes are cited results, stated in
`Parking/External/` and carried as explicit hypotheses by the theorems
that use them; they are assumed here, not proved.  Run
`python3 tools/check_axioms.py` to confirm.  Counts here are generated
from `ledger/manifest.yaml` by `python3 tools/sync_docs.py`; do not
edit them by hand and do not trust a count in prose that the checkers
have not confirmed.

<!-- STATUS-END -->

Two checkers compare the Lean statements with the paper's rather than with their hashes.
`tools/check_clauses.py` counts the assertions of a paper statement and the top-level
conjuncts of its Lean conclusion, and requires a written reading of every node.
`tools/check_exponents.py` extracts the exponents from both sides and matches them, following
the definitions a Lean statement names. In each frozen statement whose conclusion has a real
existential constant, `tools/check_constants.py` checks that no radius, time, density or point
parameter is bound before it.

## Guarantees

- **No `sorry`.** The library has none, and `tools/check_manifest.py` rejects any `sorry`
  outside a registered `DRAFT_SORRY` node, of which there is none. The 8 comparator
  challenges under [`ParkingAudit/`](ParkingAudit/) each contain one intentional
  statement-level `sorry`, which the corresponding solution file proves.
- **Standard axioms only.** The axiom report of each of the 8 main theorems lists exactly
  `propext`, `Classical.choice` and `Quot.sound`.
  [`Parking/Meta/AxiomsAudit.lean`](Parking/Meta/AxiomsAudit.lean) prints the reports, and
  `python3 tools/check_axioms.py` fails if the axiom closure of any registered statement
  contains `sorryAx`. The cited results are hypotheses, not axioms.
- **Builds from a clean checkout.** In continuous integration, `lake build` of a fresh
  checkout completes 10,371 jobs without error, and the build fails on any warning or `sorry`
  warning.
- **Independent check of the statements.** The 8 main theorems are restated in
  [`ParkingAudit/`](ParkingAudit/) using mathlib alone, with no project or library
  definitions, one challenge file per theorem
  ([`SubcriticalTail`](ParkingAudit/SubcriticalTail/Challenge.lean),
  [`Master`](ParkingAudit/Master/Challenge.lean),
  [`Growth`](ParkingAudit/Growth/Challenge.lean),
  [`Trichotomy`](ParkingAudit/Trichotomy/Challenge.lean),
  [`Nearest`](ParkingAudit/Nearest/Challenge.lean),
  [`NearestCounterexample`](ParkingAudit/NearestCounterexample/Challenge.lean),
  [`Near`](ParkingAudit/Near/Challenge.lean) and
  [`OrientedWalk`](ParkingAudit/OrientedWalk/Challenge.lean)). Each challenge rebuilds the
  model from mathlib primitives (the lattice, i.i.d. fields and the particle–hole process as in
  Lattice-Probability; the parking law, the two odometers and their means; the walk, lattice
  kernels and Green functions; the continuum objects of the scaling limits; the critical-scale
  model of the cited lower-tail estimate; and the cited results it assumes). The solution file
  proves the statement from the library through its own bridge in `ParkingAudit/Support/`, and
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the statement
  is proved, with only the three standard axioms, through independent implementations of the
  Lean kernel. See [`ParkingAudit/README.md`](ParkingAudit/README.md) and
  [`ParkingAudit/COMPARATOR_RUNS.md`](ParkingAudit/COMPARATOR_RUNS.md).
- **Pinned toolchain and dependencies.** Lean `v4.32.0`; mathlib at revision
  `81a5d257c8e410db227a6665ed08f64fea08e997`, Lattice-Probability at commit
  `9d44b4d4670df393bb86ac5a4e042f215001cddf` and Divisible-Sandpile-Percolation at commit
  `cd8b15a32d00b1eec48f8747339e2d0cfaa73a21`, recorded in [`lean-toolchain`](lean-toolchain),
  [`lakefile.lean`](lakefile.lean) and [`lake-manifest.json`](lake-manifest.json) (see
  [Building](#building)).
- **The paper is part of the repository.** The statement map refers to the version in
  [`paper/`](paper/), pinned to the SHA-256
  `4aa03aee7c30e24bffc9a4e8220f775b5c71706e694dcd9bcffc865c8135d3a0` of `paper/parking.tex`.

## Size

The library contains 831 Lean files with 126,421 physical lines (`Parking.lean` and everything
under `Parking/`), on top of mathlib, Lattice-Probability and Divisible-Sandpile-Percolation.
The comparator sources (32 files, 18,228 lines) are counted separately.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches the dependencies.

```bash
lake exe cache get   # prebuilt mathlib
lake build
```

The 2 source dependencies, Lattice-Probability and Divisible-Sandpile-Percolation, have no
prebuilt cache, so the first build compiles them as well as the library. `import Parking`
loads the main theorems and what they use, and `import Parking.MainTheorems` loads the main
theorems and what they use.

The dependencies are public repositories, pinned to exact commits in
[`lake-manifest.json`](lake-manifest.json):

- mathlib: `https://github.com/leanprover-community/mathlib4` at
  `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Lattice-Probability: `https://github.com/nitromannitol/Lattice-Probability` at
  `9d44b4d4670df393bb86ac5a4e042f215001cddf`.
- Divisible-Sandpile-Percolation: `https://github.com/nitromannitol/Divisible-Sandpile-Percolation`
  at `cd8b15a32d00b1eec48f8747339e2d0cfaa73a21`.

To reproduce the axiom reports and build the comparator libraries:

```bash
lake build Parking.Meta.AxiomsAudit   # print the axioms of the eight main theorems
lake build ParkingAudit               # the comparator challenges and solutions
```

The checkers in `tools/` need Python 3 and PyYAML (`pip install pyyaml`). `check_axioms.py` and
`check_warnings.py` run Lean; the others read the manifest, the paper and the Lean sources.

| command | what it guarantees |
|---|---|
| `python3 tools/check_manifest.py` | every node's file holds exactly one frozen block whose SHA-256 equals `frozen_sha256` and which declares exactly the node's `export`; every file in `Parking/Frozen/` belongs to one node; `Parking/` and `Parking.lean` contain no `axiom`, `admit` or `sorryAx`, and `sorry` occurs only in files of `DRAFT_SORRY` nodes (none is) |
| `python3 tools/check_axioms.py` | runs `#print axioms` on every manifest export, and fails if any axiom closure contains `sorryAx` |
| `python3 tools/check_warnings.py` | `lake build Parking` emits no Lean warning other than one `declaration uses 'sorry'` for each `DRAFT_SORRY` node (none is registered) |
| `python3 tools/check_constants.py` | in a frozen statement whose conclusion has a real-valued `∃`, none of `R n t m r s L x y u v e z ε η δ` is a theorem parameter, so the constant cannot depend on it |
| `python3 tools/check_coverage.py` | every labelled theorem, lemma, proposition and corollary of `paper/parking.tex` is named in the `source` of some manifest node |
| `python3 tools/check_clauses.py` | compares the assertion count of each paper statement with the conjunct count of its Lean statement, and requires a recorded reading of every node |
| `python3 tools/check_exponents.py` | compares the exponents written in a paper statement with those in its Lean statement and the definitions it names |

Also in `tools/`: `paper_anchors.py` and `paper_citations.py` check the `parking.tex:<lines>`
ranges in the manifest and in the Lean docstrings against the paper's labels; `sync_docs.py`
checks (`--write` regenerates) the status block of this file and the registered-statements
table of `CORRESPONDENCE.md`; `assumptions.py` regenerates `ASSUMPTIONS.md` (`--check`
verifies it is current); `certificate.py` regenerates `CERTIFICATE.md`; `freeze.py` registers
or refreshes a node in the manifest. See [`CONTRIBUTING.md`](CONTRIBUTING.md) for further
building notes.

## Running the comparators

Each comparator pair has a configuration `ParkingAudit/<Pair>/comparator.json`, for `<Pair>`
one of `SubcriticalTail`, `Master`, `Growth`, `Trichotomy`, `Nearest`,
`NearestCounterexample`, `Near` and `OrientedWalk`, that permits exactly `propext`,
`Classical.choice` and `Quot.sound` and enables the independent nanoda kernel. The comparator
checks that the solution proves the challenge statement, compares their dependency closures,
and replays the proof with the Lean and NanoDa kernels.

To run one pair locally, build `leanprover/comparator`, `lean4export`, `landrun` and
`nanoda_lib` at the revisions pinned in
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml) (also recorded in
[`ParkingAudit/COMPARATOR_RUNS.md`](ParkingAudit/COMPARATOR_RUNS.md)), and from the
repository root run:

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator ParkingAudit/<Pair>/comparator.json
```

A pair passes when the comparator prints `Your solution is okay!`. The comparator workflow
runs the eight pairs one after the other in a single job on GitHub-hosted runners.

There are two continuous-integration workflows: **CI** builds the library, builds the axiom
audit and checks the frozen statements; **Comparator audit** checks all 8 challenge/solution
pairs. Both run on pushes to `main` that change Lean files, `tools/`, `paper/`, `ledger/`,
`formalization.yaml` or the build configuration, and can be started manually from the
[Actions page](https://github.com/nitromannitol/Parking-Sharpness/actions). See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
Parking.lean              the root module, importing the main theorems and what they use
Parking/
  MainTheorems.lean       the eight main theorems, stated in full
  Frozen/                 the certified statement surface, one frozen statement per file
  External/               the cited results, each a Prop, and the proofs of those that are
                          proved here (Stopping, GreenGradient, SandpileGrowthProved, ...)
  Support/                the definitions and lemmas the frozen statements are proved from
  Meta/AxiomsAudit.lean   the axiom report, compiled by `lake build`, not imported by the root
  Basic.lean              the model: the law, the odometers U and u, their means, graphNorm
ParkingAudit/             the mathlib-only restatements and their solutions
  README.md               what each comparator pair checks
  DESIGN.md               how the pairs are built: vocabulary, bridges
  COMPARATOR_RUNS.md      the comparator pins and results
  <Pair>/                 Challenge.lean, SolutionBasic.lean, Solution.lean, comparator.json
  Support/                one bridge per pair, identifying the vocabulary with the library
ASSUMPTIONS.md            the cited results assumed, with their Lean statements (generated)
CORRESPONDENCE.md         paper to Lean: conventions, cited inputs, formulation choices, node table
PROOF.md                  the proofs section by section and the Lean tree that carries them
CERTIFICATE.md            generated record of the toolchain, the build, each node's axiom
                          closure and the SHA-256 of each frozen statement
ledger/manifest.yaml      one row per registered statement: hash, paper source, state
paper/                    parking.tex, the paper pinned by the SHA-256 in ledger/manifest.yaml;
                          CHANGES_FROM_ARXIV.md, the differences between it and the arXiv
                          version; parking-arxiv.tex, the unmodified arXiv source, with arxiv/
                          holding its figures and .bbl
tools/                    the checkers and generators listed under Building
.github/workflows/        the CI build and the comparator audit
formalization.yaml        the mathlib-initiative disclosure of models, tooling, cost and review
CITATION.cff              citation metadata
CONTRIBUTING.md           building notes and the elaboration policy for new files
lakefile.lean, lake-manifest.json, lean-toolchain   the pinned build
```

Results that do not depend on the parking model come from the shared library
Lattice-Probability, not from this repository: the scaling-limit toolkit (Chebyshev, Slutsky,
Cramér–Wold, Kolmogorov tail bounds, space-time testing, ...) is `LatticeProb/Prob/Scaling/`;
the convex-order toolkit is `LatticeProb/Prob/ConvexOrder.lean` and its companions; the
binomial law, the lattice kernel and the lattice Riemann sum are under `LatticeProb/Walk/`.
Where a frozen statement names one of these library definitions, `Parking` exports it under
the name the statement uses.

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and
DeepSeek, under the direction of the author. Every proof is checked by the Lean kernel. The
models, tooling, cost and review status are disclosed in [`formalization.yaml`](formalization.yaml),
following the [mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors and citation

The Lean development is by **Ahmed Bou-Rabee**.  The paper it formalizes, arXiv:2609.02820, is
joint work of Ahmed Bou-Rabee and Christoforos Panagiotis.  To cite the formalization, use
[`CITATION.cff`](CITATION.cff).

This formalization is built on [Lean 4](https://lean-lang.org),
[Mathlib](https://github.com/leanprover-community/mathlib4), the shared library
[`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability), and the
formalization [`Divisible-Sandpile-Percolation`](https://github.com/nitromannitol/Divisible-Sandpile-Percolation)
of the divisible sandpile paper; the comparator audit in [`ParkingAudit/`](ParkingAudit/) is set up for
[`leanprover/comparator`](https://github.com/leanprover/comparator).

## License

The Lean code in this repository is licensed under the **Apache License 2.0** (see
[`LICENSE`](LICENSE)).  The paper source in `paper/` is included for reference and is not
covered by the Apache license.
