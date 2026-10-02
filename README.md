# Parking-Sharpness

A machine-checked **Lean 4** formalization of the paper
[*Sharpness and critical scaling of parking*](https://arxiv.org/abs/2609.02820)
(Ahmed Bou-Rabee and Christoforos Panagiotis, arXiv:2609.02820), built on
[`mathlib`](https://github.com/leanprover-community/mathlib4), the shared library
[`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability) (`LatticeProb`),
and [`Divisible-Sandpile-Percolation`](https://github.com/nitromannitol/Divisible-Sandpile-Percolation)
(`Sandpile`), the formalization of the divisible sandpile paper this one quotes its growth
estimate from.

Every theorem, lemma, proposition and corollary of the paper is formalized and proved.  The
results the paper quotes from the literature without proof enter as explicit hypotheses of the
theorems that use them.

[![CI](https://github.com/nitromannitol/Parking-Sharpness/actions/workflows/build.yml/badge.svg)](https://github.com/nitromannitol/Parking-Sharpness/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Parking-Sharpness/actions/workflows/comparator.yml/badge.svg)](https://github.com/nitromannitol/Parking-Sharpness/actions/workflows/comparator.yml)

## What is proved

At each site of the lattice `ℤ^d` an independent random integer `η(x)` is placed, the number
of particles at `x` minus the number of holes there; in the parking model each site holds one
car or one spot.  In each round every unsettled particle takes one step of a simple random
walk, and it settles when it reaches a hole that is still unfilled.  The particle odometer
`U_n(x)` is the number of steps taken from `x` in the first `n` rounds, and the divisible
sandpile odometer `u_n(x)` is its deterministic analogue, `u_0 = 0` and
`u_{n+1} = (η + P u_n)⁺`, where `P` is the transition matrix of simple random walk.  The main
theorem (Theorem 1.2) says that if `η(0)` is nonconstant with mean zero and
`E e^{θ|η(0)|} < ∞` for some `θ > 0`, then there are constants `0 < c ≤ C < ∞` with

    c (E u_n(0) + log n)  ≤  E U_n(0)  ≤  C (E u_n(0) + log n)      for every n ≥ 2.

With the growth of `E u_n(0)` that the paper quotes, this gives `E U_n(0) ≍ n^{(4−d)/4}` for
`d ≤ 3` and `E U_n(0) ≍ log n` for `d ≥ 4` at the critical density (Corollary 1.3).  The paper
also proves a stretched-exponential bound with exponent `d/(d+2)` on the settling time below
the critical density (Theorem 1.1), a quenched comparison of the two odometers in each
dimension (Theorem 1.4), results on the nearest hole and particle (Theorems 1.5 and 1.6), the
order of divergence of `E U_∞(0)` as the mean of `η(0)` rises to zero (Theorem 1.7), and the
growth for the oriented walk (Theorem 1.8).

This repository formalizes **every theorem, lemma, proposition and corollary of the paper**
(`tools/check_coverage.py`).  Not formalized: the proof-overview and related-work
subsections, the five remarks, and the two figures.

### Main results

The main theorems are stated in full in [`Parking/MainTheorems.lean`](Parking/MainTheorems.lean),
each proved by `exact` of its certified counterpart in `Parking/Frozen/`, so the statements
displayed there are the certified ones.  The certified statements of Theorems 1.4 and 1.7 also
take `External.Stopping` as a hypothesis; it is proved (`Parking.External.stopping`), and the
main theorems discharge it.

* **`Parking.subcritical_tail`** (Theorem 1.1, `thm:subcritical-tail`): for an integer
  one-site law with negative mean, a positive chance of a particle and an exponential moment,
  `C⁻¹ exp(-C t^{d/(d+2)}) ≤ S_t ≤ C exp(-c t^{d/(d+2)})` for `t ≥ 1`, where `S_t` is the
  expected number of particles started at the origin still active after round `t`.
  Hypothesis: `DonskerVaradhanRange`.
* **`Parking.master`** (Theorem 1.2, `thm:master`): the display above.  Hypotheses:
  `SandpileGrowth`, `Bernstein` (the collected Green estimates and the U-concentration
  estimate, `GreenNorms` and `UConcentration`, are proved in the repository and are not
  hypotheses here).
* **`Parking.growth`** (Corollary 1.3, `cor:growth`): at the critical density,
  `E U_n(0) ≍ n^{(4-d)/4}` and `S_t ≍ (t+1)^{-d/4}` for `d ≤ 3`, and `E U_n(0) ≍ log n` and
  `c/(t+1) ≤ S_t ≤ C log(t+2)/(t+1)` for `d ≥ 4`.  Hypotheses: the same two.
* **`Parking.trichotomy`** (Theorem 1.4, `thm:trichotomy`): for `d ≤ 3` the normalized
  difference `(U_n(0) - u_n(0)) / E u_n(0)` tends to zero almost surely and in every `L^r`,
  and `E U_n(0) / E u_n(0) → 1`; for `d = 4` the ratio is bounded for each law and can be made
  arbitrarily large by the choice of law; for `d ≥ 5` and a law bounded below, `E U_n(0)` and
  `E |U_n(0) - u_n(0)|` are of order `log n` and the ratio diverges.  Hypotheses: the same
  two.
* **`Parking.nearest`** (Theorem 1.5, `thm:nearest`): for `d ≤ 3` at the critical density,
  the probability that the origin is closer to an unfilled hole than to an active particle
  after round `t` tends to zero.  Hypotheses: the same two, the scaling limit of the
  divisible odometer (`SpatialOdometerScaling`), two classical facts about the heat equation
  (`HeatInteriorRegularity`, `HeatCompactness`), and the multivariate Berry-Esseen comparison
  (`MultivariateBerryEsseen`).  The strong minimum principle for the heat equation
  (`HeatStrongMinimum`) and the critical-scale lower tail estimate (`CriticalScaleLowerTail`,
  with its own `VarianceScale` input) are proved in the repository and are not hypotheses here.
* **`Parking.nearest_counterexample`** (Theorem 1.6, `thm:nearest-counterexample`): for
  `d ≥ 5` there is `p ∈ (0, 1/2)` such that, for the law `P(±1) = p`, `P(0) = 1 - 2p`, that
  probability has a positive lower limit.  Hypothesis: `Bernstein`.
* **`Parking.near`** (Theorem 1.7, `thm:near`): for a family of one-site laws of mean `-δ`
  with uniform exponential moments, coupled to the critical law at cost `K δ`, `E U_∞(0)` is
  of order `δ^{-3}`, `δ^{-1}`, `δ^{-1/3}` and `log(e/δ)` in dimensions one, two, three and
  four upward.  Hypotheses: `SandpileGrowth`, `Bernstein` (`UConcentration` is proved in the
  repository and is not a hypothesis here).
* **`Parking.oriented_walk`** (Theorem 1.8, `thm:oriented-walk`): for the oriented walk at
  the critical density, `E U_n(0) ≍ n^{1/4}` for `d = 2` and `E U_n(0) ≍ log n` for `d ≥ 3`,
  and for `d = 2` the ratio to the oriented sandpile odometer tends to one, with a constant
  `μ > 0` such that `E U_n(0) ~ μ n^{1/4}` and `S_t ~ (μ/4) t^{-3/4}`.  Hypotheses:
  `Bernstein`, `OrientedStoppingStability` (`UConcentration` is proved in the repository and
  is not a hypothesis here).

### What is assumed

Eleven results that the paper quotes from the literature are stated in Lean as propositions in
`Parking/External/`, and every theorem whose proof uses one takes it as an explicit hypothesis,
so the statement shows exactly which of them it rests on;
[`ASSUMPTIONS.md`](ASSUMPTIONS.md) lists the eleven with their verbatim Lean statements.
They are **not proved here**, with one partial exception: the growth of the mean divisible
sandpile odometer (`SandpileGrowth`) is also proved, in
`Parking/External/SandpileGrowthProved.lean`, from the formalization of that paper, under
that formalization's own three continuum assumptions.  Nine further results the paper quotes
are proved, mostly from the shared library, and so are not assumed: the optimal stopping
representation of the divisible odometer (`Stopping`), the Green gradient bound
(`GreenGradient`), the variance-scale hypothesis (`VarianceScale`), the binomial and
simple-random-walk local central limit theorems (`BinomialLocalCLT`, `SRWLocalCLT`), the
collected Green-function norms (`GreenNorms`), the U-concentration estimate
(`UConcentration`), the critical-scale lower tail estimate (`CriticalScaleLowerTail`), and,
from classical parabolic theory, the strong minimum principle for the heat equation
(`HeatStrongMinimum`).

### Scope and faithfulness

Every statement of the paper is registered: one Lean declaration per theorem, lemma,
proposition or corollary, and one proposition per cited result.  A registered statement's text
between the lines `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END` is pinned by the
SHA-256 of those bytes in [`ledger/manifest.yaml`](ledger/manifest.yaml), together with the
line range in `paper/parking.tex` and the `\label` it transcribes; the proof after the end
marker may be rewritten freely.  In the manifest, a registered statement is `SEALED` when it
is proved with an axiom closure of exactly the three standard axioms, and `FROZEN` when it is
a cited result assumed rather than proved.  Every registered statement is pinned by hash; only
the `FROZEN` ones are assumed.  The pinned paper is arXiv:2609.02820v1 with the corrections
listed in [`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md).

Two checkers compare the Lean statements with the paper's rather than with their hashes.
`tools/check_clauses.py` counts the assertions of a paper statement and the top-level
conjuncts of its Lean conclusion, and requires a written reading of every node.
`tools/check_exponents.py` extracts the exponents from both sides and matches them, following
the definitions a Lean statement names.  In each frozen statement whose conclusion has a real
existential constant, `tools/check_constants.py` checks that no radius, time, density or
point parameter is bound before it.

The paper-to-Lean map, node by node, is [`CORRESPONDENCE.md`](CORRESPONDENCE.md), and
[`PROOF.md`](PROOF.md) describes the proofs section by section and the Lean tree that carries
them.  In summary:

- The model is `Parking.law d ν` in `Parking/Basic.lean`: an i.i.d. integer configuration with
  one-site law `ν`, independent instruction stacks for the walk, and independent uniform
  variables that order arrivals at a hole.  The particle–hole process itself is
  `LatticeProb.ParticleHole` in the shared library.  The statements are for an arbitrary
  i.i.d. integer law, as in the paper; the parking model is the case where each site is a car
  or a spot.
- Distances on `ℤ^d` are graph distances (`parking.tex:588-601`), so the paper's `|x|` is
  `Parking.graphNorm x`, the `ℓ¹` norm.
- The instruction stacks are indexed from zero here and from one in the paper.
- `U_∞(x)` is the supremum of `U_n(x)` in `ℕ∞`, and `E U_∞(0)` is a lower integral in
  `ℝ≥0∞`, so an unbounded odometer is `⊤` and not a junk value.
- The process is built two ways: the paper's stack construction, and a particle-driven
  construction in which every particle carries its own walk and uniform variables
  (`Parking/Support/Particle.lean`).  `lem:one-particle` and `lem:tagged-monotonicity` are
  stated for the particle-driven construction, and `Parking.constructionsAgree`
  (`Parking/Support/Agree.lean`) proves that the two have the same law, as the paper
  states at `parking.tex:645-646`.
- The nearest-hole-and-particle question is answered for `d ≤ 3` by Theorem 1.5 and for
  `d ≥ 5` by Theorem 1.6; neither covers `d = 4`, where the paper says only that simulations
  suggest the counterexample extends.
- The remaining formulation choices, and the cited inputs each node carries, are recorded in
  the sections "How the Lean statements read the paper" and "Cited inputs and formulation
  choices, node by node" of `CORRESPONDENCE.md`.

## Guarantees

- **No `sorry`** in the library.  Each of the eight Mathlib-only comparator challenges under
  `ParkingAudit/` contains one intentional statement-level `sorry`, which the corresponding
  solution file proves.
- **No custom axiom.**  The eight main theorems depend only on mathlib's three standard
  foundational axioms `propext`, `Classical.choice` and `Quot.sound`.
  [`Parking/Meta/AxiomsAudit.lean`](Parking/Meta/AxiomsAudit.lean) prints their axiom
  dependencies, and `python3 tools/check_axioms.py` fails if the axiom closure of any
  registered statement contains `sorryAx`.  The cited results are hypotheses, not axioms.
- **Independent check of the statements.** So that the main claims can be read without
  trusting the 126,000-line development, all eight main theorems are restated using only
  Mathlib, with no project or library definitions, in
  [`SubcriticalTail`](ParkingAudit/SubcriticalTail/Challenge.lean) (Theorem 1.1),
  [`Master`](ParkingAudit/Master/Challenge.lean) (Theorem 1.2),
  [`Growth`](ParkingAudit/Growth/Challenge.lean) (Corollary 1.3),
  [`Trichotomy`](ParkingAudit/Trichotomy/Challenge.lean) (Theorem 1.4),
  [`Nearest`](ParkingAudit/Nearest/Challenge.lean) (Theorem 1.5),
  [`NearestCounterexample`](ParkingAudit/NearestCounterexample/Challenge.lean) (Theorem 1.6),
  [`Near`](ParkingAudit/Near/Challenge.lean) (Theorem 1.7) and
  [`OrientedWalk`](ParkingAudit/OrientedWalk/Challenge.lean) (Theorem 1.8).  Each challenge
  rebuilds the model from Mathlib primitives (the lattice, i.i.d. fields and the particle–hole
  process as in `Lattice-Probability`; the parking law, the two odometers and their means; the
  walk, lattice kernels and Green functions; the continuum objects of the scaling limits; the
  critical-scale model of the cited lower-tail estimate; and the cited results it assumes) and
  contains one intentional statement-level `sorry`, which the corresponding `Solution.lean`
  fills from the library through the bridges in `ParkingAudit/Support/`.  All eight solutions
  build and depend only on `propext`, `Classical.choice` and `Quot.sound`, and
  `ParkingAudit/StatementRegression.lean` checks locally that each solution statement is
  exactly the challenge statement and mentions no constant of `Parking`, `LatticeProb` or
  `Sandpile`.  The configurations in `ParkingAudit/*/comparator.json` are for
  [`leanprover/comparator`](https://github.com/leanprover/comparator), which confirms that
  the two statements have identical elaborated types and that the proof reduces to the three
  standard axioms; every pair passed with the Lean kernel and again with the independent
  nanoda kernel.  See [`ParkingAudit/README.md`](ParkingAudit/README.md) and
  [`ParkingAudit/COMPARATOR_RUNS.md`](ParkingAudit/COMPARATOR_RUNS.md); the workflow
  [`.github/workflows/comparator.yml`](.github/workflows/comparator.yml) runs the comparator
  on request.
- **Pinned toolchain.** Lean `v4.32.0`, `mathlib` at revision
  `81a5d257c8e410db227a6665ed08f64fea08e997`, `Lattice-Probability` at commit
  `9d44b4d4670df393bb86ac5a4e042f215001cddf` and `Divisible-Sandpile-Percolation` at commit
  `cd8b15a32d00b1eec48f8747339e2d0cfaa73a21`, recorded in
  [`lean-toolchain`](lean-toolchain), [`lakefile.lean`](lakefile.lean) and
  [`lake-manifest.json`](lake-manifest.json).

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

Status: **62 registered statements: 51 `SEALED`, proved here, and 11 `FROZEN`, cited results that are assumed.**  The 51 sealed nodes are machine-checked and no sealed node's
axiom closure contains `sorryAx`.  The 11 `FROZEN` nodes are cited results, stated in
`Parking/External/` and carried as explicit hypotheses by the theorems
that use them; they are assumed here, not proved.  Run
`python3 tools/check_axioms.py` to confirm.  Counts here are generated
from `ledger/manifest.yaml` by `python3 tools/sync_docs.py`; do not
edit them by hand and do not trust a count in prose that the checkers
have not confirmed.

<!-- STATUS-END -->

## Size

About 126,000 lines of Lean in 831 modules (`Parking.lean` and everything under `Parking/`),
of which about 94,000 lines are code once comments and blank lines are removed, on top of
mathlib, the `Lattice-Probability` library and the `Divisible-Sandpile-Percolation`
formalization.  The comparator surface `ParkingAudit/` is not counted.

## Building

The project uses [`elan`](https://github.com/leanprover/elan) (the Lean toolchain manager) and
Lake.  The toolchain is pinned in [`lean-toolchain`](lean-toolchain)
(`leanprover/lean4:v4.32.0`), so `elan` installs the right Lean version automatically, and the
dependencies are pinned to commits in `lakefile.lean` and
[`lake-manifest.json`](lake-manifest.json); `lake` fetches them, and there is nothing to clone
by hand.

```bash
lake exe cache get   # prebuilt Mathlib
lake build           # compile the project
```

```bash
lake build Parking.Meta.AxiomsAudit   # print the axioms of the eight main theorems
lake build ParkingAudit               # the comparator challenges and solutions
lake build ParkingAudit.StatementRegression
```

To use the library, `import Parking` pulls in the whole development; the main results are in
`import Parking.MainTheorems`.  Practical notes for working on the development are in
[`CONTRIBUTING.md`](CONTRIBUTING.md).

The checkers in `tools/` need Python 3 and PyYAML (`pip install pyyaml`).
`check_axioms.py` and `check_warnings.py` run Lean; the others read the manifest, the paper
and the Lean sources.

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
or refreshes a node in the manifest.

## Repository layout

```
Parking/
  MainTheorems.lean   the eight main theorems, stated in full
  Frozen/             the certified statement surface, one frozen statement per file
  External/           the cited results, each a Prop, and the proofs of those that are
                      proved here (Stopping, GreenGradient, SandpileGrowthProved, ...)
  Support/            the definitions and lemmas the frozen statements are proved from
  Meta/               AxiomsAudit.lean
  Basic.lean          the model: the law, the odometers U and u, their means, graphNorm
Parking.lean          the root module (imports the whole library)
ParkingAudit/         Mathlib-only comparator challenges and solutions, with README.md,
                      DESIGN.md and COMPARATOR_RUNS.md
ASSUMPTIONS.md        the cited results assumed, with their Lean statements (generated)
CORRESPONDENCE.md     paper ↔ Lean: conventions, cited inputs, formulation choices, node table
PROOF.md              the proofs section by section and the Lean tree that carries them
CERTIFICATE.md        generated record of the toolchain, the build, each node's axiom
                      closure and the SHA-256 of each frozen statement
CONTRIBUTING.md       building notes and the elaboration policy for new files
formalization.yaml    the mathlib-initiative disclosure of models, tooling, cost and review
CITATION.cff          citation metadata
ledger/manifest.yaml  one row per registered statement: hash, paper source, state
paper/parking.tex     the paper, pinned by the SHA-256 in ledger/manifest.yaml
paper/CHANGES_FROM_ARXIV.md
                      the differences between paper/parking.tex and the arXiv version
paper/parking-arxiv.tex
                      the unmodified arXiv source; paper/arxiv/ holds its figures and .bbl
tools/                the checkers and generators listed under Building
.github/workflows/    the CI build and the comparator audit
```

Results that do not depend on the parking model come from the shared library
`Lattice-Probability`, not from this repository: the scaling-limit toolkit (Chebyshev, Slutsky,
Cramér–Wold, Kolmogorov tail bounds, space-time testing, ...) is `LatticeProb/Prob/Scaling/`;
the convex-order toolkit is `LatticeProb/Prob/ConvexOrder.lean` and its companions; the
binomial law, the lattice kernel and the lattice Riemann sum are under `LatticeProb/Walk/`.
Where a frozen statement names one of these library definitions, `Parking` exports it under
the name the statement uses.

## How this was built

The Lean code was written mostly by Claude (Fable 5.1, Opus 5, Opus 5.5 and Sonnet 5), with contributions by OpenAI's gpt-6-astra, gpt-6-luna and gpt-5.6-luna, DeepSeek-v4.1-flash, GLM-5.3, GLM-5.3-flash and Kimi k3, under the close supervision of the author; models, tooling, cost and review status are disclosed in [`formalization.yaml`](formalization.yaml), following the [mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) standard.

## Authors, citation, acknowledgements

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
