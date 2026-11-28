# Sharpness and critical scaling of parking

[![CI](https://github.com/nitromannitol/Parking-Sharpness/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Parking-Sharpness/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Parking-Sharpness/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Parking-Sharpness/actions/workflows/comparator.yml)

A Lean 4 formalization of the paper

> Ahmed Bou-Rabee and Christoforos Panagiotis,
> [*Sharpness and critical scaling of parking*](https://arxiv.org/abs/2609.02820),
> arXiv:2609.02820 (2026).

The paper studies particles that perform random walks on `ℤᵈ` and settle at the first free hole
they reach, a model that contains the parking model of cars and parking spots. When particles and
holes have the same density, it finds how fast the number of steps taken from a site grows, in every
dimension; below that density, it bounds the settling time by stretched exponentials. Every
numbered result of the paper is proved in Lean with only the standard axioms, and so are the results
it quotes from other works. The main theorems therefore hold with no assumption beyond those of the
paper.

## The paper

At each site `x` of `ℤᵈ` place a random number of particles and of holes, independently from site
to site, and write `η(x)` for the number of particles minus the number of holes. In each round,
every particle that has not settled takes one step of simple random walk. A particle *settles* when
it reaches a hole that is still unfilled; the particles not yet settled are *active*. In the
*parking model* of Damron, Gravner, Junge, Lyu and Sivakoff, each site holds one car or one parking
spot.

The *particle odometer* `U_n(x)` counts the steps taken from `x` in the first `n` rounds. Its
deterministic analogue is the odometer of the *divisible sandpile* of Levine and Peres:
`u_0 = 0` and `u_{n+1} = (η + P u_n)⁺`, where `P` is the transition matrix of simple random walk.
Write `S_t` for the expected number of particles that start at the origin and have not settled by
time `t`. The critical density is `E η(0) = 0`, where particles and holes are equally dense; below
it, `E η(0) < 0`.

- **Theorem 1.1.** Below the critical density, `S_t` is bounded above and below by stretched
  exponentials `exp(−c t^{d/(d+2)})`.
- **Theorem 1.2.** At the critical density, `E U_n(0)` is comparable to `E u_n(0) + log n`.
- **Corollary 1.3.** At the critical density, `E U_n(0)` has order `n^{(4−d)/4}` for `d ≤ 3` and
  `log n` for `d ≥ 4`.
- **Theorem 1.4.** The two odometers agree to leading order for `d ≤ 3`, have bounded ratio for
  `d = 4`, and have diverging ratio for `d ≥ 5`.
- **Theorems 1.5 and 1.6.** For `d ≤ 3`, the probability that the origin is closer to an unfilled
  hole than to an active particle tends to zero; for `d ≥ 5` it does not, for some laws.
- **Theorem 1.7.** As the mean of `η(0)` rises to zero, the expected total number of steps from the
  origin, `E U_∞(0)`, diverges at a rate that depends on the dimension.
- **Theorem 1.8.** For the oriented walk on `ℤ²`, which steps only in the positive coordinate
  directions, `E U_n(0)` is asymptotic to `μ n^{1/4}`.

Precisely, let `η` have i.i.d. integer-valued coordinates.

**Theorem 1.1.** Suppose `E|η(0)| < ∞`, `E η(0) < 0`, `P(η(0) > 0) > 0` and `E e^{θη(0)} < ∞` for
some `θ > 0`. Then there are `0 < c ≤ C < ∞` with
`C⁻¹ exp(−C t^{d/(d+2)}) ≤ S_t ≤ C exp(−c t^{d/(d+2)})` for every `t ≥ 1`.

**Theorem 1.2.** Suppose `η(0)` is nonconstant, `E η(0) = 0` and `E e^{θ|η(0)|} < ∞` for some
`θ > 0`. Then there are `0 < c ≤ C < ∞` with
`c (E u_n(0) + log n) ≤ E U_n(0) ≤ C (E u_n(0) + log n)` for every `n ≥ 2`.

**Corollary 1.3.** Under the assumptions of Theorem 1.2, `E U_n(0) ≍ n^{(4−d)/4}` and
`S_t ≍ (t+1)^{−d/4}` for `d ≤ 3`, and `E U_n(0) ≍ log n` and
`c/(t+1) ≤ S_t ≤ C log(t+2)/(t+1)` for `d ≥ 4`.

**Theorem 1.4.** Under the assumptions of Theorem 1.2:
(i) for `d ≤ 3`, `(U_n(0) − u_n(0))/E u_n(0) → 0` almost surely and in every `Lʳ`, and
`n^{−(4−d)/4} E U_n(0)` has a limit in `(0, ∞)`;
(ii) for `d = 4`, `E U_n(0)/E u_n(0)` is at least one and bounded for each law, but for every `B`
some law has `liminf E U_n(0)/E u_n(0) ≥ B`;
(iii) for `d ≥ 5` and `η(0)` bounded below, `E U_n(0) ≍ log n`, `E|U_n(0) − u_n(0)| ≍ log n` and
`E U_n(0)/E u_n(0) → ∞`.

**Theorem 1.5.** Let `d ≤ 3`, under the assumptions of Theorem 1.2. The probability that the origin
is closer to an unfilled hole than to an active particle at time `t` tends to zero.

**Theorem 1.6.** For every `d ≥ 5` there are `p ∈ (0, 1/2)` and `c > 0` such that, for the law
`P(η(0) = ±1) = p`, `P(η(0) = 0) = 1 − 2p`, the probability in Theorem 1.5 has lower limit at
least `c`.

**Theorem 1.7.** Let `η_δ` have i.i.d. coordinates of mean `−δ`, for `0 ≤ δ ≤ δ₀`, with `η_0(0)`
nonconstant, uniformly bounded exponential moments, and couplings with
`E|η_δ(0) − η_0(0)| ≤ Kδ`. Then, as `δ ↓ 0`, `E U^δ_∞(0)` has order `δ⁻³`, `δ⁻¹`, `δ^{−1/3}` and
`log(e/δ)` for `d = 1`, `2`, `3` and `d ≥ 4`.

**Theorem 1.8.** Let the walk step from `x` to `x + eᵢ` with probability `1/d` for each `i`. Under
the assumptions of Theorem 1.2, `E U_n(0) ≍ n^{1/4}` for `d = 2` and `E U_n(0) ≍ log n` for `d ≥ 3`.
For `d = 2` there is `μ ∈ (0, ∞)` with `E U_n(0) ~ μ n^{1/4}` and `S_t ~ (μ/4) t^{−3/4}`.

## The main theorems in Lean

The main theorems are in [`Parking/MainTheoremsUnconditional.lean`](Parking/MainTheoremsUnconditional.lean),
one file each in [`Parking/Unconditional/`](Parking/Unconditional/). Their only hypotheses are
those of the paper on the dimension and on the law of `η(0)`.

| Paper | Lean declaration |
| --- | --- |
| Theorem 1.1 | `Parking.subcritical_tail_proved` |
| Theorem 1.2 | `Parking.master_proved` |
| Corollary 1.3 | `Parking.growth_proved` |
| Theorem 1.4 | `Parking.trichotomy_proved` |
| Theorem 1.5 | `Parking.nearest_proved` |
| Theorem 1.6 | `Parking.nearest_counterexample_proved` |
| Theorem 1.7 | `Parking.near_proved` |
| Theorem 1.8 | `Parking.oriented_walk_proved` |

How to read the statements: the model is defined in [`Parking/Basic.lean`](Parking/Basic.lean).
`Parking.law d ν` is the law of the process with one-site law `ν`, a probability measure on `ℤ`,
and `Parking.orientedLaw d ν` is its oriented version. `Parking.meanU` and `Parking.meanu` are the
means `E U_n(0)` and `E u_n(0)`, and `Parking.S` is `S_t`. `Parking.CriticalLaw ν` collects the
assumptions of Theorem 1.2. `Parking.meanUlimit` is `E U_∞(0)`, a lower integral in `ℝ≥0∞`, so an
infinite odometer has the value `⊤`.

[`Parking/MainTheorems.lean`](Parking/MainTheorems.lean) states the same eight results with the
quoted results that their proofs use as explicit hypotheses, for example `Parking.master`.

## All numbered results

The paper has 45 numbered theorems, lemmas, propositions and corollaries. The table lists each with
the Lean declaration that proves it. Four rest on other works: Lemma 3.1, Theorem 3.4 and Lemma 4.5
are quoted, and Lemma 6.1 is deduced from a remark of Bou-Rabee and Panagiotis. All four are proved
here.

The declarations of ten results take the quoted results that their proofs use as explicit
hypotheses: Propositions 4.6, 6.3, 7.1, 8.1, 8.3 and 10.4, Theorems 6.2 and 7.2, and Lemmas 8.2 and
10.3. Each of these quoted results is proved in the repository with no hypothesis, and
[`ASSUMPTIONS.md`](ASSUMPTIONS.md) and [`CERTIFICATE.md`](CERTIFICATE.md) name the proofs. These ten
results therefore also hold with no hypothesis beyond those of the paper.

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1 | `Parking.subcritical_tail_proved` | Below the critical density, `S_t` has stretched-exponential bounds with exponent `d/(d+2)`. |
| Theorem 1.2 | `Parking.master_proved` | At the critical density, `E U_n(0) ≍ E u_n(0) + log n`. |
| Corollary 1.3 | `Parking.growth_proved` | `E U_n(0)` and `S_t` at the critical density, in every dimension. |
| Theorem 1.4 | `Parking.trichotomy_proved` | The quenched comparison of `U_n(0)` and `u_n(0)` for `d ≤ 3`, `d = 4` and `d ≥ 5`. |
| Theorem 1.5 | `Parking.nearest_proved` | `d ≤ 3`: the origin is eventually closer to an active particle than to an unfilled hole. |
| Theorem 1.6 | `Parking.nearest_counterexample_proved` | `d ≥ 5`: a three-point law for which this fails with positive probability. |
| Theorem 1.7 | `Parking.near_proved` | The order of `E U^δ_∞(0)` as the mean `−δ` rises to zero. |
| Theorem 1.8 | `Parking.oriented_walk_proved` | The growth of `E U_n(0)` for the oriented walk. |
| Lemma 2.1 | `Parking.Frozen.parallel` | The odometer satisfies `U_{n+1}(x) = (η(x) + Σ_y I_{y,x}(U_n(y)))⁺`. |
| Lemma 2.2 | `Parking.Frozen.deferred` | `{U_n(y) ≥ j}` does not depend on the `j`-th instruction at `y`. |
| Lemma 2.3 | `Parking.Frozen.one_particle` | Adding one particle changes the active particles or the unfilled holes at one site. |
| Lemma 2.4 | `Parking.Frozen.tagged_monotonicity` | In that coupling, every shared particle stays active at least as long. |
| Lemma 2.5 | `Parking.Frozen.transport` | `E A_t(0) = S_t`, `E U_n(0) = Σ_{s<n} S_s`, and the particles at the origin are exchangeable. |
| Lemma 2.6 | `Parking.Frozen.activity_holes` | `E A_t(0) − E H_t(0) = E η(0)`. |
| Lemma 2.7 | `Parking.Frozen.density_compare` | `0 ≤ S̃_t − S_t ≤ E η̃(0) − E η(0)` for coupled configurations `η ≤ η̃`. |
| Lemma 3.1 | `Parking.External.stopping` | Quoted from Bou-Rabee, Peres and Sava-Huss: `u_n(x)` is the value of an optimal stopping problem for the walk. |
| Theorem 3.2 | `Parking.Frozen.comparison` | `u_n(x) ≤ E[U_n(x) \| η]`. |
| Theorem 3.4 | `Parking.External.sandpileGrowth_holds` | Quoted from Bou-Rabee and Panagiotis: the growth of `E u_n(0)` for i.i.d. real mean-zero `η`. |
| Lemma 4.1 | `Parking.Frozen.pathwise_comparison` | `\|U_n(x) − u_n(x)\| ≤ 2 w*_n(x)`. |
| Lemma 4.2 | `Parking.Frozen.gamma_sum` | `Σ_y sup_{m≤n} Γ_m(y) ≤ C κ_d(n)`. |
| Lemma 4.3 | `Parking.Frozen.exposure` | Unread instructions are independent given the exposed ones. |
| Lemma 4.4 | `Parking.Frozen.w_martingale` | `w_n(0)` is a sum of martingale differences with bounded increments. |
| Lemma 4.5 | `Parking.External.bernstein` | Quoted from Pinelis: Rosenthal–Burkholder and Bernstein moment bounds for martingale sums. |
| Proposition 4.6 | `Parking.Frozen.w_moment` | `Lʳ` bounds on `w_m(0)` and `w*_n(0)`. |
| Lemma 5.1 | `Parking.Frozen.critical_density` | At the critical density, `liminf t S_t ≥ c` and `E U_n(0) ≥ c log n − C`. |
| Corollary 5.2 | `Parking.Frozen.cor_critical` | `E U_n(0) ≥ max{E u_n(0), c log n − C}`. |
| Lemma 6.1 | `Parking.External.uConcentration` | From a remark of Bou-Rabee and Panagiotis: concentration of `v_n(0)` for a general finite-range kernel. |
| Theorem 6.2 | `Parking.Frozen.upper` | `E U_n(0) ≤ C (E u_n(0) + log n)`, and its `Lʳ` form. |
| Proposition 6.3 | `Parking.Frozen.everyone_settles` | Every particle settles and every hole is filled, but `U_∞(x) = ∞`. |
| Proposition 7.1 | `Parking.Frozen.discrepancy` | `d ≤ 3`: `Lʳ` bounds on `U_n(0) − u_n(0)` and a tail bound. |
| Theorem 7.2 | `Parking.Frozen.four_sparse` | `d = 4`: for sparse `±1` laws, `liminf E U_n(0)/E u_n(0) ≥ c log(e/ε)`. |
| Proposition 8.1 | `Parking.Frozen.spatial_scaling` | `d ≤ 3`: the scaling limit of the rescaled particle odometer. |
| Lemma 8.2 | `Parking.Frozen.nearest_one_point` | Moment bounds on `U_t(x)`, and `h_t ↓ 0`. |
| Proposition 8.3 | `Parking.Frozen.nearest_two_hole` | A bound on the probability of two unfilled holes. |
| Lemma 8.4 | `Parking.Frozen.nearest_close_pair` | `P(H_t(x) = H_t(z) = 1) ≤ 2p h_t`. |
| Lemma 9.1 | `Parking.Frozen.range_lower` | `S_t ≥ E[η(0)⁺] E_0[P(η(0) ≥ 0)^{\|R_t\|−1}]`. |
| Lemma 9.2 | `Parking.Frozen.product` | A covariance inequality under the tilted law. |
| Theorem 9.3 | `Parking.Frozen.subcritical` | `S_t ≤ C E_0 e^{−a\|R_t\|}` below the critical density. |
| Lemma 10.1 | `Parking.Frozen.near_tilt` | `S^δ_t ≤ C E_0 e^{−cδ²\|R_t\|}`. |
| Proposition 10.2 | `Parking.Frozen.resolvent` | Bounds on `E_0 e^{−a\|R_t\|}` and on their tail sums. |
| Lemma 10.3 | `Parking.Frozen.mean_horizon` | A bound on the scenery collected up to a stopping time of mean `M`. |
| Proposition 10.4 | `Parking.Frozen.near_divisible` | The order of `E u^δ_∞(0)` as `δ ↓ 0`. |
| Lemma 11.1 | `Parking.Frozen.shift` | `d = 2`: `Σ_ℓ ‖p⃗_ℓ(· − q) − p⃗_ℓ‖₂² = 4\|q\|`. |
| Theorem 11.2 | `Parking.Frozen.oriented` | Bounds on the oriented divisible odometer. |
| Proposition 11.3 | `Parking.oriented_scaling_proved` | `d = 2`: `n^{−1/4} u⃗_{⌊nT⌋}(0)` converges in law, and `n^{−1/4} E u⃗_n(0) → μ`. |

[`CORRESPONDENCE.md`](CORRESPONDENCE.md) maps every result to its Lean statement and records each
formulation choice, and [`PROOF.md`](PROOF.md) describes the proofs section by section.

## Corrections

The Lean statements follow [`paper/parking.tex`](paper/parking.tex), a corrected text of
[arXiv:2609.02820v1](https://arxiv.org/abs/2609.02820v1). It differs from the arXiv version by five
corrections, listed with their reasons in
[`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md). No correction changes the hypotheses
or the conclusion of a statement.

- One completes the argument that the two constructions of the process have the same law
  (Section 2).
- One names the construction in which Lemma 2.3, and so Lemma 2.4, is stated.
- Two add missing steps to the proofs of Lemmas 2.5 and 2.7.
- One explains how the second bound of Lemma 4.5 follows from the tail bound of Pinelis that it
  cites.

The unmodified arXiv source is [`paper/parking-arxiv.tex`](paper/parking-arxiv.tex).

## Scope

- **The model.** The statements are for `Parking.law d ν` with `d ≥ 1` and an arbitrary
  probability measure `ν` on `ℤ`. The constants are chosen after `d` and `ν`, so they depend on
  them.
- **Two constructions.** The process is built from the instruction stacks of the paper and from a
  construction in which every particle carries its own walk and uniform variables. Lemmas 2.3 and
  2.4 are stated for the second, and `Parking.constructionsAgree` proves that the two have the same
  law.
- **Conventions.** Distances are graph distances, so the paper's `|x|` is the `ℓ¹` norm
  `graphNorm x`. The instruction stacks are indexed from zero here and from one in the paper.
- **Theorem 1.1.** The hypothesis-free form is proved from two-sided bounds of order
  `exp(−c t^{d/(d+2)})` on `E_0 exp(−a|R_t|)`, in place of the Donsker–Varadhan limit that the paper
  cites. That limit is also proved, as `Parking.External.donskerVaradhanRange_holds`.
- **Dimension four.** Theorems 1.5 and 1.6 cover `d ≤ 3` and `d ≥ 5`. The paper says only that
  simulations suggest that the counterexample extends to `d = 4`.
- **Not formalized.** The proof overview and related-work subsections, the five remarks and the two
  figures.

## Checking the proofs

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

[`ledger/manifest.yaml`](ledger/manifest.yaml) pins the text of 80 Lean
statements, and of the paper source `paper/parking.tex`, by their SHA-256.  The
80 statements are 67 theorems, all proved, and 13 results of other works,
stated as propositions in `Parking/External/` and each proved by a theorem named in
[`CERTIFICATE.md`](CERTIFICATE.md).  No proof depends on `sorryAx`, which
`python3 tools/check_axioms.py` confirms.  This paragraph is generated from the manifest by
`python3 tools/sync_docs.py`.

<!-- STATUS-END -->

- **No `sorry`.** The library has none, which `tools/check_manifest.py` checks. Each of the 16
  comparator challenges under [`ParkingAudit/`](ParkingAudit/) contains one intentional `sorry` at
  the statement, which the matching solution proves.
- **Standard axioms only.** [`Parking/Meta/AxiomsAudit.lean`](Parking/Meta/AxiomsAudit.lean) prints
  the axioms of the main theorems in both forms: exactly `propext`, `Classical.choice` and
  `Quot.sound`. [`CERTIFICATE.md`](CERTIFICATE.md) records the axioms of every pinned statement.
- **Independent check of the statements.** Each main theorem has two comparator pairs in
  [`ParkingAudit/`](ParkingAudit/): one restates it with the quoted results as hypotheses, and one,
  named `<Pair>Unconditional`, restates it with none. Each `Challenge.lean` rebuilds the model from
  mathlib alone and states the theorem; the `Solution.lean` proves it from the library.
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the two statements
  agree, that only the standard axioms are used, and replays the proof through an independent
  implementation of the Lean kernel. See [`ParkingAudit/README.md`](ParkingAudit/README.md).
- **Continuous integration.** The **CI** workflow builds the library with no warning, builds the
  axiom audit and checks the pinned statements against their hashes. The **Comparator audit**
  workflow runs the comparator on the 16 pairs.

`Parking.lean` and `Parking/` contain 915 Lean files with 142,617 lines, built on mathlib,
Lattice-Probability and Divisible-Sandpile-Percolation.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain (Lean `v4.35.0-rc2`) is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches the dependencies.

```bash
lake exe cache get                    # prebuilt mathlib
lake build                            # the library
lake build Parking.Meta.AxiomsAudit   # print the axioms of the main theorems and their forms
lake build ParkingAudit               # the comparator challenges and solutions
```

Lattice-Probability and Divisible-Sandpile-Percolation have no prebuilt cache, so the first build
compiles them as well as the library. `import Parking.MainTheoremsUnconditional` loads the main
theorems and what they use. The dependencies are public repositories, pinned in
[`lake-manifest.json`](lake-manifest.json):

- mathlib: `https://github.com/leanprover-community/mathlib4` at
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`;
- Lattice-Probability: `https://github.com/nitromannitol/Lattice-Probability` at
  `89de1230d02e1a737a9c7ecd776d34070be014ee`;
- Divisible-Sandpile-Percolation, the formalization of *Quantitative explosion and percolation of
  the divisible sandpile* (Bou-Rabee and Panagiotis, [arXiv:2609.02829](https://arxiv.org/abs/2609.02829)),
  from which the paper quotes Theorem 3.4:
  `https://github.com/nitromannitol/Divisible-Sandpile-Percolation` at
  `8470df06ae1c7847decf57f86b741bc7a4fc5d2e`.

The checkers in `tools/` need Python 3 and PyYAML (`pip install pyyaml`); for example,
`python3 tools/check_manifest.py` checks the pinned statements and `python3 tools/check_axioms.py`
the axioms. See [`CONTRIBUTING.md`](CONTRIBUTING.md) for further building notes.

## Running the comparators

Each pair has a configuration `ParkingAudit/<Pair>/comparator.json`, for `<Pair>` one of
`SubcriticalTail`, `Master`, `Growth`, `Trichotomy`, `Nearest`, `NearestCounterexample`, `Near` and
`OrientedWalk`, or one of these names followed by `Unconditional`. It permits exactly `propext`,
`Classical.choice` and `Quot.sound` and enables the nanoda kernel. Build `leanprover/comparator`,
`lean4export`, `landrun` and `nanoda_lib` at the revisions pinned in
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml), then run from the repository
root

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator ParkingAudit/<Pair>/comparator.json
```

A pair passes when the comparator prints `Your solution is okay!`.
[`ParkingAudit/COMPARATOR_RUNS.md`](ParkingAudit/COMPARATOR_RUNS.md) records the pins and the results.

## Repository layout

```text
Parking.lean                     the root module
Parking/
  MainTheoremsUnconditional.lean the eight main theorems; one file each in Unconditional/
  MainTheorems.lean              the same results, with the quoted results as hypotheses
  Basic.lean                     the model: the law, the odometers U and u, their means
  Frozen/                        the statements of the numbered results and their proofs, one per file
  External/                      the quoted results, each a proposition, and their proofs
  Support/                       the lemmas the statements are proved from
  Meta/AxiomsAudit.lean          the axiom report
ParkingAudit/                    the 16 comparator pairs
ledger/manifest.yaml             the hash and the paper location of each pinned statement
paper/                           parking.tex (corrected), parking-arxiv.tex, CHANGES_FROM_ARXIV.md
tools/                           the checkers
ASSUMPTIONS.md                   the quoted results, their Lean statements and their proofs
CORRESPONDENCE.md                paper to Lean, result by result
PROOF.md                         the proofs section by section
CERTIFICATE.md                   the toolchain, the axioms and the hash of each registered statement
```

Results that do not depend on the parking model, such as the scaling-limit and convex-order
toolkits, the binomial law and the lattice kernels, come from Lattice-Probability.

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and DeepSeek,
under the direction of Ahmed Bou-Rabee. Every proof is checked by the Lean kernel. The models,
tooling, cost and review status are recorded in [`formalization.yaml`](formalization.yaml), following
the [mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) standard.

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
