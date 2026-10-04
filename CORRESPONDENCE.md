# Correspondence: paper ↔ Lean

Maps every frozen declaration to *Sharpness and critical scaling of parking*
(Bou-Rabee–Panagiotis).

## Conventions

- The paper is pinned at `paper/parking.tex`; its SHA-256 is in
  `ledger/manifest.yaml`.  Source locations are `parking.tex:<line range>` plus
  the LaTeX `\label` name.  Never cite an equation numeral.
- The bytes between `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END`
  are the contract.  `python3 tools/check_manifest.py` is the authority on the
  hash recipe.
- The paper numbers the instruction stacks from one and this formalization from
  zero, so `ρ_{j+1}(y)` is `ω.2.1 (y, j)` throughout.
- Distances on `ℤ^d` are graph distances (`parking.tex:588-601`), so the
  paper's `|x|` is `Parking.graphNorm x`, the `l^1` norm.

## External inputs

Every cited result the paper uses without proof is a `Prop` in `Parking/External/`, frozen and
pinned like a statement.  The assumed ones enter only as explicit hypotheses of the nodes whose
proofs use them; the proved ones are proved in this repository, and the nodes that use them
obtain them internally.  The nodes that carry each assumed result as a hypothesis are listed in
the "External inputs" table of [`CERTIFICATE.md`](CERTIFICATE.md) and in Part C of
[`PROOF.md`](PROOF.md).

| node | cited result | state |
|---|---|---|
| `ext-sandpile-growth` | Bou-Rabee–Panagiotis, Theorem 1.3, Corollary 6.2, Theorem 6.6 and (94) | assumed; also proved under hypotheses by `ext-sandpile-growth-proved` |
| `ext-stopping` | Bou-Rabee–Peres–Sava-Huss, Theorem 3.2 | proved here (`Parking.External.stopping`) |
| `ext-bernstein` | Pinelis, Theorems 4.1 and 3.3 | assumed |
| `ext-u-concentration` | Bou-Rabee–Panagiotis, Remark 3.4 | proved here (`Parking.External.uConcentration`) |
| `ext-green-norms` | Bou-Rabee–Panagiotis, Section 3.1, the collected Green estimates | proved here (`Parking.External.greenNorms`) |
| `ext-critical-scale-lower-tail` | Bou-Rabee–Panagiotis, the critical-scale lower tail estimate; `sandpile.tex:1696-1720`, cited at `parking.tex:1822-1848` | proved here (`Parking.External.criticalScaleLowerTail`) |
| `ext-variance-scale` | the source theorem's explicit `VarianceScale` hypothesis, from Lawler–Limic's Green estimates at `sandpile.tex:1117-1240` | proved here (`Parking.External.varianceScale`) |
| `ext-multivariate-berry-esseen` | the source theorem's explicit `MultivariateBerryEsseen` hypothesis, Raič, Theorem 1.1, at `sandpile.tex:1770-1782` | assumed |
| `ext-oriented-stopping-stability` | the cutoff and stability estimates of the parabolic scaling limit in the companion paper, in the shape of Coquet-Toldo, Theorem 3 and Corollary 4 | assumed |
| `ext-green-gradient` | Lawler–Limic, Section 2.3, through the first-difference local central limit estimate and the Gaussian bound; the shared library proves the truncated bound uniformly in the horizon | proved here (`Parking.External.greenGradient`) |

`ext-variance-scale` and `ext-multivariate-berry-esseen` are the two antecedents of
`ext-critical-scale-lower-tail`, exactly as in the source theorem, which `Parking.ae_spatial_origin_pos`
and `thm-nearest` use.

`lem:u-concentration` is stated as a lemma in the paper and then discharged by
a citation ("Equation (57) follows from the general-kernel concentration
estimate"), so it is registered as a cited input (`ext-u-concentration`), which
is proved in this repository.

## How the Lean statements read the paper

The paper is `paper/parking.tex`, which is arXiv:2609.02820v1 with the
corrections listed in [`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md).
Each frozen statement states what the corresponding statement of that file
states, up to the notation below.

| paper | Lean formulation | reason |
|---|---|---|
| `eq:green-gradient` (`ext-green-gradient`) | only the gradient bound `|g_m(y) - g_m(z)| <= C(1+|y|)^{1-d}` is stated | the display's second relation, `Gamma_m(y) <= C(1+|y|)^{2-2d}`, follows from the first, and this development uses the node only through `Parking/Support/SpatGreenShift.lean` |
| `lem:one-particle`, `lem:tagged-monotonicity` | the process is the construction of `Parking/Support/Particle.lean`, in which each particle carries its own walk and its own uniform variables | this is the construction the two lemmas are stated for; `Parking.constructionsAgree'` proves that it has the same law as the stack construction |
| `lem:deferred` | the measurability clause is stated pathwise, as independence of the event from the one instruction it excludes, and for realizations whose instructions are neighbours of the site carrying them | that is what the proof establishes and what the second clause uses; the instructions are neighbours of their site almost surely |
| `lem:exposure` | conditional independence with the prescribed conditional law is the product rule over finite families of unread instructions | the proof checks the assertion on finite cylinders and extends it by the monotone class theorem |
| `lem:transport` | the last display uses the joint probabilities `P(η(0)=k, τ_1>t)` rather than conditional ones, and exchangeability is the invariance, on the event `{η(0)=k}`, of the joint law of the activity histories under permutations of the labels at the origin | the joint form is the same identity and never divides by a null probability |
| `lem:w-martingale` | the family is indexed from zero, so the paper's `ξ_i` is `ξ (i-1)` and `F_{i-1}` is `F i` | it removes a truncated subtraction |
| `prop:spatial-scaling` | `U` is identified with `contUc` on an exhibited Brownian space; its Green field is the L² extension of the exhibited white noise. "Converging locally uniformly" is the joint convergence of the finite-dimensional distributions, the vanishing in probability of the local uniform distance between the two rescaled odometers, and the equicontinuity in probability of the rescaled divisible odometer on compact sets of positive times | the Brownian value equality holds for every nonnegative horizon; the three convergence clauses together give convergence in distribution in the topology of local uniform convergence on `(0,∞)×ℝ^d`, as used by `thm:nearest` |
| `prop:oriented-scaling` | the limit is asserted to exist and to be measurable | the paper defines it in the proof |
| `prop:oriented-scaling`, Step 1 | the payoffs the Brownian value takes its supremum over are those of the stopping rules whose payoff is INTEGRABLE (`Parking.contPayoffs`) | Galmarino's criterion does not make a stopping rule measurable, so for a general rule the Bochner integral is the junk value zero, and a supremum over those zeros would exceed the value of the problem whenever every genuine payoff is negative.  For the paper's reward `-Z_T` the two readings agree, because the rule that stops at the horizon has payoff exactly zero (`Parking.contAttainable_eq_contPayoffs`) |
| `thm:nearest`, `thm:nearest-counterexample` | the distance from the origin to the nearest hole and to the nearest active particle is the graph distance `∑_i |x_i|` | `parking.tex:588-601` fixes distances on `Z^d` to be graph distances, and the proof of the counterexample uses the `l^1` identity `|w_i-a_i|=|w_i-y_i|+|a_i-y_i|` and `l^1` balls |
| `thm:subcritical`, `lem:product` | conditioning on the walk of the first particle is prescribing the moves of the label `(0,0)`, and the bound is asserted for every prescribed walk | the walk is independent of everything else, so this is the conditional probability |

## Cited inputs and formulation choices, node by node

- `prop-oriented-scaling`: Step 1 of the proof (`parking.tex:3207-3218`) rests
  on two results cited from outside the paper.  The node carries the first as
  an explicit hypothesis; the second is proved in this repository.

  The first is `Parking.External.OrientedStoppingStability`, the cutoff and
  stability estimates of the parabolic scaling limit.  It is the STABILITY
  statement itself and not the convergence it is used to prove: for a bounded
  continuous limit reward `G` and uniformly bounded rewards `G' n` converging
  to `G` uniformly, and GIVEN the finite-dimensional convergence of the
  rescaled oriented walk to the Brownian motion of `parking.tex:3190`, the
  discrete optimal-stopping values of the oriented walk converge to the
  Brownian optimal-stopping value.  The walk's convergence is a hypothesis
  rather than part of the cited input because without it the statement, read
  at `G' n = G`, would assert a full invariance principle for the stopped walk,
  which is one of the three inputs the paper lists as its own.  Nothing about
  the scenery, the white noise, or the joint law of the two is assumed.

  The second is `Parking.External.BinomialLocalCLT`, from the sentence "the
  binomial local central limit theorem gives convergence of the convolved
  potentials": there is a constant `C > 0` with
  `|sqrt m * binomLaw m ((j+m)/2) - 2 phi(j/sqrt m)| <= C/m` for every `m >= 1`
  and every integer `j` of the parity of `m`, where `binomLaw m k` is the chance
  of `k` heads in `m` fair tosses and `phi` is the standard normal density.  The
  error `C/m` is the one the argument consumes, because the convolved potentials
  sum the kernel error over the layers; the parity constraint is part of the
  statement, since without it the left-hand side vanishes at every second
  integer.  It is not an explicit hypothesis of `prop-oriented-scaling`
  or of `thm-oriented-walk`: both obtain it internally from
  `Parking.External.binomialLocalCLT` (`BinomialLocalCLTProved.lean`), which
  proves it from the shared library's binomial local CLT
  (`LatticeProb.BinomialLCLT.exists_binomPMF_localCLT`), bridging the index
  identity `binomLaw m ((j+m)/2) = binomPMF m j` and an elementary Gaussian
  tail estimate outside `|j| ≤ m`.

- `thm-nearest`: the proof at `parking.tex:1822-1848` applies
  `prop-spatial-scaling`, whose own cited inputs are the sandpile growth
  estimate, the Bernstein inequality, the parabolic scaling limit of the
  divisible odometer and two classical facts about the heat equation, and it
  opens with the sentence "the parabolic scaling limit and critical-scale
  lower-tail estimate of BP imply that `U(1,0) > 0` almost surely", whose
  remaining input is the multivariate Berry-Esseen comparison (the
  critical-scale lower tail estimate, with its own variance-scale input, is
  proved in the repository).  The node carries those six propositions,
  `SandpileGrowth`, `Bernstein`, `SpatialOdometerScaling`,
  `HeatInteriorRegularity`, `HeatCompactness` and `MultivariateBerryEsseen`,
  as explicit hypotheses and nothing more.

- `prop-everyone-settles`: the proof quotes `cor:growth` for the decay of
  `S_t`.  The collected Green estimates `eq:green-norms` and the
  concentration estimate `eq:u-concentration` are not explicit hypotheses of
  this or any node below: `ext-green-norms` and `ext-u-concentration` are
  each proved (`Parking.External.greenNorms`,
  `Parking/External/GreenNormsProved.lean`; `Parking.External.uConcentration`,
  `Parking/External/UConcentrationProved.lean`), so every node below obtains
  each internally.

- `lem-product`: `Parking.RelabelInvariant` is the pair of clauses the paper
  puts on `F` and on `Z` at `parking.tex:2336-2347`, "functions of the counts,
  walks, and uniform variables at these sites, each invariant under relabeling
  the particles at a site".  A site with count `k` carries the `k` particles
  labelled `0, …, k-1` and nothing else, so `Parking.SymmetricInParticles`
  quantifies over the permutations that move only the labels below the count at
  a site and fix every label the site does not carry, and
  `Parking.ReadsParticles` says that, with the counts held fixed, altering the
  walk or the uniform variables attached to a label that carries no particle
  does not change the value.  Step 2 at `parking.tex:2382-2409` reveals exactly
  the `k` particles of a site with count `k` and deletes one of them, which is
  what both clauses record.

  Invariance under EVERY permutation of the labels would be a strictly stronger
  hypothesis: the indicator that one of the `η(x)` particles at a site has a
  positive first increment is symmetric in the particles present, monotone
  under adding a particle and has the deletion bounds, yet is not invariant
  under exchanging the first particle with a label the site does not carry.

  The second clause is necessary.  Without it, take `d = 1`, one tilted site
  `0`, and the count law on `{-1, 0}` with equal masses, whose every tilt is
  again supported there.  Put `h(ω) = 1/2` when the uniform variable of the
  label `(0,0)` at its first step exceeds `1/2` and `h(ω) = 0` otherwise, and
  let `F` be `1` where the count at `0` is at least one and `h` elsewhere, and
  `Z = 1 - F`.  Then `F` is symmetric in the particles present, takes values in
  `[0,1]`, does not decrease when a particle is added, and `Z` is nonnegative,
  antitone and changes by at most one under an addition or a deletion.  The
  count at `0` is at most zero almost surely, so `F = h` almost surely and
  `Cov(F, Z) = -Var(h) = -1/16`, while `E_λ F = E h = 1/4` for every `λ`, so the
  derivative is `0` and the conclusion would read `1/16 ≤ 0`.  The observable
  `h` reads the uniform variable of a label that carries no particle, which a
  function of the particles at the site cannot do, and
  `Parking.ReadsParticles` is exactly that restriction.

  `Z` carries `Measurable Z`, as `F` does.  The paper's hypothesis is that `F`
  and `Z` are "functions of the counts, walks, and uniform variables at these
  sites", which is measurability in those variables together with
  `Parking.DependsOn N`.  Step 2 compares the value of `Z` at a configuration
  with one particle deleted, and the deleted configuration lives on a set the
  conditioned law can give measure zero, so no almost sure class of `Z`
  determines those values.

  The two relabeling clauses are asked for at the realizations whose uniform
  variables are pairwise distinct.  The ranks are independent uniforms on
  `[0,1]` (`parking.tex:632-644`), so two of them are equal on a null set; the
  model settles arrivals of equal rank in the order of their labels, and
  relabeling the particles at a site changes that order, so the observables of
  `thm:subcritical` are equivariant exactly off that null set.
  `Parking.RanksDistinct ω` is the pairwise distinctness of the uniform
  variables of `ω`; it is preserved by adding a particle, by deleting one and by
  relabeling, so the clauses are asked for on an invariant set of full measure.
  The proof uses the clauses only at realizations built from the original one by
  a relabeling, by a deletion or by splicing the noise of two independent
  copies; the first two preserve the distinctness pointwise, and a splice has
  the law of one copy, so it is distinct almost surely.  The comparison
  functional of a step carries the guard `Parking.deletedGuard`: off the set of
  distinct uniform variables it is the observable itself, so the two increment
  bounds of `Support/SpliceAvg.lean` hold at every realization, and its mean is
  the observable's because the guard is almost surely off.  The two observables
  of `thm:subcritical` carry no guard of their own: on the set of pairwise
  distinct uniform variables every tie in the tagged realization involves the
  tagged particle and exactly one other, and the label order is site-major, so
  such a tie is decided by the two sites, or at the origin by an index the
  relabeling does not move.  That is `Parking.TieInvariant`, the hypothesis of
  `Support/RelabelEquiv.lean`.

- `thm-near`: the uniform bound on the exponential moments carries the
  integrability that makes it a bound on a moment, and the same integrability
  makes the mean condition a condition on a genuine mean; `Parking.NearFamily`
  is that hypothesis block.  The lower bound is read off
  `prop:near-divisible`, which carries `thm:BP` and `lem:stopping-time` and reads
  `lem:u-concentration` and `eq:green-norms` internally; Step 3 of the upper bound
  reads the two Green rates of `eq:green-norms` again at the cutoff of
  `eq:near-cutoff`, and `eq:near-routing-mean` and `eq:near-routing-moment` apply
  `prop:w-moment`, whose own proof cites the Bernstein inequality.  The explicit
  hypotheses are `SandpileGrowth`, `Stopping` and `Bernstein`, bound before every
  parameter of the statement, exactly as for `prop-near-divisible`;
  `UConcentration` and `GreenNorms` are proved and obtained internally.
- `thm-oriented-walk`: Step 1 of the proof takes `r`-th moments in the directed
  pathwise comparison and inserts the directed form of `prop:w-moment`, whose
  own proof cites the Bernstein inequality, and Steps 2 to 4 read
  `eq:oriented-u-concentration`, obtained internally from
  `Parking.External.uConcentration`; the last part of the statement is read off
  `prop:oriented-scaling`, which carries the cutoff and stability estimates of
  the parabolic scaling limit.  The explicit hypotheses, `Bernstein` and
  `OrientedStoppingStability`, are bound before every parameter of the
  statement.
- Several nodes assert the integrability or summability that their proofs
  establish alongside the identity or the bound, so that an undefined integral
  or a divergent series cannot satisfy them through a junk value.
- `lem-parallel`: the identity is stated for realizations whose instructions
  are neighbours of the site carrying them, because the arrivals at `x` in a
  round come from the neighbours of `x`.  The instructions of the model are
  neighbours, since `ρ_j(y)` has the law `P(y,·)`, so the hypothesis is part of
  what "realization" means.
- `thm-nearest` and `thm-nearest-counterexample`: `holeDistance` and
  `activeDistance` measure the graph distance `Parking.graphNorm`, as
  `parking.tex:588-601` fixes it.  `Parking.supNorm` measures the range of a
  kernel.
- `thm-master` and `cor-growth` carry, beyond the sandpile growth estimate,
  only the martingale moment inequality (`ext-bernstein`) as an explicit
  hypothesis; `thm-trichotomy` also carries the optimal stopping
  representation, which its part (ii) reaches through `thm:four-sparse`.  The
  upper bound of `thm:master` IS the first display of `thm:upper`, which
  quotes the collected Green estimates and the concentration estimate, but
  `ext-green-norms` and `ext-u-concentration` are each proved
  (`Parking.External.greenNorms`, `Parking.External.uConcentration`) and
  obtained internally.  `cor:growth` inserts `thm:BP` into that
  bound, and parts (i) and (iii) of `thm:trichotomy` read the growth of the
  mean odometers off `cor:growth`.
- `prop-discrepancy`: its proof at `parking.tex:1586-1591` uses
  `eq:green-norms` in the logarithmic moment optimization, obtained internally
  from `Parking.External.greenNorms` rather than as an explicit hypothesis.
- `thm-nearest-counterexample` carries `ext-bernstein` through
  `lem-nearest-one-point` and `prop-nearest-two-hole`, used in its proof at
  `parking.tex:2215-2270`.  The probability sequence is bounded by one, which
  justifies its real `liminf`.
- `lem-critical-density`: the paper's `liminf_{t}tS_t\geq c` is stated as the
  eventual bound `\forall^f t, c\leq tS_t`.  In `\R` the `liminf` is the
  supremum of the set of eventual lower bounds, and `Real.sSup` of a set that is
  not bounded above is the junk value `0`; below dimension four `eq:activity`
  makes `tS_t` of order `t^{(4-d)/4}`, which tends to infinity, so a `liminf` in
  `\R` would read `c\leq0`.  The eventual bound is what the paper's Step 3
  proves, and it implies the paper's assertion wherever the `liminf` is not a
  junk value.  `thm-trichotomy` part (ii) keeps its real `liminf`: its
  preceding conjunct bounds the ratio above for each fixed law using the cited
  upper estimates.
- `thm-four-sparse`: the asymptotic lower bound is written as an eventual
  inequality, with a smaller universal constant, which its proof at
  `parking.tex:1641-1657` supplies directly.  The threshold may depend on the
  sparse-law parameter; the positive constant is bound before that parameter.
  The eventual formulation keeps precisely the cited inputs of the sparse-law
  proof.
- `thm-trichotomy`: the `L^r` clause of part (i) asserts the finiteness of the
  moment alongside its convergence to zero.
- `prop-near-divisible`: Step 1 of the proof applies `lem:mean-horizon`, whose
  own Step 1 cites `eq:green-norms` at `parking.tex:2805`, and Step 3 repeats
  that step at a bounded reference law, where the two Green rates are read
  again.  `Parking.External.GreenNorms` is proved and obtained internally
  here, not carried as an explicit hypothesis, exactly as for
  `lem-mean-horizon`.
- `lem-mean-horizon`: Step 1 of the proof cites `eq:green-norms` at
  `parking.tex:2805` to read the concentration term
  `\sqrt r\|g_m\|_2+r\max_xg_m(x)` as a multiple of the scale `\phi_d(m)`,
  obtained internally from `Parking.External.greenNorms` rather than as an
  explicit hypothesis.
- `ext-stopping` and `lem-mean-horizon`: the supremum of `eq:stopping` and the
  stopping rule of `lem:mean-horizon` are stated in the shared library's
  vocabulary, `LatticeProb.IsWalkStopping` on trajectories against
  `LatticeProb.siteWalkLaw`.  A stopping time of the walk is a function of the
  trajectory whose value at `k` is settled by the positions up to time `k`,
  which is what the paper's "stopping times for the natural filtration of `X`"
  means, and it is the form in which the library proves the representation.
- `thm-subcritical-tail`: the Donsker-Varadhan estimate for the range, which
  the paper cites at `parking.tex:117-121` and uses at `parking.tex:2514-2517`
  to turn the two bounds in `|R_t|` into the two bounds in `t`, is the explicit
  hypothesis `Parking.External.DonskerVaradhanRange`.
- `lem-near-tilt`: the proof does not use two of the hypotheses the family
  `Parking.NearFamily` carries, the nonconstancy of the law at `\delta = 0` and
  the coupling of expected absolute difference `K\delta`.  The paper's Step 1
  (`parking.tex:2610-2626`) proves `\lambda_\delta\asymp\delta` in both
  directions, and the upper bound on `S_t^\delta` needs only the direction
  `\lambda_\delta\gtrsim\delta`, which comes from an upper bound on
  `\psi_\delta''` alone; the reverse direction is what the nonconstancy and the
  coupling supply, and it is what the rest of Section 11 uses.
- `lem-gamma-sum`: the gradient bound `eq:green-gradient` in dimension two and
  above is an explicit hypothesis, as `Parking.External.GreenGradient d` under
  `2 ≤ d`.  The paper proves that bound by citing Lawler–Limic, so it is an
  external input; in dimension one the proof of the lemma computes the gradient
  exactly and nothing is assumed there.
- `lem-transport`: the exchangeability clause restricts both laws to the event
  `{η(0)=k}` that the paper conditions on, and records the activity histories
  alone.  On the complement a permutation of the labels `(0,0), …, (0,k-1)` can
  move an index below `η(0)` to an index above it, and the two laws differ
  there.
- `lem-exposure`: the measurability of `U_{k+1}` for the exposure filtration is
  asserted almost surely, as the existence of a `\mathcal G_k`-measurable field
  that `U_{k+1}` agrees with off a null set.  For a realization whose
  instructions are not neighbours of the site carrying them, a particle can
  stand at a site it is not a candidate for, where it reads the instruction of
  index exactly `U_{k+1}` of that site, which no generator of the filtration
  records.  Such realizations are null, and the almost-sure form is what the
  proof of `lem:w-martingale` uses.
- `prop-everyone-settles`: "settles after finitely many rounds" is a time past
  which the property holds at every later round, and "infinitely many distinct
  particles leave every site" says the particle stands elsewhere after the next
  round.
- `prop-spatial-scaling` and `thm-nearest`: Step 1 of the proof of
  `prop:spatial-scaling` (`parking.tex:1755-1759`) cites "the argument proving
  the parabolic scaling limit in [BP], with the time variable and scenery
  retained" for the joint convergence `(\eta_R,\overline u_R)`, together with a
  union bound transferring it to `\overline U_R`; this is BP's own Theorem
  1.3(i)(b) (`sandpile.tex:206-235`).  So the node carries
  `Parking.External.SpatialOdometerScaling` as an explicit hypothesis: it
  exhibits the noise `W`, the auxiliary field `Z`, and the continuum value `Uc`
  together with BP's own sup representation of it, the finite-dimensional
  convergence of `(scenePair,barDivisible)` to `(W,Uc)`, jointly, with the
  scenery retained, and the JOINT space-time equicontinuity clause, which is the
  `C_loc` conclusion of BP's theorem read at every horizon simultaneously, as
  `parking.tex:1760-1762`'s "estimates uniform on compact time intervals"
  licenses.  `thm-nearest`'s own proof runs through `prop:spatial-scaling`, so it
  carries the same hypothesis.  The node identifies the limit as the Brownian
  optimal-stopping value of the exhibited noise; `ext-spatial-odometer-scaling`
  specifies the Green field through the continuous linear L² extension of the
  test-function noise, with the variance-scaled isometry.
- `prop-spatial-scaling` and `thm-nearest` carry the two classical parabolic
  inputs `HeatInteriorRegularity` and `HeatCompactness`.  Steps 3–4 of
  `parking.tex:1800-1820` also use backward propagation of a zero minimum,
  the strong minimum principle `HeatStrongMinimum`; it is proved in the
  repository (`Parking.External.heatStrongMinimum`, from Nirenberg 1953,
  Theorem 1) rather than carried as a hypothesis.  Steps 3–4 use interior
  regularity and compactness of nonnegative caloric functions with bounded
  local integrals.  The local integral bound for the time quotients is
  proved by telescoping; the compactness input supplies a smooth classical
  subsequential limit.

### The two constructions, and where the equality of their laws is used

`parking.tex:645-646` states that the stack construction of Section 3 and the
construction in which every particle carries its own walk and its own uniform
variables have the same law.  It is `Parking.constructionsAgree'` (and
`Parking.constructionsAgree` in the shared library's vocabulary), proved in
`Parking/Support/Agree.lean`, and the form the proofs use is
`Parking.constructionsAgree_conf`, which records the configuration beside the
odometer, the activity, the hole counts and the activity field, and holds for
an arbitrary law of configurations.  Two sealed nodes rest on it:
`lem-density-compare`, whose lower bound has no pathwise form in the stack
construction, and `lem-transport`, whose exchangeability clause is a
relabelling of two independent families in the particle-driven construction
and has no pathwise form in the stack construction.  The proofs of both lemmas
in `paper/parking.tex` pass through this equality of laws.

### `lem:range-lower`, and where the two constructions meet again

The lemma is proved in the particle-driven construction, where "a particle
never settles where the configuration is nonnegative" is pathwise, and carried
back to the stack construction, where `S_t` and the conditional survival
probability are defined, by `Parking.map_conf_active_agree`: the configuration
and the activity field have the same joint law in the two constructions.  That
is `Parking.constructionsAgree_conf` read through the projection onto the first
and the fourth observables, and it is the form suited to the nodes of
Section 10, because they all condition on the configuration at the origin.

### The low-dimensional nearest comparison

The proof of `thm:nearest` (`parking.tex:1822-1848`) uses
`prop:spatial-scaling` and the cited critical-scale lower-tail estimate.
The one-point, two-hole and close-pair estimates in dimension at least five
are inputs of `thm:nearest-counterexample` only.

`Parking.nearest_of_positive_test_events` proves the discrete geometric and
probability endgame with the positive-event estimate as an explicit hypothesis.
`Parking.PositiveTestEvent R r φ` requires a positive particle odometer on the
lattice ball of radius `rR` and a positive signed pairing with a nonnegative
function supported in the corresponding rescaled ball. A departure exhausts
the holes at its site; a positive signed sum has an active site in the support
of its weights. Thus this event excludes a closer hole, and arbitrarily high
probability of the event gives the claimed limit. The substitution `R = √t`
recovers every integer horizon exactly.

The critical lower-tail input is transcribed in the source mass normalization:
`Parking.CriticalScale.centeredMassLaw d ν` is the independent law of
`σ = 1 + 2dη`, and its odometer uses `max 0 ((σ-1+nbrSum u)/(2d))`.
`Parking.CriticalScale.odometer_centered` proves that this odometer equals
`Parking.u η` exactly. The threshold has no extra factor of `2d`.
`odometer_lowerTail_eq` and `uOf_lowerTail_eq` prove the corresponding event-law
identities. The critical lower-tail estimate is proved here
(`Parking.External.criticalScaleLowerTail`) from the source theorem's two cited
hypotheses, which are retained as the separately registered inputs
`VarianceScale` (proved here) and `MultivariateBerryEsseen` (assumed).

`Parking.ae_spatial_origin_pos` proves almost-sure strict positivity of the
limiting odometer at `(1, 0)` from the critical lower tail, its two retained
source hypotheses, and the exact finite-dimensional clause of the frozen
spatial proposition. First the logarithmic remainder vanishes at each fixed
threshold `L`; then `L` is chosen large. The open-set inequality in Portmanteau
excludes all mass on `(-∞,0]`, without a continuity-of-distribution assumption
at zero. `Parking.ae_exists_pos_l1_ball` then uses the proposition's continuity
clause to give an almost-sure positive continuum ball.

`Parking.nearest_of_spatial_scaling` transfers the positive continuum ball
and joint signed-pair limit to the discrete positive-event estimate. It uses
the spatial proposition's joint convergence, local uniform closeness of the
two odometers, and joint space-time equicontinuity. The geometric endgame
then proves `thm:nearest`. Both the spatial proposition and the nearest
comparison are sealed under their registered external hypotheses.

## Main results

The main results are additionally exposed, stated in full, in
[`Parking/MainTheorems.lean`](Parking/MainTheorems.lean), each proved by `exact` of its
certified statement, and all eight are restated over a Mathlib-only vocabulary for the
comparator (see [`ParkingAudit/`](ParkingAudit/)).  The certified statements of `thm-trichotomy` and
`thm-near` carry `ext-stopping` as a hypothesis; it is proved (`Parking.External.stopping`), so
the two main theorems discharge it.

| Source | Main theorem | Certified statement | Comparator |
|---|---|---|---|
| Theorem 1.1, `thm:subcritical-tail` | `Parking.subcritical_tail` | `Parking.Frozen.subcritical_tail` | `ParkingAudit/SubcriticalTail/` |
| Theorem 1.2, `thm:master` | `Parking.master` | `Parking.Frozen.master` | `ParkingAudit/Master/` |
| Corollary 1.3, `cor:growth` | `Parking.growth` | `Parking.Frozen.growth` | `ParkingAudit/Growth/` |
| Theorem 1.4, `thm:trichotomy` | `Parking.trichotomy` | `Parking.Frozen.trichotomy` | `ParkingAudit/Trichotomy/` |
| Theorem 1.5, `thm:nearest` | `Parking.nearest` | `Parking.Frozen.nearest` | `ParkingAudit/Nearest/` |
| Theorem 1.6, `thm:nearest-counterexample` | `Parking.nearest_counterexample` | `Parking.Frozen.nearest_counterexample` | `ParkingAudit/NearestCounterexample/` |
| Theorem 1.7, `thm:near` | `Parking.near` | `Parking.Frozen.near` | `ParkingAudit/Near/` |
| Theorem 1.8, `thm:oriented-walk` | `Parking.oriented_walk` | `Parking.Frozen.oriented_walk` | `ParkingAudit/OrientedWalk/` |

## Frozen surface

<!-- FROZEN-SURFACE-BEGIN (generated by tools/sync_docs.py) -->

| id | Lean | paper | state |
|---|---|---|---|
| `ext-bernstein` | `Parking.External.Bernstein` | `parking.tex:1175-1188`, `lem:bernstein` | FROZEN |
| `lem-tagged-monotonicity` | `Parking.Frozen.tagged_monotonicity` | `parking.tex:714-719`, `lem:tagged-monotonicity` | PROVED |
| `lem-parallel` | `Parking.Frozen.parallel` | `parking.tex:647-653`, `lem:parallel` | PROVED |
| `lem-one-particle` | `Parking.Frozen.one_particle` | `parking.tex:682-692`, `lem:one-particle` | PROVED |
| `lem-pathwise-comparison` | `Parking.Frozen.pathwise_comparison` | `parking.tex:976-985`, `lem:pathwise-comparison` | PROVED |
| `ext-stopping` | `Parking.External.Stopping` | `parking.tex:876-884`, `lem:stopping` | SEALED |
| `lem-deferred` | `Parking.Frozen.deferred` | `parking.tex:659-667`, `lem:deferred` | PROVED |
| `thm-comparison` | `Parking.Frozen.comparison` | `parking.tex:889-895`, `thm:comparison` | PROVED |
| `lem-activity-holes` | `Parking.Frozen.activity_holes` | `parking.tex:776-782`, `lem:activity-holes` | PROVED |
| `lem-shift` | `Parking.Frozen.shift` | `parking.tex:3047-3052`, `lem:shift` | PROVED |
| `lem-nearest-close-pair` | `Parking.Frozen.nearest_close_pair` | `parking.tex:2199-2204`, `lem:nearest-close-pair` | PROVED |
| `lem-gamma-sum` | `Parking.Frozen.gamma_sum` | `parking.tex:1057-1062`, `lem:gamma-sum` | PROVED |
| `ext-green-gradient` | `Parking.External.GreenGradient` | `parking.tex:1030-1034`, `eq:green-gradient` | SEALED |
| `lem-exposure` | `Parking.Frozen.exposure` | `parking.tex:1107-1115`, `lem:exposure` | PROVED |
| `lem-density-compare` | `Parking.Frozen.density_compare` | `parking.tex:811-821`, `lem:density-compare` | PROVED |
| `lem-transport` | `Parking.Frozen.transport` | `parking.tex:741-753`, `lem:transport` | PROVED |
| `lem-range-lower` | `Parking.Frozen.range_lower` | `parking.tex:2295-2303`, `lem:range-lower` | PROVED |
| `lem-w-martingale` | `Parking.Frozen.w_martingale` | `parking.tex:1135-1148`, `lem:w-martingale` | PROVED |
| `lem-critical-density` | `Parking.Frozen.critical_density` | `parking.tex:1255-1263`, `lem:critical-density` | PROVED |
| `cor-critical` | `Parking.Frozen.cor_critical` | `parking.tex:1354-1361`, `cor:critical` | PROVED |
| `thm-four-sparse` | `Parking.Frozen.four_sparse` | `parking.tex:1601-1610`, `thm:four-sparse` | PROVED |
| `lem-nearest-one-point` | `Parking.Frozen.nearest_one_point` | `parking.tex:1882-1891`, `lem:nearest-one-point` | PROVED |
| `prop-nearest-two-hole` | `Parking.Frozen.nearest_two_hole` | `parking.tex:2025-2032`, `prop:nearest-two-hole` | PROVED |
| `thm-nearest-counterexample` | `Parking.Frozen.nearest_counterexample` | `parking.tex:289-302`, `thm:nearest-counterexample` | PROVED |
| `ext-donsker-varadhan` | `Parking.External.DonskerVaradhanRange` | parking.tex:117-121 (Theorem 1 of Donsker-Varadhan 1979, cited for eq:sharpness and used at parking.tex:2514-2517) | FROZEN |
| `prop-resolvent` | `Parking.Frozen.resolvent` | `parking.tex:2643-2663`, `prop:resolvent` | PROVED |
| `ext-oriented-stopping-stability` | `Parking.External.OrientedStoppingStability` | parking.tex:3214-3218 (the cutoff and stability estimates of the parabolic scaling limit, cited in the proof of prop:oriented-scaling) | FROZEN |
| `lem-product` | `Parking.Frozen.product` | `parking.tex:2336-2347`, `lem:product` | PROVED |
| `thm-subcritical` | `Parking.Frozen.subcritical` | `parking.tex:2434-2447`, `thm:subcritical` | PROVED |
| `thm-subcritical-tail` | `Parking.Frozen.subcritical_tail` | `parking.tex:123-135`, `thm:subcritical-tail` | PROVED |
| `lem-near-tilt` | `Parking.Frozen.near_tilt` | `parking.tex:2599-2604`, `lem:near-tilt` | PROVED |
| `ext-variance-scale` | `Parking.External.varianceScale` | parking.tex:1822-1848 (critical_toppling input, sandpile.tex:1117-1240); proved from the shared library Lattice-Probability (LatticeProb.Walk.VarianceScale, LatticeProb.Walk.Correlation, LatticeProb.Walk.WindowD4) | PROVED |
| `ext-multivariate-berry-esseen` | `Parking.External.MultivariateBerryEsseen` | parking.tex:1822-1848 (critical_toppling input, sandpile.tex:1770-1782, quoted from Raic Theorem 1.1) | FROZEN |
| `ext-spatial-fixed-time-tightness` | `Parking.External.SpatialFixedTimeTightness` | parking.tex:1756-1767 (prop:spatial-scaling, quoted from BP Theorem 1.3(i)(b)) | FROZEN |
| `ext-spatial-stopping-stability` | `Parking.External.SpatialStoppingStability` | parking.tex:1756-1767 (the cutoff and stability estimates of the parabolic scaling limit, cited in the proof of prop:spatial-scaling) | FROZEN |
| `thm-oriented` | `Parking.Frozen.oriented` | `parking.tex:3072-3085`, `thm:oriented` | PROVED |
| `prop-w-moment` | `Parking.Frozen.w_moment` | `parking.tex:1202-1215`, `prop:w-moment` | PROVED |
| `ext-heat-compactness` | `Parking.External.HeatCompactness` | parking.tex:1800-1820 (prop:spatial-scaling, Step 3, classical parabolic compactness) | FROZEN |
| `ext-spatial-odometer-scaling` | `Parking.External.SpatialOdometerScaling` | parking.tex:1756-1767 (prop:spatial-scaling, quoted from BP Theorem 1.3(i)(b), sandpile.tex:206-235) | FROZEN |
| `ext-linear-field-scaling` | `Parking.External.LinearFieldScaling` | parking.tex:1756-1767 (prop:spatial-scaling, BP Proposition 4.3, page 27) | FROZEN |
| `ext-heat-interior-regularity` | `Parking.External.HeatInteriorRegularity` | parking.tex:1800-1820 (prop:spatial-scaling, Step 3, hypoelliptic interior regularity) | FROZEN |
| `ext-sandpile-growth` | `Parking.External.SandpileGrowth` | `parking.tex:929-943`, `thm:BP` | FROZEN |
| `ext-sandpile-growth-proved` | `Parking.External.sandpileGrowth` | `parking.tex:929-943`, `thm:BP` | PROVED |
| `ext-binomial-local-clt` | `Parking.External.binomialLocalCLT` | parking.tex:3207-3218 (proved from LatticeProb.BinomialLCLT.exists_binomPMF_localCLT) | PROVED |
| `prop-oriented-scaling` | `Parking.Frozen.oriented_scaling` | `parking.tex:3166-3174`, `prop:oriented-scaling` | PROVED |
| `ext-green-norms` | `Parking.External.greenNorms` | `parking.tex:1383-1400`, `eq:green-norms` | PROVED |
| `ext-critical-scale-lower-tail` | `Parking.External.criticalScaleLowerTail` | parking.tex:1822-1848 (the critical-scale lower tail estimate of Bou-Rabee-Panagiotis, sandpile.tex:1696-1720); proved outright from the statement's own VarianceScale and MultivariateBerryEsseen hypotheses | PROVED |
| `ext-srw-local-clt` | `Parking.External.srwLocalCLT` | parking.tex:1756-1767 (prop:spatial-scaling, quoted from BP eq. (25), citing Lawler-Limic Thm 2.1.3 Eq. (2.8)); proved from the local central limit theorem of the divisible sandpile formalization, Sandpile.External.localCLT, via the heat-kernel identification | PROVED |
| `ext-u-concentration` | `Parking.External.uConcentration` | `parking.tex:1402-1413`, `lem:u-concentration` | PROVED |
| `ext-heat-strong-minimum` | `Parking.External.heatStrongMinimum` | parking.tex:1800-1820 (prop:spatial-scaling, Step 4, strong minimum principle); proved from the shared library strong minimum principle of Nirenberg 1953 Theorem 1 | PROVED |
| `thm-master` | `Parking.Frozen.master` | `parking.tex:159-168`, `thm:master` | PROVED |
| `cor-growth` | `Parking.Frozen.growth` | `parking.tex:174-188`, `cor:growth` | PROVED |
| `prop-discrepancy` | `Parking.Frozen.discrepancy` | `parking.tex:1566-1583`, `prop:discrepancy` | PROVED |
| `thm-trichotomy` | `Parking.Frozen.trichotomy` | `parking.tex:207-238`, `thm:trichotomy` | PROVED |
| `prop-everyone-settles` | `Parking.Frozen.everyone_settles` | `parking.tex:1501-1509`, `prop:everyone-settles` | PROVED |
| `lem-mean-horizon` | `Parking.Frozen.mean_horizon` | `parking.tex:2779-2785`, `lem:mean-horizon` | PROVED |
| `prop-near-divisible` | `Parking.Frozen.near_divisible` | `parking.tex:2844-2860`, `prop:near-divisible` | PROVED |
| `thm-near` | `Parking.Frozen.near` | `parking.tex:314-335`, `thm:near` | PROVED |
| `thm-upper` | `Parking.Frozen.upper` | `parking.tex:1418-1431`, `thm:upper` | PROVED |
| `thm-oriented-walk` | `Parking.Frozen.oriented_walk` | `parking.tex:363-380`, `thm:oriented-walk` | PROVED |
| `prop-spatial-scaling` | `Parking.Frozen.spatial_scaling` | `parking.tex:1694-1752`, `prop:spatial-scaling` | PROVED |
| `thm-nearest` | `Parking.Frozen.nearest` | `parking.tex:266-275`, `thm:nearest` | PROVED |

<!-- FROZEN-SURFACE-END -->
