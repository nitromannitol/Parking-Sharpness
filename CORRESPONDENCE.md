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

Every cited result the paper uses without proof is a `Prop` in
`Parking/External/`, frozen and pinned like a statement, and enters only as an
explicit hypothesis of the nodes whose proofs use it.

| node | cited result | used by |
|---|---|---|
| `ext-sandpile-growth` | Bou-Rabee–Panagiotis, Theorem 1.3, Corollary 6.2, Theorem 6.6 and (94) | `thm-upper`, `thm-master`, `cor-growth`, `thm-trichotomy`, `thm-four-sparse`, `prop-near-divisible`, `thm-near` |
| `ext-stopping` | Bou-Rabee–Panagiotis–Rossignol–Sun, Theorem 3.2 | `thm-four-sparse`, `lem-mean-horizon`, `prop-near-divisible`, `thm-oriented`, `thm-near` |
| `ext-bernstein` | Pinelis, Theorems 4.1 and 3.3 | `prop-w-moment`, `thm-upper`, `lem-nearest-one-point`, `prop-nearest-two-hole`, `thm-nearest-counterexample`, `thm-near` |
| `ext-u-concentration` | Bou-Rabee–Panagiotis, Remark 3.4 | `thm-upper`, `prop-discrepancy`, `lem-mean-horizon`, `thm-near` |
| `ext-green-norms` | Bou-Rabee–Panagiotis, Section 3.1, the collected Green estimates | `thm-upper`, `thm-master`, `cor-growth`, `thm-trichotomy`, `prop-discrepancy`, `prop-everyone-settles`, `thm-near` |
| `ext-critical-scale-lower-tail` | Bou-Rabee–Panagiotis, the critical-scale lower tail estimate; `sandpile.tex:1696-1720`, cited at `parking.tex:1807-1833` | `Parking.ae_spatial_origin_pos`; `thm-nearest` |
| `ext-variance-scale` | the source theorem's explicit `VarianceScale` hypothesis, from Lawler–Limic's Green estimates at `sandpile.tex:1117-1240` | `ext-critical-scale-lower-tail` antecedent |
| `ext-multivariate-berry-esseen` | the source theorem's explicit `MultivariateBerryEsseen` hypothesis, Raič, Theorem 1.1, at `sandpile.tex:1770-1782` | `ext-critical-scale-lower-tail` antecedent |
| `ext-oriented-stopping-stability` | the cutoff and stability estimates of the parabolic scaling limit in the companion paper, in the shape of Coquet-Toldo, Theorem 3 and Corollary 4 | `prop-oriented-scaling` |
| `ext-green-gradient` | Lawler–Limic, Section 2.3, through the first-difference local central limit estimate and the Gaussian bound; discharged, the shared library proves the truncated bound uniformly in the horizon | `lem-gamma-sum` |

`lem:u-concentration` is stated as a lemma in the paper and then discharged by
a citation ("Equation (57) follows from the general-kernel concentration
estimate"), so it is an external input here rather than a proof obligation.

## Where a Lean statement is not literally the paper's

| paper | how the Lean statement differs | why |
|---|---|---|
| `eq:green-gradient` (`ext-green-gradient`) | only the gradient bound `|g_m(y) - g_m(z)| <= C(1+|y|)^{1-d}` is stated | the display's second relation, `Gamma_m(y) <= C(1+|y|)^{2-2d}`, is introduced by "hence" as a consequence of the first and is not consumed anywhere in this development, which uses the node only through `Parking/Support/SpatGreenShift.lean` |
| `lem:one-particle`, `lem:tagged-monotonicity` | the process is the particle-driven construction of `Parking/Support/Particle.lean`, not the stack construction | the paper's coupling gives "every particle they share the same walk and the same uniform variables", which the stack construction cannot express: adding a particle at a site shifts which instruction every later departure from that site reads |
| `lem:deferred` | the measurability clause is stated pathwise, as independence of the event from the one instruction it excludes, and for realizations whose instructions are neighbours of the site carrying them | that is what the proof establishes and what the second clause uses; without the neighbour hypothesis a particle can stand at a site it is not a candidate for and read an instruction of an index the round does not count |
| `lem:exposure` | conditional independence with the prescribed conditional law is the product rule over finite families of unread instructions | the paper's own proof says the assertion is checked on finite cylinders and extended by the monotone class theorem |
| `lem:transport` | the last display uses the joint probabilities `P(η(0)=k, τ_1>t)` rather than conditional ones, and exchangeability is the invariance, on the event `{η(0)=k}`, of the joint law of the activity histories under permutations of the labels at the origin | the joint form is the same identity and never divides by a null probability |
| `lem:w-martingale` | the family is indexed from zero, so the paper's `ξ_i` is `ξ (i-1)` and `F_{i-1}` is `F i` | it removes a truncated subtraction without changing the statement |
| `prop:spatial-scaling` | `U` is identified with `contUc` on an exhibited Brownian space; its Green field is the L² extension of the exhibited white noise. "Converging locally uniformly" is the joint convergence of the finite-dimensional distributions, the vanishing in probability of the local uniform distance between the two rescaled odometers, and the equicontinuity in probability of the rescaled divisible odometer on compact sets of positive times | the Brownian value equality holds for every nonnegative horizon; the three convergence clauses together give convergence in distribution in the topology of local uniform convergence on `(0,∞)×ℝ^d`, as used by `thm:nearest` |
| `prop:oriented-scaling` | the limit is asserted to exist and to be measurable rather than characterized | the paper defines it in the proof, not in the statement |
| `prop:oriented-scaling`, Step 1 | the payoffs the Brownian value takes its supremum over are those of the stopping rules whose payoff is INTEGRABLE (`Parking.contPayoffs`) | Galmarino's criterion does not make a stopping rule measurable, so for a general rule the Bochner integral is the junk value zero, and a supremum over those zeros would exceed the value of the problem whenever every genuine payoff is negative.  For the paper's own reward `-Z_T` the two readings agree, because the rule that stops at the horizon has payoff exactly zero (`Parking.contAttainable_eq_contPayoffs`) |
| `thm:nearest`, `thm:nearest-counterexample` | the distance from the origin to the nearest hole and to the nearest active particle is the graph distance `∑_i |x_i|`, not the sup norm | `parking.tex:588-601` fixes distances on `Z^d` to be graph distances, and the proof of the counterexample uses the `l^1` identity `|w_i-a_i|=|w_i-y_i|+|a_i-y_i|` and `l^1` balls |
| `thm:subcritical`, `lem:product` | conditioning on the walk of the first particle is prescribing the moves of the label `(0,0)`, and the bound is asserted for every prescribed walk | the walk is independent of everything else, so this is the conditional probability |

## Statement repairs

- `prop-oriented-scaling` (version 3): Step 1 of the paper's proof
  (`parking.tex:3192-3203`) rests on a result cited from outside the paper,
  the cutoff and stability estimates of the parabolic scaling limit, so the
  node carries `Parking.External.OrientedStoppingStability` as an explicit
  hypothesis and nothing more.  The conclusion is unchanged.

  The External is the STABILITY statement itself and not the convergence it is
  used to prove: for a bounded continuous limit reward `G` and uniformly
  bounded rewards `G' n` converging to `G` uniformly, and GIVEN the
  finite-dimensional convergence of the rescaled oriented walk to the Brownian
  motion of `parking.tex:3175`, the discrete optimal-stopping values of the
  oriented walk converge to the Brownian optimal-stopping value.  The walk's
  convergence is a hypothesis rather than part of the cited input because
  without it the statement, read at `G' n = G`, would assert a full invariance
  principle for the stopped walk, which is one of the three inputs the paper
  lists as its own.  Nothing about the scenery, the white noise, or the joint
  law of the two is assumed.

  Version 4 attaches a second cited input to the same node.  The same paragraph
  of the proof says "the binomial local central limit theorem gives convergence
  of the convolved potentials", so the node also carries
  `Parking.External.BinomialLocalCLT`: there is a constant `C > 0` with
  `|sqrt m * binomLaw m ((j+m)/2) - 2 phi(j/sqrt m)| <= C/m` for every `m >= 1`
  and every integer `j` of the parity of `m`, where `binomLaw m k` is the chance
  of `k` heads in `m` fair tosses and `phi` is the standard normal density.  The
  error `C/m` is the one the argument consumes, because the convolved potentials
  sum the kernel error over the layers; the parity constraint is part of the
  statement, since without it the left-hand side vanishes at every second
  integer.  `thm-oriented-walk` (version 3) carries it too, because its proof
  applies this node.

- `thm-nearest` (version 3): the proof at `parking.tex:1807-1833` applies
  `prop-spatial-scaling`, whose own cited inputs are the sandpile growth
  estimate, the Bernstein inequality and the odometer concentration estimate,
  and it opens with the sentence "the parabolic scaling limit and critical-scale
  lower-tail estimate of BP imply that `U(1,0) > 0` almost surely", whose inputs
  are the critical-scale lower tail with its variance-scale and multivariate
  Berry-Esseen hypotheses.  The node carries those six propositions as
  explicit hypotheses and nothing more.  The conclusion is unchanged.


- `prop-everyone-settles` (version 3): the collected Green estimates
  `eq:green-norms` are an explicit hypothesis, as
  `Parking.External.GreenNorms`.  The proof of the proposition quotes
  `cor:growth` for the decay of `S_t`, and the proof of `cor:growth` uses those
  estimates, so the node carries the input its own citation chain uses, exactly
  as `thm-trichotomy` and `cor-growth` do.  Nothing else changed.

- `lem-product` (version 3): `Parking.RelabelInvariant` is now the pair of
  clauses the paper puts on `F` and on `Z` at `parking.tex:2321-2332`,
  "functions of the counts, walks, and uniform variables at these sites, each
  invariant under relabeling the particles at a site".  A site with count `k`
  carries the `k` particles labelled `0, …, k-1` and nothing else, so
  `Parking.SymmetricInParticles` quantifies over the permutations that move only
  the labels below the count at a site and fix every label the site does not
  carry, and `Parking.ReadsParticles` says that, with the counts held fixed,
  altering the walk or the uniform variables attached to a label that carries no
  particle does not change the value.  Step 2 at `parking.tex:2367-2394` reveals
  exactly the `k` particles of a site with count `k` and deletes one of them,
  which is what both clauses record.

  The first clause replaces a quantification over EVERY permutation of the
  labels, which is a strictly stronger hypothesis than the paper's: the
  indicator that one of the `η(x)` particles at a site has a positive first
  increment is symmetric in the particles present, monotone under adding a
  particle and has the deletion bounds, yet is not invariant under exchanging
  the first particle with a label the site does not carry.

  The second clause is what makes the lemma true.  Without it, take `d = 1`, one
  tilted site `0`, and the count law on `{-1, 0}` with equal masses, whose every
  tilt is again supported there.  Put `h(ω) = 1/2` when the uniform variable of
  the label `(0,0)` at its first step exceeds `1/2` and `h(ω) = 0` otherwise,
  and let `F` be `1` where the count at `0` is at least one and `h` elsewhere,
  and `Z = 1 - F`.  Then `F` is symmetric in the particles present (at a count
  at most zero the condition forces the identity permutation, and at a positive
  count the value is `1` before and after), takes values in `[0,1]`, does not
  decrease when a particle is added, and `Z` is nonnegative, antitone and
  changes by at most one under an addition or a deletion.  The count at `0` is
  at most zero almost surely, so `F = h` almost surely and
  `Cov(F, Z) = -Var(h) = -1/16`, while `E_λ F = E h = 1/4` for every `λ`, since
  `h` reads a uniform variable and not a count, so the derivative is `0` and the
  conclusion would read `1/16 ≤ 0`.  The observable `h` reads the uniform
  variable of a label that carries no particle, which the paper's `F` cannot do,
  and `Parking.ReadsParticles` is exactly that restriction.  The frozen block is
  unchanged; the definition it names is what changed.

- `lem-product` (version 4): `Z` now carries `Measurable Z`, the clause `F`
  already carried.  The paper's hypothesis is that `F` and `Z` are "functions of
  the counts, walks, and uniform variables at these sites"
  (`parking.tex:2321-2332`), which is measurability in those variables together
  with `Parking.DependsOn N`; without it the conclusion is not a bound on the
  covariance of two random variables.  It is also what the proof needs and what
  integrability alone cannot give: Step 2 at `parking.tex:2367-2394` compares the
  value of `Z` at a configuration with one particle deleted, and the deleted
  configuration lives on a set the conditioned law can give measure zero, so no
  almost sure class of `Z` determines those values.  Only the regularity clause
  was added; every quantifier, bound and conclusion is unchanged.

- `lem-product` (version 5): the two relabeling clauses are asked for at the
  realizations whose uniform variables are pairwise distinct, and not at every
  realization.  The paper's ranks are independent uniforms on `[0,1]`
  (`parking.tex:632-644`), so two of them are equal on a null set; the model
  settles arrivals of equal rank in the order of their labels, and relabeling
  the particles at a site changes that order, so the raw observables of
  `thm:subcritical` (the indicator that a tagged particle has not settled, the
  number of unfilled holes of a set) are equivariant exactly off that null set.
  `Parking.RanksDistinct ω` is the pairwise distinctness of the uniform
  variables of `ω`; it is preserved by adding a particle, by deleting one and by
  relabeling, so the weakened clauses are asked for on an invariant set of full
  measure.  This transcribes a statement that fails only on a null set in its
  almost sure form, and it makes the hypotheses weaker, hence the lemma
  stronger.  The proof uses the clauses only at realizations built from
  the original one by a relabeling, by a deletion or by splicing the noise of two
  independent copies; the first two preserve the distinctness pointwise, and a
  splice has the law of one copy, so it is distinct almost surely, which is all
  the proof needs since every use sits inside an integral.  The comparison
  functional of a step carries the guard (`Parking.deletedGuard`): off the set of
  distinct uniform variables it is the observable itself, so the two increment
  bounds of `Support/SpliceAvg.lean` hold at every realization, and its mean is
  unchanged because the guard is almost surely off.  The frozen block is
  unchanged; the definition it names is what changed.
  The two observables of `thm:subcritical` now carry NO guard of their own.  The
  hole count never did once the clauses were weakened; the survival indicator
  lost its guard as well, because on the set of pairwise distinct uniform
  variables every tie in the tagged realization involves the tagged particle and
  exactly one other, and the label order is site-major, so such a tie is decided
  by the two sites, or at the origin by an index the relabeling does not move.
  That is `Parking.TieInvariant`, the hypothesis `Support/RelabelEquiv.lean` now
  takes in place of the injectivity of the whole rank map.  Deleting the guard is
  also what makes the observables functions of the data at finitely many sites:
  the guard read the uniform variables of labels the box does not carry.

- `thm-near` (version 2): the uniform bound on the exponential moments now
  carries the integrability that makes it a bound on a moment.  Without it the
  Bochner integral of a nonintegrable function is zero and every family, however
  heavy tailed, satisfies the hypothesis, which would make the theorem vacuous.
  The same integrability is what makes the mean condition a condition on a
  genuine mean.  The same repair is in `Parking.NearFamily`, which is that
  hypothesis block.
- `thm-near` (version 3): the lower bound is read off
  `prop:near-divisible`, which carries `thm:BP`, `lem:stopping-time`,
  `lem:u-concentration` and `eq:green-norms`; Step 3 of the upper bound reads the
  two Green rates of `eq:green-norms` again at the cutoff of `eq:near-cutoff`,
  and `eq:near-routing-mean` and `eq:near-routing-moment` apply `prop:w-moment`,
  whose own proof cites the Bernstein inequality.  Those five are attached as
  explicit hypotheses, bound before every parameter of the statement, exactly as
  for `prop-near-divisible`.  Nothing else changed: no quantifier, bound,
  constant or conclusion.
- `thm-oriented-walk` (version 2): Step 1 of the paper's
  proof takes `r`-th moments in the directed pathwise comparison and inserts the
  directed form of `prop:w-moment`, whose own proof cites the Bernstein
  inequality, and Steps 2 to 4 read `eq:oriented-u-concentration`; the last part
  of the statement is read off `prop:oriented-scaling`, which carries the cutoff
  and stability estimates of the parabolic scaling limit.  Those three are
  attached as explicit hypotheses, bound before every parameter of the statement.
  Nothing else changed: no quantifier, bound, constant or conclusion.  The node is
  sealed, using the proved `prop:oriented-scaling`.
- Several nodes assert the integrability or summability that their proofs
  establish alongside the identity or the bound, so that an undefined integral
  or a divergent series cannot satisfy them through a junk value.
- `lem-parallel` (version 2): the identity fails for a realization whose
  instructions are not neighbours of the site carrying them, because the
  arrivals at `x` in a round come from the neighbours of `x` and a particle
  that has moved `t` times is within distance `t` of where it started.  The
  instructions of the model are neighbours, since `ρ_j(y)` has the law
  `P(y,·)`, so the hypothesis is part of what "realization" means.
- `thm-nearest` and `thm-nearest-counterexample` (version 2): `holeDistance`
  and `activeDistance` now measure the graph distance `Parking.graphNorm`, as
  `parking.tex:588-601` fixes it, and not the sup norm.  `Parking.supNorm`
  stays, since it is what measures the range of a kernel.
- `thm-master` (version 4), `cor-growth` (version 3) and `thm-trichotomy`
  (version 3) carry `ext-green-norms` as well.  The upper bound of `thm:master`
  IS the first display of `thm:upper`, which quotes the collected Green
  estimates; `cor:growth` inserts `thm:BP` into that bound, and parts (i) and
  (iii) of `thm:trichotomy` read the growth of the mean odometers off
  `cor:growth`.  `thm-four-sparse` does NOT carry it: its proof quotes `thm:BP`,
  the optimal stopping representation and `eq:q-lower-log`, and never
  `thm:upper`.
- `prop-discrepancy` (version 3) carries `ext-green-norms`: its proof at
  `parking.tex:1571-1576` explicitly uses `eq:green-norms` in the logarithmic
  moment optimization. The rates and all quantifiers are unchanged.
- `thm-nearest-counterexample` (version 3) carries `ext-bernstein` through
  `lem-nearest-one-point` and `prop-nearest-two-hole`, used in its proof at
  `parking.tex:2200-2255`. Its law, dimensions, strict graph-distance comparison
  and quantifiers are unchanged. The probability sequence is bounded by one,
  which justifies retaining its real `liminf`.
- `lem-critical-density` (version 2): the paper's `liminf_{t}tS_t\geq c` is
  transcribed as the eventual bound `\forall^f t, c\leq tS_t`.  In `\R` the
  `liminf` is the supremum of the set of eventual lower bounds, and `Real.sSup`
  of a set that is not bounded above is the junk value `0`; below dimension four
  `eq:activity` makes `tS_t` of order `t^{(4-d)/4}`, which tends to infinity, so
  the clause as a `liminf` in `\R` read `c\leq0` and was false at every
  dimension the lemma covers.  The eventual bound is what the paper's Step 3
  proves, and it implies the paper's assertion wherever the `liminf` is not a
  junk value.  `thm-trichotomy` part (ii) keeps its real `liminf`: its preceding conjunct
  bounds the ratio above for each fixed law using the cited upper estimates.
- `thm-four-sparse` (version 3): the asymptotic lower bound is written as an
  eventual inequality, with a smaller universal constant. Its proof at
  `parking.tex:1626-1642` supplies this directly. The threshold may depend on
  the sparse-law parameter; the positive constant is bound before that
  parameter. The upper boundedness used to justify the real `liminf` in
  `thm-trichotomy` needs concentration, Bernstein and Green estimates that
  are absent from this node. The eventual formulation keeps precisely the
  cited inputs of the sparse-law proof.
- `thm-trichotomy` (version 2): the `L^r` clause of part (i) asserts the
  finiteness of the moment alongside its convergence to zero, so that an
  undefined integral cannot satisfy the convergence through its junk value.
- `thm-master`, `cor-growth` and `thm-trichotomy` (version 2) carry the results
  their proofs quote from outside the paper: the martingale moment inequality
  and the concentration estimate, and, for `thm-trichotomy`, the optimal
  stopping representation, which its part (ii) reaches through
  `thm:four-sparse`.
- `prop-near-divisible` (version 3): Step 1 of the paper's
  proof applies `lem:mean-horizon`, whose own Step 1 cites `eq:green-norms` at
  `parking.tex:2790`, and Step 3 repeats that step at a bounded reference law,
  where the two Green rates are read again.  So `Parking.External.GreenNorms` is
  attached as a fourth explicit hypothesis, bound alongside the three the node
  already carried and before every parameter of the statement, exactly as for
  `lem-mean-horizon`.  Nothing else changed: no quantifier, bound, constant or
  conclusion.
- `lem-mean-horizon` (version 5): Step 1 of the paper's
  proof cites `eq:green-norms` at `parking.tex:2790` to read the concentration
  term `\sqrt r\|g_m\|_2+r\max_xg_m(x)` as a multiple of the scale
  `\phi_d(m)`, so `Parking.External.GreenNorms` is attached as a fourth
  explicit hypothesis, bound alongside the three the node already carried and
  before every parameter of the statement.  Nothing else changed: no quantifier,
  bound, constant or conclusion.
- `ext-stopping` (version 2) and `lem-mean-horizon` (version 4): the supremum
  of `eq:stopping` and the stopping rule of `lem:mean-horizon` are stated in the
  shared library's vocabulary, `LatticeProb.IsWalkStopping` on trajectories
  against `LatticeProb.siteWalkLaw`, rather than on the direction sequences of
  `Parking/Support/Walk.lean`.  A stopping time of the walk is a function of the
  trajectory whose value at `k` is settled by the positions up to time `k`,
  which is what the paper's "stopping times for the natural filtration of `X`"
  means, and it is the form in which the library proves the representation.
- `thm-subcritical-tail` (version 3): the Donsker-Varadhan estimate for the
  range, which the paper cites at `parking.tex:117-121` and uses at
  `parking.tex:2499-2502` to turn the two bounds in `|R_t|` into the two bounds
  in `t`, is carried as the explicit hypothesis
  `Parking.External.DonskerVaradhanRange`.  Nothing else changed; the
  version was bumped only by the re-registration that recorded the node as
  SEALED, and the frozen block is byte for byte the one version 2 carried.
- `lem-near-tilt` (version 3): the version was bumped only by the
  re-registration that recorded the node as SEALED; the frozen block is byte for
  byte the one version 2 carried.  The proof does not use two of the hypotheses
  the family `Parking.NearFamily` carries, the nonconstancy of the law at
  `\delta = 0` and the coupling of expected absolute difference `K\delta`.  The
  paper's Step 1 (`parking.tex:2595-2611`) proves `\lambda_\delta\asymp\delta`
  in both directions, and the upper bound on `S_t^\delta` needs only the
  direction `\lambda_\delta\gtrsim\delta`, which comes from an upper bound on
  `\psi_\delta''` alone; the reverse direction is what the nonconstancy and the
  coupling supply, and it is what the rest of Section 11 uses.
- `lem-gamma-sum` (version 2): the gradient bound `eq:green-gradient` in
  dimension two and above is an explicit hypothesis, as
  `Parking.External.GreenGradient d` under `2 ≤ d`.  The paper proves that
  bound by citing Lawler–Limic, so it is an external input; in dimension one
  the proof of the lemma computes the gradient exactly and nothing is assumed
  there.
- `lem-transport` (version 2): the exchangeability clause restricts both laws
  to the event `{η(0)=k}` that the paper conditions on, and records the
  activity histories alone rather than paired with the value of `η(0)`.
  Version 1 asserted the invariance under a permutation of the labels
  `(0,0), …, (0,k-1)` on every realization, including those with `η(0) < k`,
  where such a permutation moves an index below `η(0)` to an index above it:
  for `ν = (δ₂+δ₃)/2`, `k = 3` and the transposition of `1` and `2`, the label
  `(0,1)` is active at time `0` and `(0,2)` is not on the event `{η(0)=2}`, so
  the two laws give a set the probabilities `1/2` and `0`.
- `lem-exposure` (version 2): the measurability of `U_{k+1}` for the exposure
  filtration is asserted almost surely, as the existence of a
  `\mathcal G_k`-measurable field that `U_{k+1}` agrees with off a null set.
  Version 1 asserted it pathwise, which is false: for a realization whose
  instructions are not neighbours of the site carrying them, a particle can
  stand at a site it is not a candidate for, where it reads the instruction of
  index exactly `U_{k+1}` of that site, which no generator of the filtration
  records, and its later position depends on it.  In `d = 1`, one particle that
  jumps two sites in the first round separates two stacks that every generator
  of `\mathcal G_2` identifies and that give `U_3` different values.  Such
  realizations are null, and the almost-sure form is what the proof of
  `lem:w-martingale` uses.
- `prop-everyone-settles` (version 2): "settles after finitely many rounds" is
  a time past which the property holds at every later round, and "infinitely
  many distinct particles leave every site" says the particle stands elsewhere
  after the next round.
- `prop-spatial-scaling` (versions 5-6) and `thm-nearest` (versions 6-7): Step 1
  of the paper's proof of `prop:spatial-scaling` (`parking.tex:1740-1744`) cites
  "the argument proving the parabolic scaling limit in [BP], with the time
  variable and scenery retained" for the joint convergence
  `(\eta_R,\overline u_R)`, together with a union bound transferring it to
  `\overline U_R`; this is BP's own Theorem 1.3(i)(b)
  (`sandpile.tex:206-235`).  So the node
  carries `Parking.External.SpatialOdometerScaling` as a fifth explicit
  hypothesis, bound alongside the four the node already carried and before every parameter
  of the statement: it exhibits the noise `W`, the auxiliary field `Z`, and the
  continuum value `Uc` together with BP's own sup representation of it, and the
  finite-dimensional convergence of `(scenePair,barDivisible)` to `(W,Uc)`,
  jointly, with the scenery retained.  Version 5 also attached
  `Parking.External.SpatialFixedTimeTightness` as a sixth hypothesis to supply
  the equicontinuity clause; version 6 removes it again, because version 2 of
  `SpatialOdometerScaling` carries the JOINT space-time
  equicontinuity clause directly (the same `C_loc` conclusion of BP's theorem,
  read at every horizon simultaneously rather than at one fixed time, exactly
  as `parking.tex:1745-1747`'s own "estimates uniform on compact time
  intervals" licenses), which subsumes and is strictly stronger than
  `SpatialFixedTimeTightness`'s single-time restriction — the fixed-time
  External could not, alone, supply the joint-in-time clause the node needs
  (deriving genuine local-uniform equicontinuity from finite-dimensional
  convergence alone is false in general), so keeping both would leave one
  hypothesis unused.  `thm-nearest`'s own proof runs through
  `prop:spatial-scaling`, so it carries the same (single) extra hypothesis.
  Neither conclusion is otherwise changed.


- `prop-spatial-scaling` (version 9) identifies the limit as the Brownian
  optimal-stopping value of the exhibited noise. `ext-spatial-odometer-scaling`
  (version 3) specifies the Green field through the continuous linear L²
  extension of the test-function noise, with the variance-scaled isometry.
  Coordinatewise a.e. changes of the noise preserve this representation.
  `thm-nearest` (version 9) consumes this strengthened spatial proposition;
  its statement is unchanged.

- `prop-spatial-scaling` and `thm-nearest` carry the three classical parabolic
  inputs `HeatInteriorRegularity`, `HeatStrongMinimum`, and `HeatCompactness`.
  Steps 3–4 of `parking.tex:1785-1805` use interior regularity, compactness of
  nonnegative caloric functions with bounded local integrals, and backward
  propagation of a zero minimum. The local integral bound for the time
  quotients is proved by telescoping; the compactness input supplies a smooth
  classical subsequential limit. Their conclusions are unchanged.

### The two constructions, and where the equality of their laws is used

`parking.tex:630` asserts that the stack construction of Section 3 and the
particle-driven construction, in which every particle carries its own walk and
its own uniform variables, have the same law, and it does not prove it.  It is
`Parking.constructionsAgree'` (and `Parking.constructionsAgree` in the shared
library's vocabulary), proved in `Parking/Support/Agree.lean`, and the form the
proofs use is `Parking.constructionsAgree_conf`, which records the
configuration beside the odometer, the activity, the hole counts and the
activity field, and holds for an arbitrary law of configurations.  Two sealed
nodes rest on it: `lem-density-compare`, whose lower bound has no pathwise form
in the stack construction, and `lem-transport`, whose exchangeability clause is
false as a pathwise symmetry of the stack construction and true as a
relabelling of two independent families in the particle-driven one.  Neither is
an external input: both are theorems here.

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

The proof of `thm:nearest` (`parking.tex:1807-1833`) uses
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
identities. Both of the source theorem's cited hypotheses are retained as
separately frozen inputs. It is a cited input and remains an explicit
local proposition here.

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

## Frozen surface

<!-- FROZEN-SURFACE-BEGIN (generated by tools/sync_docs.py) -->

| id | Lean | paper | state |
|---|---|---|---|
| `ext-sandpile-growth` | `Parking.External.SandpileGrowth` | `parking.tex:919-932`, `thm:BP` | FROZEN |
| `ext-u-concentration` | `Parking.External.UConcentration` | `parking.tex:1387-1400`, `lem:u-concentration` | FROZEN |
| `ext-bernstein` | `Parking.External.Bernstein` | `parking.tex:1165-1178`, `lem:bernstein` | FROZEN |
| `lem-tagged-monotonicity` | `Parking.Frozen.tagged_monotonicity` | `parking.tex:712-717`, `lem:tagged-monotonicity` | SEALED |
| `lem-parallel` | `Parking.Frozen.parallel` | `parking.tex:647-653`, `lem:parallel` | SEALED |
| `lem-one-particle` | `Parking.Frozen.one_particle` | `parking.tex:682-690`, `lem:one-particle` | SEALED |
| `lem-pathwise-comparison` | `Parking.Frozen.pathwise_comparison` | `parking.tex:966-975`, `lem:pathwise-comparison` | SEALED |
| `ext-stopping` | `Parking.External.Stopping` | `parking.tex:866-874`, `lem:stopping` | SEALED |
| `lem-deferred` | `Parking.Frozen.deferred` | `parking.tex:659-667`, `lem:deferred` | SEALED |
| `thm-comparison` | `Parking.Frozen.comparison` | `parking.tex:879-885`, `thm:comparison` | SEALED |
| `lem-activity-holes` | `Parking.Frozen.activity_holes` | `parking.tex:768-774`, `lem:activity-holes` | SEALED |
| `lem-shift` | `Parking.Frozen.shift` | `parking.tex:3032-3037`, `lem:shift` | SEALED |
| `lem-nearest-close-pair` | `Parking.Frozen.nearest_close_pair` | `parking.tex:2184-2189`, `lem:nearest-close-pair` | SEALED |
| `lem-gamma-sum` | `Parking.Frozen.gamma_sum` | `parking.tex:1047-1052`, `lem:gamma-sum` | SEALED |
| `ext-green-gradient` | `Parking.External.GreenGradient` | `parking.tex:1019-1030`, `eq:green-gradient` | SEALED |
| `lem-exposure` | `Parking.Frozen.exposure` | `parking.tex:1097-1105`, `lem:exposure` | SEALED |
| `lem-density-compare` | `Parking.Frozen.density_compare` | `parking.tex:803-813`, `lem:density-compare` | SEALED |
| `lem-transport` | `Parking.Frozen.transport` | `parking.tex:739-751`, `lem:transport` | SEALED |
| `lem-range-lower` | `Parking.Frozen.range_lower` | `parking.tex:2280-2288`, `lem:range-lower` | SEALED |
| `lem-w-martingale` | `Parking.Frozen.w_martingale` | `parking.tex:1125-1138`, `lem:w-martingale` | SEALED |
| `ext-green-norms` | `Parking.External.GreenNorms` | `parking.tex:1366-1386`, `eq:green-norms` | FROZEN |
| `thm-upper` | `Parking.Frozen.upper` | `parking.tex:1403-1416`, `thm:upper` | SEALED |
| `lem-critical-density` | `Parking.Frozen.critical_density` | `parking.tex:1240-1248`, `lem:critical-density` | SEALED |
| `cor-critical` | `Parking.Frozen.cor_critical` | `parking.tex:1339-1346`, `cor:critical` | SEALED |
| `thm-master` | `Parking.Frozen.master` | `parking.tex:159-168`, `thm:master` | SEALED |
| `cor-growth` | `Parking.Frozen.growth` | `parking.tex:174-188`, `cor:growth` | SEALED |
| `prop-discrepancy` | `Parking.Frozen.discrepancy` | `parking.tex:1551-1568`, `prop:discrepancy` | SEALED |
| `thm-four-sparse` | `Parking.Frozen.four_sparse` | `parking.tex:1586-1595`, `thm:four-sparse` | SEALED |
| `thm-trichotomy` | `Parking.Frozen.trichotomy` | `parking.tex:207-238`, `thm:trichotomy` | SEALED |
| `lem-nearest-one-point` | `Parking.Frozen.nearest_one_point` | `parking.tex:1867-1876`, `lem:nearest-one-point` | SEALED |
| `prop-nearest-two-hole` | `Parking.Frozen.nearest_two_hole` | `parking.tex:2010-2017`, `prop:nearest-two-hole` | SEALED |
| `thm-nearest-counterexample` | `Parking.Frozen.nearest_counterexample` | `parking.tex:289-302`, `thm:nearest-counterexample` | SEALED |
| `ext-donsker-varadhan` | `Parking.External.DonskerVaradhanRange` | parking.tex:117-121 (Theorem 1 of Donsker-Varadhan 1979, cited for eq:sharpness and used at parking.tex:2499-2502) | FROZEN |
| `prop-everyone-settles` | `Parking.Frozen.everyone_settles` | `parking.tex:1486-1494`, `prop:everyone-settles` | SEALED |
| `prop-resolvent` | `Parking.Frozen.resolvent` | `parking.tex:2628-2648`, `prop:resolvent` | SEALED |
| `lem-mean-horizon` | `Parking.Frozen.mean_horizon` | `parking.tex:2764-2770`, `lem:mean-horizon` | SEALED |
| `prop-near-divisible` | `Parking.Frozen.near_divisible` | `parking.tex:2829-2845`, `prop:near-divisible` | SEALED |
| `ext-oriented-stopping-stability` | `Parking.External.OrientedStoppingStability` | parking.tex:3199-3203 (the cutoff and stability estimates of the parabolic scaling limit, cited in the proof of prop:oriented-scaling) | FROZEN |
| `lem-product` | `Parking.Frozen.product` | `parking.tex:2321-2332`, `lem:product` | SEALED |
| `thm-subcritical` | `Parking.Frozen.subcritical` | `parking.tex:2419-2432`, `thm:subcritical` | SEALED |
| `thm-subcritical-tail` | `Parking.Frozen.subcritical_tail` | `parking.tex:123-135`, `thm:subcritical-tail` | SEALED |
| `lem-near-tilt` | `Parking.Frozen.near_tilt` | `parking.tex:2584-2589`, `lem:near-tilt` | SEALED |
| `thm-near` | `Parking.Frozen.near` | `parking.tex:314-335`, `thm:near` | SEALED |
| `ext-variance-scale` | `Parking.External.VarianceScale` | parking.tex:1807-1833 (critical_toppling input, sandpile.tex:1117-1240) | FROZEN |
| `ext-multivariate-berry-esseen` | `Parking.External.MultivariateBerryEsseen` | parking.tex:1807-1833 (critical_toppling input, sandpile.tex:1770-1782, quoted from Raic Theorem 1.1) | FROZEN |
| `ext-binomial-local-clt` | `Parking.External.BinomialLocalCLT` | parking.tex:3192-3203 (the binomial local central limit theorem cited in step 1 of the proof of prop:oriented-scaling) | FROZEN |
| `prop-oriented-scaling` | `Parking.Frozen.oriented_scaling` | `parking.tex:3151-3159`, `prop:oriented-scaling` | SEALED |
| `thm-oriented-walk` | `Parking.Frozen.oriented_walk` | `parking.tex:363-380`, `thm:oriented-walk` | SEALED |
| `ext-spatial-fixed-time-tightness` | `Parking.External.SpatialFixedTimeTightness` | parking.tex:1741-1752 (prop:spatial-scaling, quoted from BP Theorem 1.3(i)(b)) | FROZEN |
| `ext-spatial-stopping-stability` | `Parking.External.SpatialStoppingStability` | parking.tex:1741-1752 (the cutoff and stability estimates of the parabolic scaling limit, cited in the proof of prop:spatial-scaling) | FROZEN |
| `ext-srw-local-clt` | `Parking.External.SRWLocalCLT` | parking.tex:1741-1752 (prop:spatial-scaling, quoted from BP eq. (25), citing Lawler-Limic Thm 2.1.3 Eq. (2.8)) | FROZEN |
| `thm-oriented` | `Parking.Frozen.oriented` | `parking.tex:3057-3070`, `thm:oriented` | SEALED |
| `prop-w-moment` | `Parking.Frozen.w_moment` | `parking.tex:1187-1200`, `prop:w-moment` | SEALED |
| `ext-heat-compactness` | `Parking.External.HeatCompactness` | parking.tex:1785-1805 (prop:spatial-scaling, Step 3, classical parabolic compactness) | FROZEN |
| `ext-spatial-odometer-scaling` | `Parking.External.SpatialOdometerScaling` | parking.tex:1741-1752 (prop:spatial-scaling, quoted from BP Theorem 1.3(i)(b), sandpile.tex:206-235) | FROZEN |
| `prop-spatial-scaling` | `Parking.Frozen.spatial_scaling` | `parking.tex:1679-1737`, `prop:spatial-scaling` | SEALED |
| `thm-nearest` | `Parking.Frozen.nearest` | `parking.tex:266-275`, `thm:nearest` | SEALED |
| `ext-linear-field-scaling` | `Parking.External.LinearFieldScaling` | parking.tex:1741-1752 (prop:spatial-scaling, BP Proposition 4.3, page 27) | FROZEN |
| `ext-heat-strong-minimum` | `Parking.External.HeatStrongMinimum` | parking.tex:1785-1805 (prop:spatial-scaling, Step 4, strong minimum principle) | FROZEN |
| `ext-heat-interior-regularity` | `Parking.External.HeatInteriorRegularity` | parking.tex:1785-1805 (prop:spatial-scaling, Step 3, hypoelliptic interior regularity) | FROZEN |
| `ext-critical-scale-lower-tail` | `Parking.External.CriticalScaleLowerTail` | parking.tex:1807-1833 (the critical-scale lower tail estimate of Bou-Rabee-Panagiotis, sandpile.tex:1696-1720) | FROZEN |

<!-- FROZEN-SURFACE-END -->
