# The proof and the Lean tree

This file describes the mathematics of *Sharpness and critical scaling of
parking* (Bou-Rabee and Panagiotis) and the Lean 4 development that
formalizes it. Part A states the results as the paper proves them, section
by section. Part B maps each registered statement to the Lean declarations
and support modules that prove it, and records the two places the tree is
still open. Part C lists the cited inputs and what is deliberately not
assumed.

The pinned source is `paper/parking.tex`. Every registered statement is a
declaration in its own file under `Parking/Frozen/` or `Parking/External/`,
with a paper line anchor recorded in `ledger/manifest.yaml`. The library
`Parking` is built on Mathlib and on the shared library `LatticeProb`, which
supplies the lattice `Site d`, the simple random walk, and its Green
function.

## Part A. The mathematics

### The model: particle odometer and divisible sandpile

At each site of `Z^d` an independent random number `η(x)` of particles minus
holes is placed. Particles move by independent simple random walks in
discrete time and settle at the first hole they reach; when several arrive
at a site with fewer holes than arrivals, the holes are filled in increasing
order of an independent uniform variable attached to each arrival. The
particle odometer `U_n(x)` counts the steps taken from `x` in the first `n`
rounds (`sec:model`, `parking.tex:612-839`). Attaching the randomness to
sites rather than particles gives the stack construction: each site carries
an independent stack of instructions, and the `j`-th departure from `y`
reads `ρ_j(y)`. `lem:parallel` (`parking.tex:647-653`) is the resulting
recursion `U_{n+1}(x) = (η(x) + Σ_y I_{y,x}(U_n(y)))^+`. `lem:deferred`
(`parking.tex:659-667`) is the deferred-decision principle: an instruction
not yet read stays independent of everything that has happened, so `U_n(y)`
crossing a threshold `j` is measurable with respect to the initial
configuration and every instruction except `ρ_j(y)`. `lem:one-particle` and
`lem:tagged-monotonicity` (`parking.tex:682-717`) couple two configurations
differing by one particle: exactly one active particle or one unfilled hole
is unmatched at every time, and every particle present in both couplings
stays active at least as long in the larger configuration.
`lem:activity-holes` (`parking.tex:768-774`) and `lem:density-compare`
(`parking.tex:803-813`) are the two conservation identities that close the
section: the density of active particles and of unfilled holes differ by
`E η(0)` at every time, and a translation-invariant coupling with
stochastically larger data has a stochastically larger activity density.
`lem:transport` (`parking.tex:739-751`) is the mass-transport identity
`E U_n(0) = Σ_{s<n} S_s`, where `S_t` is the expected number of particles
from the origin unsettled at time `t`, together with the exchangeability of
the activity histories at the origin conditionally on its particle count.

The divisible sandpile odometer `u_n(x)` (`sec:divisible`,
`parking.tex:840-938`) is the deterministic analogue in which mass divides
equally among neighbors instead of following one instruction; it solves the
optimal-stopping problem `u_n(x) = sup_{σ≤n} E_x Σ_{j<σ} η(X_j)`
(`eq:stopping-intro`, `lem:stopping`, `parking.tex:866-874`, quoted from
Bou-Rabee-Peres-Sava-Huss). `thm:comparison` (`parking.tex:879-885`) is the
quenched domination `u_n(x) ≤ E[U_n(x) | η]`, since the particle system can
only be delayed relative to the deterministic recursion.

### Pathwise comparison and moment bounds

`sec:routing` (`parking.tex:939-1228`) bounds the gap between the two
odometers pathwise. Let `w_0 = 0` and
`w_{k+1}(x) = (1/2d) Σ_{y~x} w_k(y) + Σ_{y~x}(I_{y,x}(U_k(y)) - (1/2d)U_k(y))`
(`eq:error-recursion`) record the accumulated difference between actual
arrivals and their means. `lem:pathwise-comparison` (`parking.tex:966-975`)
bounds `|U_n(x) - w_n(x) - u_n(x)|` by `w_n^⋆(x)`, the maximum of `|w|` along
an independent walk, and hence `|U_n(x)-u_n(x)| ≤ 2 w_n^⋆(x)`.
`lem:exposure` (`parking.tex:1097-1105`) reveals each instruction only when
first used, so that `w_n(0)` is a sum of bounded martingale differences for
the filtration this generates. `lem:gamma-sum` (`parking.tex:1047-1052`)
bounds the sum of the resulting conditional variances by a truncated
Green-function quantity `Γ`, using the gradient bound `eq:green-gradient`
(`parking.tex:1019-1030`, from Lawler-Limic, dimension `d≥2`; computed
directly in `d=1`). `lem:w-martingale` (`parking.tex:1125-1138`) records the
resulting predictable quadratic variation identity, and `prop:w-moment`
(`parking.tex:1187-1200`, Proposition 5.6) is the martingale moment bound
this variation gives via the Bernstein-type inequality `lem:bernstein`
(`parking.tex:1165-1178`, from Pinelis): a dimension-dependent `C` such that
`max_{m≤n}(E|w_m(0)|^r)^{1/r} ≤ C(√(r κ_d(n) (E U_n(0)^r)^{1/r}) + r)` and
`(E w_n^⋆(0)^r)^{1/r} ≤ (n+1)^{1/r} max_{m≤n}(E|w_m(0)|^r)^{1/r}`.

### The logarithmic lower bound and growth of the expected odometer

`sec:critical` (`parking.tex:1229-1354`) proves a logarithmic lower bound on
`E U_n(0)` uniform over every mean-zero nonconstant integer law, by adapting
the resampling argument of Cabezas-Rolla-Sidoravicius to discrete time:
couple the original and a resampled configuration with shared steps, match
common particles, and bound the expected number of canceled labels by
simple random walk return probabilities. `lem:critical-density`
(`parking.tex:1240-1248`) is the resulting `liminf_t t S_t ≥ c` (a universal
constant) and `E U_n(0) ≥ c log n - C`; `cor:critical`
(`parking.tex:1339-1346`) restates it as a lower bound on `E U_n(0)` alone.

`sec:bounds` (`parking.tex:1354-1537`) proves the matching upper bound.
`eq:green-norms` (`parking.tex:1366-1386`, from BP Section 3.1) collects the
Green-function rates `‖g_n‖_2` and `max_x g_n(x)` in every dimension.
`lem:u-concentration` (`parking.tex:1387-1400`, BP Remark 3.4) is the
translation-invariant-kernel concentration inequality
`(E|v_n(0)-E v_n(0)|^r)^{1/r} ≤ C(√r ‖g_n^K‖_2 + r ‖g_n^K‖_∞)` for the
recursion `v_{n+1}=(η+Kv_n)^+`. `thm:upper` (`parking.tex:1403-1416`)
combines the pathwise comparison, Young's inequality, `prop:w-moment` and
`lem:u-concentration` into `E U_n(0) ≤ C(E u_n(0) + log n)`, taking `r=8`
below dimension four and `r` of order `log n` from dimension four on.
`thm:master` (`parking.tex:159-168`, stated in the introduction) combines
this with `lem:critical-density` into the two-sided
`c(E u_n(0)+log n) ≤ E U_n(0) ≤ C(E u_n(0)+log n)`. `cor:growth`
(`parking.tex:174-188`) inserts the sandpile growth rates of `thm:BP`
(`parking.tex:919-932`, quoted from the divisible-sandpile paper) to get
`E U_n(0) ≍ n^{(4-d)/4}` for `d≤3` and `≍ log n` for `d≥4`, together with the
matching two-sided bound on the activity `S_t`. `prop:everyone-settles`
(`parking.tex:1486-1494`) observes that although `S_t→0`, the particle
odometer is infinite at every site, contributed by infinitely many distinct
particles arriving from ever further away.

### Quenched odometer comparison

`sec:four` (`parking.tex:1537-1670`) refines the comparison between the two
odometers pathwise rather than only in mean. `prop:discrepancy`
(`parking.tex:1551-1568`) bounds `(E|U_n(0)-u_n(0)|^r)^{1/r}` at the balanced
exponent `r = 2 ∨ ⌈log(n+1)⌉` for `d≤3`, giving a concentration tail for the
discrepancy around its mean. `thm:four-sparse`
(`parking.tex:1586-1595`) shows that in dimension four the ratio
`E U_n(0)/E u_n(0)` cannot be bounded uniformly over the law: for a sparse
symmetric law taking values `±1` with probability `ε/2`, convexity and
positive homogeneity of `u_n(0)` as a function of `η` (from the
optimal-stopping representation) force `liminf_n E U_n(0)/E u_n(0) ≥ c
log(e/ε)`, while the logarithmic lower-bound coefficient of
`lem:critical-density` is law-independent. `thm:trichotomy`
(`parking.tex:207-238`, stated in the introduction) assembles the three
regimes: `d≤3` (the ratio converges to one, a.s. and in `L^r`), `d=4` (bounded
above for each fixed law, unboundedly so across laws, by `thm:four-sparse`),
and `d≥5` with `η(0)` bounded below (the ratio diverges to infinity).

### The nearest particle and hole

`sec:nearest` (`parking.tex:1670-2262`) answers whether the origin ends up
closer to an active particle or an unfilled hole. Below dimension four,
`prop:spatial-scaling` (`parking.tex:1679-1737`) is the parabolic scaling
limit: jointly, the rescaled scenery `η_R` converges to spatial white noise
`W`, and the rescaled divisible and particle odometers `ū_R`, `Ū_R` converge
locally uniformly on `(0,∞)×R^d` to the same continuous Brownian
optimal-stopping value `U`, which solves `∂_s U = (1/2d)ΔU + W` in the
distributional sense on `{U>0}` and whose time derivative `v=∂_s U` is
strictly positive there. `thm:nearest` (`parking.tex:266-275`, stated in the
introduction, proved at `parking.tex:1807-1833`) reads off strict positivity
of `U(1,0)` from the parabolic scaling limit and the critical-scale
lower-tail estimate of BP, then transfers it through the scaling limit to a
ball of the discrete lattice where the particle odometer is positive
everywhere and hence carries no unfilled hole, giving that every unfilled
hole is eventually farther from the origin than every active particle, by
any fixed ratio.

From dimension five on (`parking.tex:1835-2262`), the origin can end up
closer to a hole. `thm:nearest-counterexample` (`parking.tex:289-302`,
stated in the introduction) constructs, for the particle-hole law taking
values `±1` with probability `p∈(0,1/4]` and `0` otherwise, a positive
limiting probability that the origin is closer to an unfilled hole.
`lem:nearest-one-point` (`parking.tex:1867-1876`) bounds the moments of
`U_t(x)` by the mean `m_t=E U_t(0)` and `m_t` by `log(1/h_t)`, where
`h_t=P(H_t(0)=1)`; `prop:nearest-two-hole`
(`parking.tex:2010-2017`) and `lem:nearest-close-pair`
(`parking.tex:2184-2189`) bound the probability that two nearby sites are
simultaneously unfilled holes, using the Green-function bubble estimate
`eq:nearest-bubble-decay` from Lawler-Limic's Gaussian bound.

### Subcritical phase

`sec:subcritical` (`parking.tex:2262-2564`) proves `thm:subcritical-tail`
(`parking.tex:123-135`, stated in the introduction), the two-sided
stretched-exponential bound on `S_t` below the critical density, with
exponent `d/(d+2)` from the Donsker-Varadhan large-deviation estimate for
the range of a simple random walk. `lem:range-lower`
(`parking.tex:2280-2288`) is the elementary lower bound: conditionally on
the tagged particle's range, no other site of the range initially carrying
a hole gives independence across distinct sites. The upper bound tilts the
law of `η(0)` to raise the particle density and differentiates the
resulting survival probability in the tilt parameter `λ`; the derivative is
a covariance between the survival event and the number of unfilled holes
left in the range, which `lem:product` (`parking.tex:2321-2332`) bounds by
`3 ∂_λ E_λ F` for observables `F,Z` of the counts, walks and uniform
variables at finitely many tilted sites, invariant under relabeling the
particles present, with `F∈[0,1]` monotone increasing and `Z≥0` monotone
decreasing and Lipschitz under one addition or deletion. Integrating the
resulting differential inequality gives `thm:subcritical`
(`parking.tex:2419-2432`), the bound `S_t ≤ C E_0 e^{-a|R_t|}` on the range
`R_t` of the tagged particle's walk, which the Donsker-Varadhan estimate
converts into the stretched exponential.

### Near criticality

`sec:near` (`parking.tex:2564-2979`) proves `thm:near`
(`parking.tex:314-335`, stated in the introduction), the divergence rate of
`E U_∞^δ(0) = Σ_t S_t^δ` as the mean `-δ` of the initial law tends to zero.
`lem:near-tilt` (`parking.tex:2584-2589`) extends the subcritical tilt
bound uniformly across a family of laws with mean `-δ`, using that the
Legendre transform's unique positive zero `λ_δ` is of order `δ`.
`prop:resolvent` (`parking.tex:2628-2648`) is the resolvent tail bound
`Σ_{t>T} E_0 e^{-a|R_t|} ≤ 1` at an explicit threshold `T`, in every
dimension, needed because the tilt bound alone is not summable in `t`.
`lem:mean-horizon` (`parking.tex:2764-2770`) bounds the expected duration of
a near-optimal stopping rule for the tilted scenery, the delicate point
being that such a rule may run far longer than its expected duration.
`prop:near-divisible` (`parking.tex:2829-2845`) assembles these into the
two-sided bound on `E u_∞^δ(0)`: order `δ^{-3}, δ^{-1}, δ^{-1/3}` in
dimensions one to three, `log(e/δ)` in dimension four, and, when `η_δ(0)` is
additionally bounded uniformly in `δ`, `[log(e/δ)]^{2/d}` from dimension
five on. `thm:near` transfers this to the particle odometer through
`thm:master`'s comparison.

### Oriented walk

`sec:oriented` (`parking.tex:2979-end`) proves the analogous results for the
oriented walk, whose particles take steps `-e_i` with probability `1/d` and
never revisit a layer `Σ_i x_i = const`. Disjointness of the layer supports
makes the truncated Green function `g_n=Σ_{ℓ<n} p⃗_ℓ` bounded by one, with
`‖g_n‖_2^2 ≍ κ⃗_d(n)` of order `√n` (`d=2`), `log n` (`d=3`), and bounded
(`d≥4`) (`eq:oriented-green`), lowering the critical ambient dimension from
four to three. `lem:shift` (`parking.tex:3032-3037`), needed only for
`d=2`, is the exact identity `Σ_ℓ ‖p⃗_ℓ(·-q)-p⃗_ℓ‖_2^2 = 4|q|`, by Parseval's
identity on the layer's Fourier transform. `thm:oriented`
(`parking.tex:3057-3070`, "Divisible odometer") gives the three growth
regimes for `E u⃗_n(0)`: `Cn^{1/4}` at `d=2` under an `r>4` moment,
`C log(n+1)` at `d≥3` under an exponential moment, and the matching lower
bound `c√κ⃗_d(n)` under finite positive variance, the last from the
optimal-stopping representation at the deterministic stopping time `n`.
`prop:oriented-scaling` (`parking.tex:3151-3159`) is the parabolic scaling
limit for `d=2`: `n^{-1/4} u⃗_{⌊nT⌋}(0)` converges in distribution to a
self-similar limit `U(T) =^d T^{1/4} U(1)` with `μ = E U(1) ∈ (0,∞)`,
adapting BP's parabolic scaling limit with space-time white noise in place
of spatial white noise; its proof cites the binomial local central limit
theorem and the cutoff and stability estimates of BP's scaling limit, "of
the kind of" Coquet-Toldo. `thm:oriented-walk`
(`parking.tex:363-380`, stated in the introduction) reads off
`E u⃗_n(0) ~ μ n^{1/4}` and the resulting activity rate from this limit.

## Part B. The Lean tree

### Registered nodes

The manifest registers 53 declarations: 41 paper statements and 12 cited
inputs. 37 of the statements are `SEALED`; two, `prop-spatial-scaling` and
`prop-oriented-scaling`, are `DRAFT_SORRY`, meaning their statement is
frozen and registered but no proof exists yet; two more,
`thm-oriented-walk` and `thm-nearest`, are `CONDITIONAL`, meaning their own
proof carries no `sorry` but applies one of the two draft nodes, so their
axiom closure carries `sorryAx` until that node is sealed. Of the 12 cited
inputs, ten are `FROZEN` propositions assumed without proof and two,
`ext-stopping` and `ext-green-gradient`, are `SEALED`: proved inside this
repository or the shared library rather than left as bare hypotheses.
`CERTIFICATE.md` records the exact axiom closure of every node.

### Shared infrastructure

The vocabulary of the whole development is in `Parking/Basic.lean` (the
site type `Site d`, the configuration, the odometer recursions `u` and `U`,
`meanu`, `meanU`, `CriticalLaw`, `graphNorm`) and roughly ninety further
modules used by five or more of the eight proof steps below. `Walk`,
`Particle`, `OneParticle`, `Parallel`, `Deferred`, `Pathwise`, `Comparison`
and `Agree` build the particle-driven construction and prove
`Parking.constructionsAgree`, the fact (unproved in the paper) that the
stack construction of `sec:model` and the particle-driven construction in
which every particle carries its own walk and uniform variables have the
same law; `ActivityHoles`, `DensityCompare`, `Coupling`, `CouplingProof`,
`Equivariance`, `Invariance`, `Monotone`, `ConfMoments` and `ConfMonotone`
carry this into the two conservation identities and the coupling
comparisons. `Exposure`, `Filtration`, `Measurability`,
`ParticleMeasurability` and `Reads` build the exposure filtration of
`lem:exposure`. `GammaSum`, `GreenBridge`, `GreenIncrement`, `Kernel`,
`KernelBridge` and `HeatMoments` build the truncated Green-function
machinery `Γ` and `g_n`. `WMartingale`, `WFiltration`, `WCondExp`,
`WExploration`, `WQuadratic`, `WBound`, `WReads`, `WStarBound`,
`WStarMoment` and `WMomentProof` build the martingale `w` and its moment
bounds. `Odometer`, `OdometerLower`, `Error`, `ErrorUnroll`, `MassTransport`,
`Transport`, `Range`, `RangeLower`, `UBound`, `UConcBridge`, `UpperProof`,
`UpperStep`, `UpperTarget` and `CriticalLawReal` build the odometer
comparison and the critical upper bound. `CoordIntegral`, `Lp` and `Shells`
supply the integral and `ℓ^p` lemmas these use throughout.

### The particle odometer and the divisible sandpile

`lem-parallel` is proved by `Parking.parallel_of_labelOrder` in
`Parking/Support/Parallel.lean`. `lem-deferred` is proved by
`Parking.deferred_factorization` in `Parking/Support/DeferredIntegral.lean`.
`lem-one-particle` is proved by `Parking.one_particle_of_labelOrder` in
`Parking/Support/OneParticle.lean`. `lem-tagged-monotonicity` is proved by
`Parking.tagged_invariant` in `Parking/Support/Coupling.lean`.
`lem-activity-holes` is proved by `Parking.activity_holes_main` in
`Parking/Support/ActivityHoles.lean`. `lem-density-compare` is proved by
`Parking.S_mono_of_coupling` and `Parking.mean_activity_eq_survivors` in
`Parking/Support/DensityCompare.lean`. `lem-transport` is proved in
`Parking/Support/SurvivorExpansion.lean`. `thm-comparison` is proved by
`Parking.comparison_of_labelOrder` in `Parking/Support/Comparison.lean`.
`ext-sandpile-growth` (`Parking.External.SandpileGrowth`) and `ext-stopping`
(`Parking.External.Stopping`, SEALED, discharged by
`Parking.External.stopping` from `LatticeProb.Graph.Zd.parkingStopping'`,
via the identity `Parking.u_eq_zdOdometer`) are the two cited inputs of this
part of the tree.

### Pathwise comparison and moment bounds

`lem-pathwise-comparison` is proved by
`Parking.pathwise_comparison_of_labelOrder` in
`Parking/Support/Pathwise.lean`. `lem-exposure` is proved in
`Parking/Support/ExposureProduct.lean` (`Parking.exposure_condExp` and the
almost-sure measurability of `Parking.expOdometer`). `lem-gamma-sum` is
proved by `Parking.gamma_sum_of_gradient` in `Parking/Support/GammaSum.lean`,
carrying `ext-green-gradient` (`Parking.External.GreenGradient`, SEALED,
discharged by `Parking.External.greenGradient` from
`LatticeProb.exists_srwGreen_gradient`, via the lazy-walk parity transfer of
`LatticeProb/Walk/BinomWindow.lean`) for `d≥2`. `lem-w-martingale` is
proved in `Parking/Support/WQuadratic.lean`. `prop-w-moment` is proved by
`Parking.exists_wErr_moment_const_uniform` in `Parking/Support/WMomentProof.lean`,
carrying `ext-bernstein` (`Parking.External.Bernstein`); the registered
node's statement binds its constant before the law, exponent and moment
hypothesis, matching the paper's "dimension-dependent `C`" at
`parking.tex:1188`, and is the same theorem `Parking/Support/NearRouting.lean`
and `Parking/Support/UpperProof.lean` apply.

### The logarithmic lower bound and growth of the expected odometer

`lem-critical-density` is proved by `Parking.critical_density_of_coupling`
in `Parking/Support/CouplingProof.lean`. `cor-critical` is proved by
`Parking.cor_critical_of_critical_density` in
`Parking/Support/CriticalChain.lean`. `ext-green-norms`
(`Parking.External.GreenNorms`) and `ext-u-concentration`
(`Parking.External.UConcentration`) enter here. `thm-upper` is proved by
`Parking.exists_target` and `Parking.exists_critical_moment` in
`Parking/Support/UpperTarget.lean`, carrying SandpileGrowth, Bernstein,
UConcentration and GreenNorms. `thm-master` is proved by
`Parking.master_of_cor_critical` in `Parking/Support/MasterChain.lean`,
reading the upper bound off `thm-upper`'s external inputs. `cor-growth` is
proved by `Parking.growth_of_master` in `Parking/Support/GrowthChain.lean`.
`prop-everyone-settles` is proved in `Parking/Support/Settles.lean`,
`Parking/Support/AllInfinite.lean` and `Parking/Support/Departers.lean`
(`Parking.ae_settle_and_fill`, `Parking.ae_forall_Ulimit_top`,
`Parking.infinite_departers`), reading `cor-growth`'s decay of `S_t`. The
distinctive modules of this step, beyond the shared infrastructure, are
`GrowthChain`, `GrowthMeans`, `GrowthSequence`, `MasterChain`,
`OdometerInfinite`, `DensitySequence`, `Ergodic`, `Propagate`,
`SecondMoment` and `StackHits`.

### Quenched odometer comparison

`prop-discrepancy` is proved by `Parking.exists_discrepancy_moment` and
`Parking.exists_discrepancy_tail` in `Parking/Support/DiscrepancyTail.lean`,
carrying GreenNorms alongside the externals `thm-upper` needs.
`thm-four-sparse` is proved by `Parking.four_sparse_of_growth` in
`Parking/Support/FourSparseChain.lean`, using the sparse three-point law of
`Parking/Support/ThreePointLaw.lean` and carrying SandpileGrowth and
Stopping only. `thm-trichotomy` is proved in `Parking/Support/LowMeanLimits.lean`,
`Parking/Support/FourRatio.lean` and `Parking/Support/HighDiscrepancy.lean`
(`Parking.low_mean_ratio_tendsto_one`, `Parking.four_mean_ratio_bounds`,
`Parking.exists_four_mean_ratio_large`), assembling parts (i)-(iii). The
distinctive modules of this step are the `Discrepancy` family
(`DiscrepancyBalance`, `DiscrepancyFresh`, `DiscrepancyLabels`,
`DiscrepancyLimits`, `DiscrepancyMeas`, `DiscrepancyMoment`,
`DiscrepancyNorm`, `DiscrepancyRates`, `DiscrepancyRelative`,
`DiscrepancyScale`, `DiscrepancyShift`, `DiscrepancyTail`,
`DiscrepancyTransport`), together with `AbsoluteMeanPos`, `AtomUpdate`,
`ConvexProduct`, `ExpTail`, `FourRatio`, `FourSparseChain`, `HighDiscrepancy`,
`HighMeanLimits`, `Laplace`, `LastMove`, `LowMeanLimits`, `MeanPos`,
`MomentTail`, `OdometerRandomness`, `ParticleConfLaw`, `PositiveAtom`,
`SparseCompare`, `TailLimits`, `UConvex` and `UFinite`.

### The nearest particle and hole

`lem-nearest-one-point` is proved by `Parking.nearest_one_point_proof` in
`Parking/Support/NearestOnePointProof.lean`. `prop-nearest-two-hole` is
proved by `Parking.nearest_two_hole_proof` in
`Parking/Support/NearestTwoHoleProof.lean`. `lem-nearest-close-pair` is
proved by `Parking.close_pair` in `Parking/Support/ClosePair.lean`.
`thm-nearest-counterexample` is proved by
`Parking.nearest_counterexample_proof` in
`Parking/Support/NearestCounterexampleProof.lean`. These four carry only
`ext-bernstein`.

`prop-spatial-scaling` is `DRAFT_SORRY`: its statement, in
`Parking/Frozen/SpatialScaling.lean`, carries three convergence clauses
(finite-dimensional convergence of `(η_R,ū_R,Ū_R)`; local uniform closeness
in probability of the two discrete rescaled odometers; equicontinuity in
probability of the rescaled divisible odometer on every compact subset of
`(0,∞)×R^d`), assembled from `Parking/Support/Continuum.lean` and its
family (`ContOpRegularity`, `ContOrientedLimit`, `ContOrientedNoise`,
`ContOrientedValue`, `ContStopGeneral`). Its own proof file has no proof
yet: this is the first of the two open nodes. `thm-nearest` is
`CONDITIONAL`: its proof, `Parking.nearest_of_spatial_scaling` in
`Parking/Support/NearestFromSpatial.lean`, has no `sorry` of its own and
destructures `Parking.Frozen.spatial_scaling`, so the whole chain reduces to
that one open node. The chain it assembles is otherwise complete and
sorry-free: `Parking.ae_spatial_origin_pos` (almost-sure strict positivity
of the limiting odometer at `(1,0)`) from the critical-scale lower tail and
the finite-dimensional clause, `Parking.ae_exists_pos_l1_ball` (a positive
continuum ball, from the continuity clause), and
`Parking.nearest_of_positive_test_events`/`Parking.PositiveTestEvent` (the
discrete geometric and probability endgame), assembled through
`Parking/Support/NearestPathwise.lean`, `NearestSigned.lean` and
`NearestContinuumPositivity.lean`, from the positive-event estimate. The two
cited inputs `ext-critical-scale-lower-tail`, `ext-variance-scale` and
`ext-multivariate-berry-esseen` enter here, together with SandpileGrowth,
Bernstein and UConcentration. Given a sealed `prop-spatial-scaling`,
`thm-nearest` needs no further Lean work.

The distinctive modules of this step, beyond `Continuum` and the `Nearest`
family already named (`NearestBallEvent`, `NearestContinuumPositivity`,
`NearestCounterexampleProof`, `NearestCriticalModel`,
`NearestCriticalNormalization`, `NearestCriticalTail`,
`NearestDensityCriterion`, `NearestEvents`, `NearestFromSpatial`,
`NearestGeometry`, `NearestGreen`, `NearestHoleFilled`, `NearestLimit`,
`NearestMollifier`, `NearestOnePointProof`, `NearestPairSum`,
`NearestPathwise`, `NearestSigned`, `NearestSpatialAssembly`,
`NearestTestFun`, `NearestTwoHoleProof`), include the `Hole` family
(`HoleBounds`, `HoleCloserEvent`, `HoleCost`, `HoleKernel`,
`HoleKernelBound`, `HoleLocality`, `HoleMean`, `HoleNoArrival`,
`HolePositive`, `HoleRelative`, `HoleSinkEvent`, `HoleSinkLaw`, `HoleTail`),
the `Sink` family (`SinkCenteredMoment`, `SinkCompensatorMean`, `SinkField`,
`SinkGreenMoment`, `SinkLambdaMoment`, `SinkMean`, `SinkNoArrival`,
`SinkNoiseMoment`, `SinkObservable`, `SinkSceneryLaw`), the `Table` family
(`TableBernstein`, `TableDecomposition`, `TableDifference`,
`TableDifferenceSum`, `TableHoleLaw`, `TableJointNoise`, `TableLaw`,
`TableMomentBounds`, `TableQuadratic`, `TableReads`), the `Round` family
(`RoundArrivalMean`, `RoundBlock`, `RoundDifference`, `RoundDifferenceSum`,
`RoundEnumeration`, `RoundEnumerationSum`, `RoundHoleFactor`,
`RoundHoleSection`, `RoundMeanField`, `RoundNoArrival`, `RoundPartialMeas`),
the `Instruction` family (`InstructionField`, `InstructionHole`,
`InstructionHoleFactor`, `InstructionInfluence`, `InstructionPartial`,
`InstructionPartialCentered`, `InstructionUnused`), the `Isolated` family
(`IsolatedDensity`, `IsolatedHoles`, `IsolatedMeasurable`, `IsolatedShift`,
`IsolatedTransport`, `IsolationUnion`), and the `TwoHole` family
(`TwoHoleConstants`, `TwoHoleJoint`, `TwoHoleLoadMoment`,
`TwoHoleShellBounds`, `TwoHoleWeight`).

### Subcritical phase

`lem-range-lower` is proved in `Parking/Support/RangeLower.lean`.
`lem-product` is proved by `Parking.abs_cov_le_deriv` in
`Parking/Support/TiltCov.lean`, using the current definition of
`Parking.RelabelInvariant` (`SymmetricInParticles ∧ ReadsParticles`, both
guarded by `Parking.RanksDistinct`) in `Parking/Support/Range.lean`.
`thm-subcritical` is proved by `Parking.subcritical_a_pos`,
`Parking.survivalGivenWalk_le` and `Parking.S_le_rangeExp` in
`Parking/Support/SubcriticalJointBound.lean`. `thm-subcritical-tail` is
proved by `Parking.exists_tail_bounds` in
`Parking/Support/TailTwoSided.lean`, carrying `ext-donsker-varadhan`
(`Parking.External.DonskerVaradhanRange`). The distinctive modules of this
step are the `Subcritical` family (`SubcriticalBound`,
`SubcriticalConditional`, `SubcriticalDepends`, `SubcriticalGraft`,
`SubcriticalGraftStep1`, `SubcriticalGraftStep3`, `SubcriticalHoleMean`,
`SubcriticalInterval`, `SubcriticalInvariance`, `SubcriticalJoint`,
`SubcriticalJointBound`, `SubcriticalMeasurable`, `SubcriticalPair`,
`SubcriticalRelabel`, `SubcriticalStep1`, `SubcriticalStep2`,
`SubcriticalStep3`), the `Tilt` family (`Tilt`, `TiltContinuity`, `TiltCov`,
`TiltDeriv`, `TiltInterval`, `TiltProduct`), and the relabeling machinery
(`Relabel`, `RelabelEquiv`, `RelabelLaw`, `RankDistinct`, `ReadsPresent`,
`RestrictLaw`, `TaggedRankAe`, `TaggedSurvivor`, `NoiseSplice`,
`PairSplice`, `SpliceAvg`, `SceneryField`, `SceneryFinite`, `SceneryHole`,
`SceneryLaw`).

### Near criticality

`lem-near-tilt` is proved by `Parking.exists_near_tilt_bound` in
`Parking/Support/NearTiltInterval.lean`. `prop-resolvent` is proved by
`Parking.exists_resolvent_tail_one`, `Parking.exists_resolvent_tail_two`
and `Parking.exists_resolvent_tail_high` in
`Parking/Support/RangeResolvent.lean`. `lem-mean-horizon` is proved by
`Parking.exists_meanHorizon` in `Parking/Support/MeanHorizonProof.lean` and
`Parking/Support/MeanHorizonStep1.lean`, carrying SandpileGrowth, Stopping,
UConcentration and GreenNorms. `prop-near-divisible` is proved in
`Parking/Support/NearBounded.lean` and `Parking/Support/Near.lean`
(`Parking.exists_meanuLimit_upper`, `Parking.exists_meanuLimit_lower`,
`Parking.exists_meanuLimit_psi_upper`), carrying the same four externals.
`thm-near` is proved by `Parking.exists_rate_le_meanUlimit` and
`Parking.exists_meanUlimit_le_rate` in `Parking/Support/NearEndgame.lean`,
adding Bernstein as a fifth external. The distinctive modules of this step
are the `Near` family (`Near`, `NearBounded`, `NearBridge`, `NearCutoff`,
`NearDensity`, `NearEndgame`, `NearEnv`, `NearHorizon`, `NearLower`,
`NearLowerLog`, `NearMoment`, `NearOptimize`, `NearParticle`,
`NearProducts`, `NearRateBounds`, `NearRates`, `NearRouting`, `NearScale`,
`NearStep1`, `NearTail`, `NearTailSum`, `NearTiltInterval`,
`NearTiltMoments`), the `Block` family (`BlockAverages`, `BlockMoments`,
`BlockStop`, `BlockTail`, `BlockTools`), and the `Matched` family
(`MatchedBellman`, `MatchedBounds`, `MatchedCountIntegral`,
`MatchedLocality`, `MatchedMonotone`, `MatchedPriority`, `MatchedUniform`)
that formalizes the near-optimal stopping rule's expected-duration bound.

### Oriented walk

`lem-shift` is proved by `Parking.shift_energy` in
`Parking/Support/Shift.lean`. `thm-oriented` is proved by
`Parking.exists_meanuOriented_two_upper`,
`Parking.exists_meanuOriented_log_upper` and
`Parking.exists_meanuOriented_variance_lower` in
`Parking/Support/OrientedTwoMean.lean`,
`Parking/Support/OrientedLogMean.lean` and
`Parking/Support/OrientedAllNorms.lean`; the registered node no longer
carries `ext-stopping`, matching the paper's own statement of
`thm:oriented`. `prop-oriented-scaling`
is `DRAFT_SORRY`: its statement, in `Parking/Frozen/OrientedScaling.lean`,
asserts the existence and measurability of the self-similar limit `Uc` with
the exponent `1/4`, and carries `ext-oriented-stopping-stability` and
`ext-binomial-local-clt`. This is the second of the two open nodes.
`thm-oriented-walk` is `CONDITIONAL`: its proof,
`Parking.oriented_walk_of_mean` in `Parking/Support/OrientedActivity.lean`,
has no `sorry` of its own and destructures `Parking.Frozen.oriented_scaling`,
so the whole chain reduces to that one open node. The distinctive modules
of this step are the `Oriented` family (over eighty modules, including
`OrientedActivity`, `OrientedAllNorms`, `OrientedComparison`,
`OrientedConcentration`, `OrientedGreenRates`, `OrientedKernel`,
`OrientedLaw`, `OrientedLayer` and its layer-bounds and layer-independence
companions, `OrientedLogMean`, `OrientedMoments`, `OrientedOdometer`,
`OrientedPotential`, `OrientedRouting` and its routing-coordinate
companions, `OrientedScaling`, `OrientedStopping` and its stopping-value
companion, `OrientedTwoMean`, `OrientedVariance`), the `Scal` family
(`ScalDyadicSnell`, `ScalNoiseModification`, `ScalOrientedChain`,
`ScalOrientedScalingChain`, `ScalParabolicScaling`, `ScalScalingDischarge`,
`ScalSpatialScalingChain`, `ScalSpatialSnell`, `ScalWhiteNoise`) that
carries the continuum scaling argument, the binomial family
(`BernsteinRange`, `BinomialConvolution`, `BinomialDelay`,
`BinomialMoments`, `BinomialNorm`) for `lem:shift`'s Fourier computation,
and the `Coordinate` family (`CoordinateConditional`,
`CoordinateErasedSpace`, `CoordinateErasure`, `CoordinateFactor`,
`CoordinateFiltration`, `CoordinateMartingale`, `CoordinateProductFactor`)
shared with the product-space machinery of `lem-product`.

### Where the Lean route differs

`lem-one-particle` and `lem-tagged-monotonicity` are transcribed against the
particle-driven construction of `Parking/Support/Particle.lean`, not the
stack construction of `sec:model`: the paper's coupling gives every shared
particle the same walk and the same uniform variables, which the stack
construction cannot express, since adding a particle at a site changes which
instruction every later departure from that site reads. `lem-parallel` and
`lem-pathwise-comparison` carry the additional hypothesis that a
realization's instructions are neighbours of the site carrying them, part
of what "realization" means; without it a particle could stand at a site it
is not a candidate for. `lem-deferred`'s first clause carries the same
neighbour hypothesis; its second, used by `lem-w-martingale`, is stated
almost surely rather than pathwise, since a realization violating it is
null. `lem-exposure`'s measurability clause is likewise almost sure.
`lem-transport`'s exchangeability clause and its last display are stated
conditionally and jointly, respectively, on the event `{η(0)=k}`, since the
unconditional form is false. `lem-product`'s hypothesis
`RelabelInvariant`, unspecified further by the paper, is the conjunction of
symmetry in the particles present at a site and dependence only on data
those particles carry, both asked for only at realizations with pairwise
distinct uniform variables, since the model breaks ties of equal rank by
label order. `lem-critical-density` and `thm-four-sparse` transcribe the
paper's `liminf_t t S_t ≥ c` as the eventual bound `∀ᶠ t, c ≤ t S_t`,
since a real `liminf` of an a priori unbounded quantity is a junk value
zero in Lean and would otherwise be trivially satisfiable;
`thm-trichotomy`'s own `liminf` is kept real because a preceding conjunct
bounds the same quantity above for the same law. `thm:nearest` and
`thm:nearest-counterexample`'s distances are the graph (`ℓ^1`) distance the
paper fixes at `parking.tex:588-601`, not the sup norm. `prop:oriented-scaling`
asserts the limit exists and is measurable, rather than characterizing it,
since the paper defines it inside its own proof.

## Part C. The cited inputs

Each cited input is a proposition-valued definition under
`Parking/External/`, stated in the paper's vocabulary and carried as an
explicit hypothesis of the frozen statements that use it.

`Parking.External.SandpileGrowth` transcribes Theorem 1.3, Corollary 6.2,
Theorem 6.6 and equation (94) of Bou-Rabee-Panagiotis, *Quantitative
explosion and percolation of the divisible sandpile*: the mean divisible
sandpile odometer's growth rate in every dimension. It is consumed by
`thm-upper`, `thm-master`, `cor-growth`, `prop-discrepancy`,
`thm-four-sparse`, `thm-trichotomy`, `prop-everyone-settles`,
`lem-mean-horizon`, `prop-near-divisible`, `thm-near`,
`prop-spatial-scaling`, `thm-nearest`.

`Parking.External.Bernstein` transcribes Pinelis, Theorems 4.1 and 3.3: the
Rosenthal-Burkholder martingale moment bound and its Bernstein form under a
factorial moment condition. It is consumed by `prop-w-moment`, `thm-upper`,
`thm-master`, `cor-growth`, `prop-discrepancy`, `thm-trichotomy`,
`lem-nearest-one-point`, `prop-nearest-two-hole`,
`thm-nearest-counterexample`, `prop-everyone-settles`, `thm-near`,
`prop-spatial-scaling`, `thm-oriented-walk`, `thm-nearest`.

`Parking.External.UConcentration` transcribes the same paper's Remark 3.4:
the translation-invariant-kernel concentration estimate. It is consumed by `thm-upper`,
`thm-master`, `cor-growth`, `prop-discrepancy`, `thm-trichotomy`,
`prop-everyone-settles`, `lem-mean-horizon`, `prop-near-divisible`,
`thm-near`, `prop-spatial-scaling`, `thm-oriented-walk`, `thm-nearest`.

`Parking.External.GreenNorms` transcribes the same paper's Section 3.1: the
collected Green-function rates `‖g_n‖_2` and `max_x g_n(x)`. It is consumed
by `thm-upper`, `thm-master`, `cor-growth`, `prop-discrepancy`,
`thm-trichotomy`, `prop-everyone-settles`, `lem-mean-horizon`,
`prop-near-divisible`, `thm-near`.

`Parking.External.Stopping` transcribes Theorem 3.2 of
Bou-Rabee-Peres-Sava-Huss, *Divisible sandpiles via random walks in random
scenery*: the optimal-stopping representation of the divisible sandpile
odometer. It is `SEALED`, discharged from the shared library. It is
consumed by `thm-four-sparse`, `thm-trichotomy`,
`lem-mean-horizon`, `prop-near-divisible`, `thm-near`.

`Parking.External.GreenGradient` transcribes Lawler-Limic, Section 2.3: the
gradient bound on the truncated Green function of the simple walk. It is
`SEALED`, discharged from the shared library's truncated-walk Green
estimate. It is consumed by `lem-gamma-sum`.

`Parking.External.DonskerVaradhanRange` transcribes Theorem 1 of
Donsker-Varadhan, *On the number of distinct sites visited by a random
walk*: the large-deviation rate for the range of a symmetric random walk,
specialized to the simple random walk. It is consumed by
`thm-subcritical-tail`.

`Parking.External.OrientedStoppingStability` and
`Parking.External.BinomialLocalCLT` are the two cited inputs of
`prop-oriented-scaling`'s proof: the stability of optimal-stopping values
under uniform convergence of uniformly bounded rewards together with
finite-dimensional convergence of the driving walk, of the kind of Coquet
and Toldo, Theorem 3 and Corollary 4, and the binomial local central limit
theorem, Lawler-Limic Theorem 2.1.1. They are consumed by
`prop-oriented-scaling` and `thm-oriented-walk`.

`Parking.External.VarianceScale`, `Parking.External.MultivariateBerryEsseen`
and `Parking.External.CriticalScaleLowerTail` transcribe the variance-scale
and multivariate Berry-Esseen hypotheses and the critical-scale lower-tail
estimate of Bou-Rabee and Panagiotis, cited at `parking.tex:1807-1833`. They
are consumed by `thm-nearest`.

What is deliberately not assumed: the paper's own theorems are not
hypotheses of one another beyond the citation chain the paper itself
states. `thm-master`'s upper bound is `thm-upper` and its lower bound is
`lem-critical-density`; `cor-growth`, `thm-trichotomy`, `prop-discrepancy`
and `thm-four-sparse` build on `thm-master` and `cor-growth`;
`thm-subcritical-tail` builds on `thm-subcritical`, `lem-range-lower` and
`lem-product`; `thm-near` builds on `prop-near-divisible`,
`lem-mean-horizon`, `lem-near-tilt` and `prop-resolvent`; `thm-oriented-walk`
builds on `thm-oriented` and `prop-oriented-scaling`; `thm-nearest` builds
on `prop-spatial-scaling` and the critical-scale lower tail. No statement
assumes the conclusion of a later statement, and the two open nodes,
`prop-spatial-scaling` and `prop-oriented-scaling`, are exactly the two
places this chain is not yet closed.

This description matches the Lean tree it accompanies; the registered
declarations are checked against `ledger/manifest.yaml` by
`tools/check_manifest.py`.
