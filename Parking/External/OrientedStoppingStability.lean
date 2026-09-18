/-
External input: the stability of optimal-stopping values under uniform
convergence of uniformly bounded rewards, together with the invariance principle
for the stopped oriented walk, in the form the paper cites at
`parking.tex:3199-3203`.

The proof of `prop:oriented-scaling` (`parking.tex:3162-3222`) builds the limit
`U(T) = Z_T(0,0) + sup_{τ≤T} E_0[-Z_T(τ,B_τ)]` and then says verbatim:

  "Identify layer $\ell$ with the sites $(-j,j-\ell)$, $j\in\mathbb Z$.  The
   rescaled scenery
   $n^{-3/4}\sum_{\ell\geq0}\sum_{j\in\mathbb Z}\eta(-j,j-\ell)\,
   \delta_{(\ell/n,(j-\ell/2)/\sqrt n)}$
   converges in law as a random distribution to $\sqrt{\Var\eta(0)}W$.  The
   binomial local central limit theorem gives convergence of the convolved
   potentials, and the rescaled $\vec P$-walk converges to $B$.  The cutoff and
   stability estimates in the proof of the parabolic scaling limit in
   \citet{BP} use only heat-kernel bounds and bounds on translated kernel
   differences.  Equation~\eqref{eq:oriented-heat} and
   Lemma~\ref{lem:shift} give those bounds here.  The cited cutoff and
   stability estimates therefore prove the displayed convergence."

The cited source is Bou-Rabee and Panagiotis (`BP` in the paper), whose
parabolic scaling limit contains the cutoff and stability estimates; those
estimates are of the same kind as Coquet and Toldo, *Convergence of values in
optimal stopping and convergence of optimal stopping times*, Electronic Journal
of Probability 12 (2007), 207-228, Theorem 3 and Corollary 4: if the driving
processes converge in law and the rewards are uniformly bounded and converge
uniformly, the values of the finite-horizon optimal-stopping problems converge.

This result is assumed here, not proved.

WHAT IS ASSUMED AND WHAT IS NOT.  Only the STABILITY step is assumed: for a
fixed bounded continuous limit reward `G` and fixed uniformly bounded rewards
`G' n` converging to `G` uniformly, the discrete optimal-stopping values of the
oriented walk converge to the Brownian optimal-stopping value.  Nothing about
the scenery, about the white noise, or about the joint law of `(W,B)` is
assumed: the three inputs the paper lists (the rescaled scenery converges to
white noise, the binomial local central limit theorem, the rescaled oriented
walk converges to `B`) are statements the repository discharges about the
particular rewards, not hypotheses of this Prop.  This is the boundary the
design of this External was chosen to sit on: an implication whose hypotheses
were those three inputs and whose conclusion was the convergence of the
odometer would hide inside itself the joint convergence and independence of
`(W,B)`, the `L^2` structure the cited proof uses, and the stability of the
optimal-stopping functional, which is the cited estimate itself.

MODELLING.

- The discrete value is `Parking.orientedStoppingSup`, the supremum of
  `E_x F(σ, X_σ)` over the stopping times of the oriented walk bounded by the
  horizon, at the terminal reward `F`.  That the oriented odometer is such a
  value is `Parking.isLUB_orientedStopValues` together with the Dynkin identity
  `Parking.orientedStopValue_eq_potential`, both proved here; the reward the
  paper's proof produces is `-Φ_{n-σ}(X_σ)` rescaled, and it is a reward of
  exactly this shape.
- The ELAPSED time is the first argument of both rewards.  The discrete reward
  is read at the rescaled elapsed time `k/n` and the rescaled site
  `Parking.orientedScaledSite n z = (z₂-z₁)/(2√n)`, and the Brownian value
  `Parking.contValue B PB G T` is the supremum of `E_0 G(τ, B_τ)` over the
  stopping times of `B` bounded by `T`, again with `τ` the elapsed time.  The
  limit field `Z_T(s,x)` of `parking.tex:3177-3180` also carries the elapsed
  time as its first argument, since it integrates the noise over `r ∈ (s,T)`;
  `Parking.contStopValue_eq_contValue` reads the paper's value as a
  `Parking.contValue`.  A reward that the paper writes with the REMAINING time
  is read here at the elapsed time `k/n` with the horizon subtracted inside it,
  so that the two sides of the statement are the same problem.  Along an
  oriented trajectory the layer index `ℓ(z) = -(z₁+z₂)` equals the number of
  steps, so the pair (elapsed time, rescaled site) determines the site, and a
  reward of the paper's shape is indeed a function of that pair.
- Brownian motion is `Parking.IsQuarterBrownian`: `2B` is a real Brownian
  motion, so `Var(B_t) = t/4`, which is the normalization of
  `parking.tex:3175`.  It starts at zero, since a pre-Brownian process vanishes
  at zero almost surely.  Mathlib 4.32 has a construction of a real Brownian
  motion but the statement is quantified over a space carrying one, as every
  other continuum statement of the repository is.
- A stopping time of `B` is recorded by Galmarino's criterion
  (`Parking.IsContStopping`), as in the companion divisible-sandpile repository.

WHY THE UNIFORM CONVERGENCE IS OVER ALL OF `[0,T] × ℝ`.  The cited estimates
need only uniform convergence on compact sets, at the price of a tightness bound
for the stopped rescaled walk.  The application supplies the stronger, global
form for free, because both rewards carry the continuous cutoff
`Parking.spatialCutoff A`, which vanishes for `|y| ≥ 2A`: the DIFFERENCE of the
two rewards is supported in a fixed compact set, on which local uniform
convergence is uniform.  Assuming the global form therefore assumes strictly
less, and leaves the tightness of the stopped walk out of the cited input.

WHY THE WALK'S CONVERGENCE IS A HYPOTHESIS AND NOT PART OF THE INPUT.  Without it the
statement, read at `G' n = G`, would assert that the rescaled oriented walk's
optimal-stopping values converge to the Brownian ones for EVERY bounded continuous reward,
which is a full invariance principle for the stopped walk and is one of the three inputs the
paper lists as its own ("the rescaled `P⃗`-walk converges to `B`").  It is therefore a
hypothesis here, in the finite-dimensional form the binomial local central limit theorem
gives: the rescaled position after `⌊n t⌋` steps, at finitely many times of `[0,T]`,
converges in distribution to `B` at those times, tested against bounded continuous functions.
What the cited estimates then supply, and all they supply, is the passage from that
convergence of the walk, and the uniform convergence of the rewards, to the convergence of
the VALUES: the tightness of the stopped walk and the stability of the optimal-stopping
functional.  That is the content of `parking.tex:3199-3203`.

WHAT THE STATEMENT DOES NOT GIVE.  Three things are deliberately outside it, and the
repository owes each of them.

- The rewards themselves.  The prefactor `n^{-1/4}`, the factor `√(Var η(0))` and the
  potential field are baked into `G'` and `G` by the caller; the Prop is agnostic about
  them.  So it is the STABILITY step and nothing more, and it must never be cited as the
  displayed convergence of `prop:oriented-scaling`.
- The convergence of the rewards.  `G' n → G` uniformly is a HYPOTHESIS here.  It is the
  paper's "the binomial local central limit theorem gives convergence of the convolved
  potentials", which the repository is to prove.
- The cutoff level.  Both rewards are bounded by one `M`, and the unbounded field is not:
  conditionally on the noise, `Z_T(s,·)` is a Gaussian field on the line and is almost
  surely unbounded in space.  So the Prop can only ever be applied at a FIXED cutoff level
  `A`, with both rewards vanishing outside `|y| ≤ 2A`, and the passage from the truncated
  values to `U(T)` as `A → ∞` is a separate argument, which is what the `L^r` bound
  `Parking.exists_uOriented_two_moment` at a fixed `r > 4` is for.  Uniform convergence over
  all of `ℝ` is available exactly because `A` is fixed; with cutoff levels growing with `n`
  it would fail, and the compact-uniform form with a tightness bound for the stopped walk
  would be needed instead.

QUANTIFIER ORDER.  The Brownian realization comes first, then the horizon `T`
(the convergence of the rewards is only ever used on `[0,T]`), then the common
bound `M`, then the limit reward and the approximating family, then the
accuracy, and last the threshold.  The threshold therefore depends on the
Brownian law, the horizon, the bound, the two rewards and the accuracy, and on
nothing else.

VACUITY.  Both values are real `sSup`s.  A real `sSup` of the empty set, or of
a set unbounded above, is zero.  Neither junk value can fire under the
hypotheses: the rule that stops at once is admissible on both sides, so both
sets are nonempty, and both rewards are bounded by `M`, so both sets are bounded
above by `M`.  The statement is therefore a genuine assertion about two
suprema and not satisfiable through a junk value.
-/
import Parking.Support.OrientedTerminal
import Parking.Support.OrientedScaling
import Parking.Support.ContStopGeneral
import Parking.Support.SpatialCutoff

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
/-- Stability of optimal-stopping values under uniform convergence of uniformly
bounded rewards, with the invariance principle for the stopped oriented walk
(`parking.tex:3199-3203`; the cutoff and stability estimates of the parabolic
scaling limit in the cited companion paper, of the kind of Coquet-Toldo,
Theorem 3 and Corollary 4).  Assumed, not proved. -/
def Parking.External.OrientedStoppingStability : Prop :=
  ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
      (B : ℝ≥0 → ΩB → ℝ), Parking.IsQuarterBrownian B PB →
    ∀ T : ℝ, 0 < T →
      (∀ (m : ℕ) (ts : Fin m → ℝ), (∀ i, ts i ∈ Set.Icc (0 : ℝ) T) →
        ∀ F : BoundedContinuousFunction (Fin m → ℝ) ℝ,
          Tendsto (fun n : ℕ =>
              ∫ p, F (fun i => Parking.orientedScaledSite n
                  (Parking.orientedPath (0 : Parking.Site 2) p ⌊(n : ℝ) * ts i⌋₊))
                ∂(Parking.walkLaw 2)) atTop
            (𝓝 (∫ β, F (fun i => B (Real.toNNReal (ts i)) β) ∂PB))) →
    ∀ M : ℝ, 0 ≤ M →
    ∀ G : ℝ → ℝ → ℝ, Continuous (fun p : ℝ × ℝ => G p.1 p.2) →
      (∀ s y : ℝ, |G s y| ≤ M) →
    ∀ G' : ℕ → ℝ → ℝ → ℝ, (∀ (n : ℕ) (s y : ℝ), |G' n s y| ≤ M) →
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : ℝ, |G' n s y - G s y| ≤ ε) →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |Parking.orientedStoppingSup 2
            (fun (k : ℕ) (z : Parking.Site 2) =>
              G' n ((k : ℝ) / n) (Parking.orientedScaledSite n z))
            ⌊(n : ℝ) * T⌋₊ (0 : Parking.Site 2) -
          Parking.contValue B PB G T| ≤ ε
-- FROZEN-STATEMENT-END
