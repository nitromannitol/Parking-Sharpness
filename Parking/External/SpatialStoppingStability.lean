/-
External input: the stability of optimal-stopping values under uniform convergence of
uniformly bounded rewards, together with the invariance principle for the stopped simple
random walk, in the form the paper's proof of `prop:spatial-scaling` cites at
`parking.tex:1741-1752`: "The argument
proving the parabolic scaling limit in BP, with the time variable and scenery retained, gives
the joint convergence of `(η_R,ū_R)`.  Its estimates are uniform on compact time intervals."

BP's own proof (Subsection 4.2, pages 27-28, `Parking.External.SpatialFixedTimeTightness`'s
docstring) obtains the joint convergence from Proposition 4.3 (the linear membrane field
converges locally uniformly on `[0,T]×ℝ^d`) composed with the stability of optimal-stopping
values under uniform convergence of bounded rewards: Coquet and Toldo, *Convergence of values
in optimal stopping and convergence of optimal stopping times*, Electronic Journal of
Probability 12 (2007), 207-228, Theorem 3 and Corollary 4 — the SAME citation
`Parking.External.OrientedStoppingStability` already uses for the oriented node, applied via
BP's Lemma 2.5 (`u_t = V_t + sup_{τ≤t} E_x[-V_{t-τ}(X_τ)]`, transcribed for the simple random
walk in `Parking/Support/Terminal.lean`'s `u_eq_potential_add_stoppingSup`).  Coquet-Toldo's
theorem is a general fact about optimal-stopping values under convergence of the driving
process and of the rewards; it is not specific to a one-dimensional state space, so this is
the SAME cited theorem as `Parking.External.OrientedStoppingStability`, transcribed for a
`(Fin d → ℝ)`-valued driving process instead of a real-valued one, exactly as `Parking.
External.OrientedStoppingStability`'s own docstring anticipates ("this is the boundary the
design of this External was chosen to sit on").

This result is assumed here, not proved.

WHAT IS ASSUMED AND WHAT IS NOT, mirroring `Parking.External.OrientedStoppingStability`
verbatim with `d` in place of the fixed oriented dimension `2` and `EuclideanSpace ℝ (Fin d)`
in place of `ℝ`.  Only the STABILITY step is assumed: for a fixed bounded continuous limit
reward `G` and fixed uniformly bounded rewards `G' n` converging to `G` uniformly on `[0,T] ×
(Fin d → ℝ)`, the discrete optimal-stopping values of the simple random walk converge to the
Brownian optimal-stopping value.  Nothing about the scenery, the linear membrane field, or the
joint law of `(V, B)` is assumed: the finite-dimensional convergence of the rescaled walk to
`B` is a hypothesis, discharged elsewhere by the invariance principle for the simple random
walk, not by this Prop.

MODELLING.

- The discrete value is `Parking.stoppingSup`, the supremum of `E_x F(σ, X_σ)` over the
  stopping times of the simple random walk bounded by the horizon, at the terminal reward `F`
  (`Parking.u_eq_potential_add_stoppingSup` is the Dynkin identity that produces a
  reward of exactly this shape, `-V_{n-σ}`, mirroring `Parking.orientedStopValue_eq_potential`
  for the oriented walk).
- The rescaled site is `Parking.spatialScaledSite n z = z / √n`, the CLT scaling that inverts
  `barDivisible`'s own `⌊Rx⌋` at `R = √n`; the elapsed time is read at `k/n`, exactly as
  `Parking.orientedScaledSite`/the elapsed-time convention of `Parking.External.
  OrientedStoppingStability` does for the oriented walk.
- The Brownian motion is `LatticeProb.IsBrownianSpace d 0 B PB`: generator `Δ/(2d)`, matching
  `parking.tex`'s `L = (2d)^{-1}Δ` and the diffusion rate of the simple random walk (each
  coordinate changes with probability `1/d` per step).  Its driving space is `EuclideanSpace ℝ
  (Fin d)`; `Parking.ofBrownianSpace` reads it in the paper's own `Fin d → ℝ` vocabulary.
  `LatticeProb.exists_isBrownianSpace_cont` proves one with every path continuous exists, so
  the hypothesis is not vacuous.
- A stopping time of `B` is recorded by Galmarino's criterion, `Parking.IsSpatialContStopping`,
  the `Fin d`-dimensional analogue of `Parking.IsContStopping`.

WHY THE UNIFORM CONVERGENCE IS OVER ALL OF `[0,T] × (Fin d → ℝ)`.  Exactly as for
`Parking.External.OrientedStoppingStability`: the application supplies the reward through a
spatial cutoff vanishing outside a fixed compact set, so the difference of the two rewards is
supported there, and the global form assumes strictly less than the local-uniform form the
cited estimates need.

WHY THE WALK'S CONVERGENCE IS A HYPOTHESIS AND NOT PART OF THE INPUT.  Exactly as for
`Parking.External.OrientedStoppingStability`: read at `G' n = G`, the statement would otherwise
assert the full invariance principle for the simple random walk, which `parking.tex:1741-1752`
attributes to BP's own argument, not to this cited stability estimate.

WHAT THE STATEMENT DOES NOT GIVE.  The rewards themselves (the prefactor, the variance, the
membrane field are the caller's), the convergence of the rewards (the caller's own binomial or
local-CLT argument), and the cutoff level (fixed, exactly as for the oriented node, because the
unbounded field is a.s. unbounded in space).

QUANTIFIER ORDER.  The dimension first (`prop:spatial-scaling`'s own range `1 ≤ d ≤ 3`), then
the Brownian realization, then the horizon `T`, then the walk's convergence, then the common
bound `M`, then the limit reward and the approximating family, then the accuracy, then the
threshold — the same order as `Parking.External.OrientedStoppingStability`, with the dimension
bound first because the paper fixes `d` before every other quantity of `prop:spatial-scaling`.

VACUITY.  Both values are real `sSup`s.  Neither junk value (`sSup ∅ = 0`, `sSup` of an
unbounded set `= 0`) can fire: the rule that stops at once is admissible on both sides, so both
sets of payoffs are nonempty (`Parking.zero_mem_spatialContPayoffs`,
`Parking.stopValues`/`Parking.stoppingSup_le`), and both rewards are bounded by `M`, so both
sets are bounded above by `M` (`Parking.spatialContValue_le`, `Parking.stoppingSup_le`).  The
Brownian hypothesis is not vacuous: `LatticeProb.exists_isBrownianSpace_cont` (checked at
`d = 1, 2, 3`, the paper's own range) produces a witness.  The statement is therefore a genuine
assertion about two suprema, not satisfiable through a junk value.
-/
import Parking.Support.ContSpatialValue
import Parking.Support.Terminal
import Parking.External.OrientedStoppingStability

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
/-- Stability of optimal-stopping values under uniform convergence of uniformly bounded
rewards, with the invariance principle for the stopped simple random walk
(`parking.tex:1741-1752`; the cutoff and stability estimates of the parabolic scaling limit in
the cited companion paper, of the kind of Coquet-Toldo, Theorem 3 and Corollary 4, the SAME
citation as `Parking.External.OrientedStoppingStability`, transcribed here for a
`(Fin d → ℝ)`-valued driving process).  Assumed, not proved. -/
def Parking.External.SpatialStoppingStability : Prop :=
  ∀ (d : ℕ), 1 ≤ d → d ≤ 3 →
    ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)),
      LatticeProb.IsBrownianSpace d 0 B PB →
    ∀ T : ℝ, 0 < T →
      (∀ (m : ℕ) (ts : Fin m → ℝ), (∀ i, ts i ∈ Set.Icc (0 : ℝ) T) →
        ∀ F : BoundedContinuousFunction (Fin m → (Fin d → ℝ)) ℝ,
          Tendsto (fun n : ℕ =>
              ∫ p, F (fun i => Parking.spatialScaledSite n
                  (Parking.walkPath (0 : Parking.Site d) p ⌊(n : ℝ) * ts i⌋₊))
                ∂(Parking.walkLaw d)) atTop
            (𝓝 (∫ β, F (fun i => Parking.ofBrownianSpace B (Real.toNNReal (ts i)) β) ∂PB))) →
    ∀ M : ℝ, 0 ≤ M →
    ∀ G : ℝ → (Fin d → ℝ) → ℝ, Continuous (fun p : ℝ × (Fin d → ℝ) => G p.1 p.2) →
      (∀ s (y : Fin d → ℝ), |G s y| ≤ M) →
    ∀ G' : ℕ → ℝ → (Fin d → ℝ) → ℝ, (∀ (n : ℕ) s (y : Fin d → ℝ), |G' n s y| ≤ M) →
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : Fin d → ℝ, |G' n s y - G s y| ≤ ε) →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |Parking.stoppingSup d
            (fun (k : ℕ) (z : Parking.Site d) =>
              G' n ((k : ℝ) / n) (Parking.spatialScaledSite n z))
            ⌊(n : ℝ) * T⌋₊ (0 : Parking.Site d) -
          Parking.spatialContValue (Parking.ofBrownianSpace B) PB G T| ≤ ε
-- FROZEN-STATEMENT-END
