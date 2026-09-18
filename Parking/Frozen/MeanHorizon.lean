/-
Lemma 11.3 of parking.tex, frozen.  `parking.tex:2764-2770` (label
`lem:mean-horizon`), in the setting of `parking.tex:2729-2763` ($\xi_\delta
\coloneqq\eta_\delta+\delta$, and $\phi_d(s)=(s+1)^{(4-d)/4}$ for $d\leq3$,
$\log(s+2)$ for $d\geq4$):

  "Conditionally on $\xi_\delta$, let $\sigma$ be a bounded stopping time for
   the walk.  If $M=\E\sigma$, then
   $\E\sum_{j<\sigma}\xi_\delta(X_j)\leq C\phi_d(M)$."

"Conditionally on $\xi_\delta$" makes the stopping rule a function of the
configuration as well as of the walk; it is a stopping time for the natural
filtration of the walk for each configuration, and it is bounded by one
horizon `n` uniformly.  A stopping time is measurable, in the walk for each
configuration and in the configuration for each walk, so that both expectations
below are expectations of genuine random variables.  Both average over the
configuration and the walk.  The three results the proof quotes without proving
them here enter as explicit hypotheses.  Their finiteness is asserted alongside the bound,
so that an undefined integral cannot satisfy it through its junk value.

Step 1 of the paper's proof cites `eq:green-norms` at `parking.tex:2790` to read
the concentration term as a multiple of the scale, so standing ruling R1 attaches
`Parking.External.GreenNorms` as a fourth explicit hypothesis.
-/
import Parking.Support.MeanHorizonProof
import Parking.External.SandpileGrowth
import Parking.External.Stopping
import Parking.External.UConcentration
import Parking.External.GreenNorms

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.mean_horizon (hGrowth : Parking.External.SandpileGrowth)
    (hStopping : Parking.External.Stopping)
    (hConcentration : Parking.External.UConcentration)
    (hGreen : Parking.External.GreenNorms) (d : ℕ) (hd : 1 ≤ d) (δ₀ : ℝ) (ν : ℝ → Measure ℤ)
    (θ M K : ℝ) (hfam : Parking.NearFamily δ₀ ν θ M K) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Icc (0 : ℝ) δ₀, ∀ n : ℕ,
      ∀ σ : (Parking.Site d → ℤ) → (ℕ → Parking.Site d) → ℕ,
        (∀ η, LatticeProb.IsWalkStopping (σ η)) → (∀ η X, σ η X ≤ n) →
        (∀ X, Measurable fun η => σ η X) →
        ∀ Mσ : ℝ, Mσ = ∫ η, ∫ X, (σ η X : ℝ) ∂(LatticeProb.siteWalkLaw d 0)
            ∂(LatticeProb.iidLaw d (ν δ)) →
          Integrable (fun η => ∫ X, ∑ j ∈ Finset.range (σ η X),
              Parking.xi δ η (X j) ∂(LatticeProb.siteWalkLaw d 0))
              (LatticeProb.iidLaw d (ν δ)) ∧
            ∫ η, ∫ X, ∑ j ∈ Finset.range (σ η X),
                Parking.xi δ η (X j) ∂(LatticeProb.siteWalkLaw d 0)
                ∂(LatticeProb.iidLaw d (ν δ))
              ≤ C * Parking.phi d Mσ
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨C, hC, hbound⟩ :=
    Parking.exists_meanHorizon (d := d) hd hGrowth hStopping hConcentration hGreen hfam
  exact ⟨C, hC, hbound⟩
