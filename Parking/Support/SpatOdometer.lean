/-
The `r`-th moment norm of the divisible odometer `uOf` at an arbitrary site,
under the full data law, from the scenery-only bound at the same site.

This combines `Parking.uOf_eq_u_xi_zero` (the odometer reads the recentred
scenery), `Parking.law_map_confReal` (the configuration read in the reals has
the i.i.d. law), `Parking.integral_shift_iidLaw` (translation invariance) and
`Parking.exists_uNormReal_le_site` (the moment norm at an arbitrary site).

The constant is uniform in the site and in the horizon, which is what the
Kolmogorov route to the equicontinuity clause of `prop:spatial-scaling`
consumes: the rescaled divisible odometer is `uOf` read at the lattice points
of a compact set, and the Kolmogorov condition needs the moment norm at every
site of that set with one constant.
-/
import Parking.Support.SpatMoment
import Parking.Support.UConcBridge
import Parking.Support.NearBridge
import Parking.Support.CriticalLawReal

noncomputable section
namespace Parking
open MeasureTheory LatticeProb

variable {d : ℕ}

/-- The `r`-th moment norm of `uOf ω n x` under the data law is bounded by the
mean odometer plus the same constant as at the origin. -/
theorem exists_uOfNorm_le_site (hd : 1 ≤ d) (hConc : Parking.External.UConcentration)
    (ν : Measure ℤ) [IsProbabilityMeasure ν] {θ : ℝ} (hθ : 0 < θ)
    (hexpabs : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ r : ℝ, 2 ≤ r → ∀ x : Site d,
      ((∫ ω, |uOf ω n x| ^ r ∂(law d ν)) ^ (1 / r))
        ≤ External.meanSandpileReal d (realLaw ν) n
          + C * (Real.sqrt r * l2Norm (green d n) + r * greenMax d n) := by
  have hexp' : Integrable (fun z : ℝ => Real.exp (θ * |z|)) (realLaw ν) := by
    have := (integrable_map_measure (g := fun z : ℝ => Real.exp (θ * |z|))
      (f := fun k : ℤ => (k : ℝ)) (by fun_prop) (by fun_prop)).2 hexpabs
    show Integrable (fun z => Real.exp (θ * |z|)) (Measure.map (fun k : ℤ => (k : ℝ)) ν)
    simpa only [Function.comp_def] using this
  obtain ⟨C, hC, hCle⟩ := exists_uNormReal_le_site hd hConc (realLaw ν) hθ hexp'
  refine ⟨C, hC, fun n hn r hr x => ?_⟩
  have hu := hCle n hn r hr x
  have hint : ∫ ω : Data d, |uOf ω n x| ^ r ∂(law d ν)
      = ∫ η : Site d → ℝ, |u η n x| ^ r ∂(iidLaw d (realLaw ν)) :=
    integral_confReal hd ν (((measurable_u_eval n x).abs).pow_const r)
  rw [hint]
  exact hCle n hn r hr x

end Parking

end