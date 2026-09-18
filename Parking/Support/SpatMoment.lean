/-
The `r`-th moment norm of the divisible odometer at an arbitrary site, from the
norm at the origin by the translation invariance of the scenery law.

This is the site-uniform form of `Parking.exists_uNormReal_le`
(`Parking/Support/UConcReal.lean`), the input the Kolmogorov route to the
equicontinuity clause of `prop:spatial-scaling` needs at every site.
-/
import Parking.Support.UConcReal
import Parking.Support.BlockTools
import Parking.Support.SpatShift

noncomputable section
namespace Parking
open MeasureTheory LatticeProb

variable {d : ℕ}

/-- The `r`-th moment norm of `u_n(x)` under the i.i.d. law is bounded by the
mean odometer plus the same constant as at the origin. -/
theorem exists_uNormReal_le_site (hd : 1 ≤ d) (hConc : Parking.External.UConcentration)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {θ : ℝ} (hθ : 0 < θ)
    (hexpabs : Integrable (fun z : ℝ => Real.exp (θ * |z|)) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ r : ℝ, 2 ≤ r → ∀ x : Site d,
      ((∫ η, |u η n x| ^ r ∂(iidLaw d ν)) ^ (1 / r))
        ≤ External.meanSandpileReal d ν n
          + C * (Real.sqrt r * l2Norm (green d n) + r * greenMax d n) := by
  obtain ⟨C, hC, hCle⟩ := Parking.exists_uNormReal_le hd hConc ν hθ hexpabs
  refine ⟨C, hC, fun n hn r hr x => ?_⟩
  have hg : Measurable (fun ξ : Site d → ℝ => |u ξ n 0| ^ r) := ((measurable_u_eval n 0).abs).pow_const r
  have h1 : ∫ η, |u η n x| ^ r ∂(iidLaw d ν)
      = ∫ η, |u (fun z => η (z + x)) n 0| ^ r ∂(iidLaw d ν) :=
    integral_congr_ae (Filter.Eventually.of_forall fun η => by simp only [Parking.u_shift hd η n x 0, zero_add])
  have h2 : ∫ η, |u (fun z => η (z + x)) n 0| ^ r ∂(iidLaw d ν)
      = ∫ η, |u η n 0| ^ r ∂(iidLaw d ν) :=
    Parking.integral_shift_iidLaw ν x hg
  rw [h1, h2]
  exact hCle n hn r hr

end Parking

end