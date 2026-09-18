/-
`thm:nearest` from `prop:spatial-scaling`.

`parking.tex:1807-1833` proves Theorem 1.5 from Proposition 8.3 and two inputs
cited there: the critical-scale lower tail, which makes the limit field positive
at the origin at time one, and the strict positivity of its time derivative on
`{U > 0}`, which Proposition 8.3 itself asserts.  The remaining continuum step,
the positivity of the signed pair at a test function supported where the field is
positive, is `pathwise_signed_of_displays`, obtained by mollifying the two
distributional displays in time to the right of `s = 1`.

The measurability of `ω ↦ ∫ U(ω,1,x) (Lφ)(x) dx` is not one of the frozen
clauses; it follows from the measurability of `U` at each fixed point and its
continuity in the space variable, which together make the integrand jointly
measurable.
-/
import Parking.Support.NearestPathwise
import Parking.Support.NearestSigned
import Parking.Support.NearestContinuumPositivity
import Parking.Frozen.SpatialScaling
import Parking.Support.UpperTarget

open MeasureTheory Filter Topology

noncomputable section

namespace Parking

variable {d : ℕ}

/-- **The pairing of the limit field with a fixed continuous kernel is measurable.**
The integrand is jointly measurable because it is measurable in the sample and
continuous in the space variable. -/
theorem measurable_integral_potential {Ω : Type} [MeasurableSpace Ω]
    {Uc : Ω → ℝ → (Fin d → ℝ) → ℝ}
    (hUm : ∀ s x, Measurable fun ω => Uc ω s x)
    (hct : ∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2)
    {χ : (Fin d → ℝ) → ℝ} (hχ : Continuous χ) (s : ℝ) :
    Measurable fun ω => ∫ x, Uc ω s x * χ x := by
  have hjoint : Measurable
      (Function.uncurry fun (x : Fin d → ℝ) (ω : Ω) => Uc ω s x * χ x) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ω => ((hct ω).comp (continuous_const.prodMk continuous_id)).mul hχ)
      (fun x => (hUm s x).mul_const _)
  have hswap : Measurable fun p : Ω × (Fin d → ℝ) => Uc p.1 s p.2 * χ p.2 :=
    hjoint.comp measurable_swap
  exact (hswap.stronglyMeasurable.integral_prod_right').measurable

/-- **Theorem 1.5 of `parking.tex` from Proposition 8.3 and the cited inputs.** -/
theorem nearest_of_spatial_scaling (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration)
    (hGreenNorms : Parking.External.GreenNorms)
    (hOdometer : Parking.External.SpatialOdometerScaling)
    (hInterior : Parking.External.HeatInteriorRegularity)
    (hMinimum : Parking.External.HeatStrongMinimum)
    (hCompact : Parking.External.HeatCompactness)
    (hLower : Parking.External.CriticalScaleLowerTail)
    (hVar : Parking.External.VarianceScale)
    (hBerry : Parking.External.MultivariateBerryEsseen)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    Tendsto (fun t : ℕ => ((Parking.law d ν) {ω | Parking.HoleCloser ω t}).toReal)
      atTop (𝓝 0) := by
  haveI := hν.prob
  haveI := Parking.law_isProb hd ν
  obtain ⟨Ω, _, Q, _, W, Uc, v, _hwhite, hWmeas, hUm, _hvm, _hzero, hct, hmono,
    _hBrownian, hFDD, hclose, htight, hdisp1, hdisp2⟩ :=
    Parking.Frozen.spatial_scaling hGrowth hBernstein hConcentration hGreenNorms
      hOdometer hInterior hMinimum hCompact d hd hd3 ν hν
  have hpos0 : ∀ᵐ ω ∂Q, 0 < Uc ω 1 0 :=
    Parking.ae_spatial_origin_pos hLower hVar hBerry hd hd3 ν hν Q W Uc hUm hFDD
  have hWm : ∀ φ : (Fin d → ℝ) → ℝ, IsTestFun φ →
      Measurable fun ω => W φ ω + ∫ x, Uc ω 1 x * contOp d φ x := fun φ hφ =>
    (hWmeas φ hφ).add (measurable_integral_potential hUm hct (continuous_contOp hφ) 1)
  have hid : ∀ᵐ ω ∂Q, ∀ φ : (Fin d → ℝ) → ℝ, IsTestFun φ → (∀ x, 0 ≤ φ x) → φ 0 = 1 →
      (∀ x ∈ tsupport φ, 0 < Uc ω 1 x) →
      0 < W φ ω + ∫ x, Uc ω 1 x * contOp d φ x := by
    filter_upwards [hdisp1, hdisp2] with ω h1 h2
    intro φ hφ hφ0 hφ1 hsupp
    exact pathwise_signed_of_displays (Uc := Uc ω) (v := v ω) (Wf := fun ψ => W ψ ω)
      (hct ω) (hmono ω) h2.1.continuousOn h2.2.2
      (fun ψ hψ hsub => (h1 ψ hψ hsub).symm.trans (h2.2.1 ψ hψ hsub)) hφ hφ0 hφ1 hsupp
  exact nearest_of_pathwise_signed hd ν hν.prob Q W Uc hUm hct hFDD hclose htight
    hpos0 hWm hid

end Parking

end
