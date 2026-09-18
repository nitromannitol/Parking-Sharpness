/- Coordinatewise versions preserve the white-noise laws. -/
import Parking.Support.SpatialResidualAlgebra

open MeasureTheory ProbabilityTheory Filter Topology
noncomputable section
namespace Parking
variable {d : ℕ}

theorem isSpatialWhiteNoise_congr {Ω : Type} [MeasurableSpace Ω]
    {Q : Measure Ω} {v : ℝ} {W W' : ((Fin d → ℝ) → ℝ) → Ω → ℝ}
    (hW : IsSpatialWhiteNoise d v Q W)
    (heq : ∀ φ, IsTestFun φ → W' φ =ᵐ[Q] W φ) :
    IsSpatialWhiteNoise d v Q W' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro φ χ hφ hχ a b
    have htest : IsTestFun (fun x => a * φ x + b * χ x) :=
      ⟨(contDiff_const.mul hφ.1).add (contDiff_const.mul hχ.1),
        hφ.2.mul_left.add hχ.2.mul_left⟩
    filter_upwards [heq _ htest, heq φ hφ, heq χ hχ, hW.1 φ χ hφ hχ a b]
      with ω hsum hφω hχω hlin
    simpa only [hsum, hφω, hχω] using hlin
  · intro φ hφ
    exact ⟨(hW.2.1 φ hφ).1.congr (heq φ hφ).symm,
      (integral_congr_ae (heq φ hφ)).trans (hW.2.1 φ hφ).2⟩
  · intro φ χ hφ hχ
    have hprod : (fun ω => W' φ ω * W' χ ω) =ᵐ[Q] fun ω => W φ ω * W χ ω :=
      (heq φ hφ).mul (heq χ hχ)
    exact ⟨(hW.2.2.1 φ χ hφ hχ).1.congr hprod.symm,
      (integral_congr_ae hprod).trans (hW.2.2.1 φ χ hφ hχ).2⟩
  · intro φ hφ
    obtain ⟨s, hs, hmap⟩ := hW.2.2.2 φ hφ
    exact ⟨s, hs, (Measure.map_congr (heq φ hφ)).trans hmap⟩

end Parking
