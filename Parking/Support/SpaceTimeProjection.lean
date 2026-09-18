/- Spatial tests obtained by integrating space-time tests in time. -/
import Parking.Support.Continuum
import Parking.Generic.CompactTimeIntegral

open MeasureTheory
noncomputable section
namespace Parking
variable {d : ℕ}

/-- The source coordinate of a space-time weak equation is a valid spatial test. -/
theorem isTestFun_timeIntegral {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ) :
    IsTestFun (fun x => ∫ s : ℝ, ψ (s, x)) :=
  ⟨Generic.CompactTimeIntegral.contDiff hψ.1 hψ.2.1,
    Generic.CompactTimeIntegral.hasCompactSupport hψ.2.1⟩

/-- Each time slice of a space-time test is a spatial test. -/
theorem isTestFun_spaceSlice {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : IsSpaceTimeTest ψ) (s : ℝ) : IsTestFun (fun x => ψ (s, x)) := by
  refine ⟨hψ.1.comp (contDiff_const.prodMk contDiff_id), ?_⟩
  apply HasCompactSupport.intro (hψ.2.1.isCompact.image continuous_snd)
  intro x hx
  apply image_eq_zero_of_notMem_tsupport
  intro hp
  exact hx ⟨(s, x), hp, rfl⟩

end Parking
