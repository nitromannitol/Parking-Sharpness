/- Integrability and linearity of compactly supported scenery pairings. -/
import Parking.Support.SpatialTimeSourceApproximation
import Parking.Support.SpatialTestedSum

open MeasureTheory LatticeProb
noncomputable section
namespace Parking
variable {d : ℕ}

theorem isTestFun_sampledTimeIntegral {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : IsSpaceTimeTest ψ) (T R : ℝ) : IsTestFun (sampledTimeIntegral ψ T R) := by
  unfold sampledTimeIntegral
  constructor
  · exact contDiff_const.mul (ContDiff.sum fun n _ => (isTestFun_spaceSlice hψ _).1)
  · apply HasCompactSupport.intro (hψ.2.1.isCompact.image continuous_snd)
    intro x hx
    have hz : ∀ s, ψ (s, x) = 0 := by
      intro s
      apply image_eq_zero_of_notMem_tsupport
      intro hp
      exact hx ⟨(s, x), hp, rfl⟩
    simp only [hz, Finset.sum_const_zero, mul_zero]

theorem integrable_scenePair_test (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) {R : ℝ} (hR : 1 ≤ R) :
    Integrable (fun w => scenePair w R φ) (law d ν) := by
  obtain ⟨B, hB, hb⟩ := exists_norm_bound_of_hasCompactSupport hφ.2
  obtain ⟨M, hM, hm⟩ := exists_norm_le_of_hasCompactSupport hφ.1.continuous hφ.2
  exact (integral_abs_scenePair_le hd ν hint hB hM hR hb hm).1

theorem scenePair_sub_test (w : Data d) {φ χ : (Fin d → ℝ) → ℝ}
    (hφ : IsTestFun φ) (hχ : IsTestFun χ) {R : ℝ} (hR : 1 ≤ R) :
    scenePair w R (fun x => φ x - χ x) = scenePair w R φ - scenePair w R χ := by
  have hφs : Summable (fun y : Site d => (w.1 y : ℝ) * φ (fun i => (y i : ℝ) / R)) :=
    summable_of_hasFiniteSupport ((hasFiniteSupport_sampledTest hφ.2 hR).mul_right _)
  have hχs : Summable (fun y : Site d => (w.1 y : ℝ) * χ (fun i => (y i : ℝ) / R)) :=
    summable_of_hasFiniteSupport ((hasFiniteSupport_sampledTest hχ.2 hR).mul_right _)
  unfold scenePair
  simp_rw [mul_sub]
  rw [hφs.tsum_sub hχs, mul_sub]

end Parking
