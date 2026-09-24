/- Conditional scenery moments of directed potential increments. -/
import Parking.Support.OrientedFinite
import Parking.Support.OrientedDelay
import Parking.Support.LinearFiniteSupport

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset

/-- The conditional scenery estimate for a prescribed directed displacement. -/
theorem exists_oriented_potential_scenery_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 2 ≤ p) (hmom : Integrable (fun z : ℝ => |z| ^ p) μ)
    (hmean : ∫ z : ℝ, z ∂μ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N h : ℕ) (D : ℤ) (x : Site 2),
      Integrable (fun η : Site 2 → ℝ => |orientedPotential η (N + h) x -
          orientedPotential η N (x + orientedLayerPoint h D)| ^ p) (iidLaw 2 μ) ∧
      (∫ η : Site 2 → ℝ, |orientedPotential η (N + h) x -
          orientedPotential η N (x + orientedLayerPoint h D)| ^ p ∂(iidLaw 2 μ)) ^ (2 / p) ≤
        C * (Real.sqrt h + |(D : ℝ) - (h : ℝ) / 2|) := by
  classical
  obtain ⟨C, hC, hb⟩ := exists_linear_moment_finite_support (ι := Site 2) μ p hp hmom hmean
  refine ⟨4 * C, by positivity, fun N h D x => ?_⟩
  let y := orientedLayerPoint h D
  let S := boxFinset x (N + h) ∪ boxFinset (x + y) N
  let a : Site 2 → ℝ := fun z => orientedGreen 2 (N + h) (z - x) - orientedGreen 2 N (z - (x + y))
  have ha : ∀ z ∉ S, a z = 0 := by
    intro z hz
    have h1 : z ∉ boxFinset x (N + h) := fun h1 => hz (mem_union_left _ h1)
    have h2 : z ∉ boxFinset (x + y) N := fun h2 => hz (mem_union_right _ h2)
    simp only [a, orientedGreen_sub_zero_outside h1, orientedGreen_sub_zero_outside h2, sub_self]
  have he : ∀ η : Site 2 → ℝ, (∑' z, a z * η z) =
      orientedPotential η (N + h) x - orientedPotential η N (x + y) := by
    intro η
    exact (orientedPotential_sub η (N + h) N x (x + y)).symm
  obtain ⟨hi, hB⟩ := hb S a ha
  simp only [he] at hi hB
  have hnorm : (∑' z : Site 2, a z ^ 2) =
      ∑' z : Site 2, (orientedGreen 2 (N + h) z - orientedGreen 2 N (z - y)) ^ 2 := by
    have hs := (Equiv.addRight x).tsum_eq (fun z : Site 2 => a z ^ 2)
    have ht : ∀ z : Site 2, a (z + x) = orientedGreen 2 (N + h) z - orientedGreen 2 N (z - y) := by
      intro z
      dsimp only [a]
      rw [add_sub_cancel_right, show z + x - (x + y) = z - y by abel]
    simp only [Equiv.coe_addRight, ht] at hs
    exact hs.symm
  rw [hnorm] at hB
  refine ⟨hi, hB.trans ?_⟩
  have hbound := mul_le_mul_of_nonneg_left (orientedGreen_delay_bound N h D) hC.le
  calc _ ≤ C * (4 * (Real.sqrt h + |(D : ℝ) - (h : ℝ) / 2|)) := hbound
    _ = _ := by ring

end Parking
