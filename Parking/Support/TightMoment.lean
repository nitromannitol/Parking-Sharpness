/-
The increment moments of the rescaled convolved potential of the directed
scaling limit (`parking.tex:3192-3203`).

The potential increment over a layer displacement is a linear functional of the
i.i.d. scenery, so its `p`-th moment is bounded by the scenery moment bound of
`Parking.exists_oriented_potential_scenery_bound`; the exponential moment of the
scenery supplies the finiteness of that bound at every `p ≥ 0`.
-/
import Parking.Support.TightField
import Parking.Support.OrientedSceneryMoment
import Parking.Support.CriticalLawReal
import Parking.Support.ConfMoments

noncomputable section
namespace Parking
open MeasureTheory LatticeProb

/-- **The `p`-th moment of the scenery is finite under the exponential moment.** -/
theorem integrable_rpow_realLaw (ν : Measure ℤ) (hν : CriticalLaw ν) (p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun z : ℝ => |z| ^ p) (realLaw ν) := by
  obtain ⟨θ, hθ, hexp⟩ := realLaw_expMoment ν hν
  obtain ⟨K, _hK, hbound⟩ := rpow_le_const_mul_exp (r := p) hp hθ
  refine Integrable.mono' (hexp.const_mul K) (measurable_abs.pow_const p).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  have hb := hbound |z| (abs_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg z) p)]
  exact hb

/-- **The prefactor of the `p`-th moment of the rescaled increment.** -/
theorem orientedRescaledPotential_integral_rpow_eq (n : ℕ) (s y s' y' : ℝ)
    (h : ⌊(n : ℝ) * s'⌋₊ ≤ ⌊(n : ℝ) * s⌋₊) (p : ℝ) (hp : 0 < p) (ν : Measure ℤ) :
    (∫ η : Site 2 → ℝ,
        |orientedRescaledPotential n s y η - orientedRescaledPotential n s' y' η| ^ p
      ∂(iidLaw 2 (realLaw ν))) ^ (2 / p) =
      (n : ℝ) ^ (-(1 : ℝ) / 2) *
        (∫ η : Site 2 → ℝ,
          |orientedPotential η ⌊(n : ℝ) * s⌋₊ (orientedFieldSite n s y) -
            orientedPotential η ⌊(n : ℝ) * s'⌋₊ (orientedFieldSite n s' y')| ^ p
        ∂(iidLaw 2 (realLaw ν))) ^ (2 / p) := by
  have hpt : ∀ η : Site 2 → ℝ,
      |orientedRescaledPotential n s y η - orientedRescaledPotential n s' y' η| ^ p
      = ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ p *
        |orientedPotential η ⌊(n : ℝ) * s⌋₊ (orientedFieldSite n s y) -
          orientedPotential η ⌊(n : ℝ) * s'⌋₊ (orientedFieldSite n s' y')| ^ p :=
    fun η => orientedRescaledPotential_abs_sub_rpow n s y s' y' h p η
  simp only [hpt]
  rw [integral_const_mul]
  rw [Real.mul_rpow (Real.rpow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) _)
    (integral_nonneg (fun η => Real.rpow_nonneg (abs_nonneg _) p))]
  congr 1
  rw [← Real.rpow_mul (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  rw [← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1
  have h2 : p * (2 / p) = 2 := by
    rw [mul_comm p (2 / p), div_mul_cancel₀ 2 (ne_of_gt hp)]
  rw [h2]
  norm_num

/-- **The spatial increment moment**: two sites in the same layer differ by a
layer point of layer zero, and the scenery estimate bounds the `p`-th moment of
that increment by the layer coordinate. -/
theorem exists_oriented_spatial_increment_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 2 ≤ p) (hmom : Integrable (fun z : ℝ => |z| ^ p) μ)
    (hmean : ∫ z : ℝ, z ∂μ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (D : ℤ) (x : Site 2),
      Integrable (fun η : Site 2 → ℝ => |orientedPotential η N (x + orientedLayerPoint 0 D) -
          orientedPotential η N x| ^ p) (iidLaw 2 μ) ∧
      (∫ η : Site 2 → ℝ, |orientedPotential η N (x + orientedLayerPoint 0 D) -
          orientedPotential η N x| ^ p ∂(iidLaw 2 μ)) ^ (2 / p) ≤
        C * |(D : ℝ)| := by
  obtain ⟨C, hC, hb⟩ := exists_oriented_potential_scenery_bound μ p hp hmom hmean
  refine ⟨C, hC, fun N D x => ?_⟩
  have h := hb N 0 D x
  simpa [abs_sub_comm, Real.sqrt_zero, zero_div, sub_zero, Nat.cast_zero, add_zero] using h

/-- **The increment moment of the rescaled field**: when the two space-time
points differ by `h` layers and layer coordinate `D`, the `p`-th moment of the
increment is bounded by the crossed scenery estimate. -/
theorem exists_orientedRescaledPotential_moment_bound (ν : Measure ℤ) (hν : CriticalLaw ν)
    (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (s y s' y' : ℝ) (h : ℕ) (D : ℤ),
      ⌊(n : ℝ) * s'⌋₊ + h = ⌊(n : ℝ) * s⌋₊ →
      orientedFieldSite n s' y' = orientedFieldSite n s y + orientedLayerPoint h D →
      Integrable (fun η : Site 2 → ℝ => |orientedRescaledPotential n s y η -
          orientedRescaledPotential n s' y' η| ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedRescaledPotential n s y η -
          orientedRescaledPotential n s' y' η| ^ p ∂(iidLaw 2 (realLaw ν))) ^ (2 / p) ≤
        C * ((n : ℝ) ^ (-(1 : ℝ) / 2) * (Real.sqrt h + |(D : ℝ) - (h : ℝ) / 2|)) := by
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  have hp0 : (0 : ℝ) ≤ p := le_trans (by norm_num) hp
  have hpp : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp
  obtain ⟨C, hC, hb⟩ := exists_oriented_potential_scenery_bound (realLaw ν) p hp
    (integrable_rpow_realLaw ν hν p hp0) (realLaw_mean ν hν)
  refine ⟨C, hC, fun n s y s' y' h D hN hsite => ?_⟩
  have hle : ⌊(n : ℝ) * s'⌋₊ ≤ ⌊(n : ℝ) * s⌋₊ := hN ▸ Nat.le_add_right _ _
  have hkey := hb ⌊(n : ℝ) * s'⌋₊ h D (orientedFieldSite n s y)
  have hkey2 : Integrable (fun η : Site 2 → ℝ =>
        |orientedPotential η ⌊(n : ℝ) * s⌋₊ (orientedFieldSite n s y) -
          orientedPotential η ⌊(n : ℝ) * s'⌋₊ (orientedFieldSite n s' y')| ^ p)
        (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedPotential η ⌊(n : ℝ) * s⌋₊ (orientedFieldSite n s y) -
          orientedPotential η ⌊(n : ℝ) * s'⌋₊ (orientedFieldSite n s' y')| ^ p
          ∂(iidLaw 2 (realLaw ν))) ^ (2 / p) ≤
        C * (Real.sqrt h + |(D : ℝ) - (h : ℝ) / 2|) := by
    have h := hkey
    rw [hN, ← hsite] at h
    exact h
  constructor
  · have h1 : Integrable (fun η : Site 2 → ℝ =>
        ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ p *
          |orientedPotential η ⌊(n : ℝ) * s⌋₊ (orientedFieldSite n s y) -
            orientedPotential η ⌊(n : ℝ) * s'⌋₊ (orientedFieldSite n s' y')| ^ p)
        (iidLaw 2 (realLaw ν)) := hkey2.1.const_mul _
    refine h1.congr ?_
    filter_upwards with η
    rw [orientedRescaledPotential_abs_sub_rpow n s y s' y' hle p]
  · rw [orientedRescaledPotential_integral_rpow_eq n s y s' y' hle p hpp ν]
    calc (n : ℝ) ^ (-(1 : ℝ) / 2) *
            (∫ η : Site 2 → ℝ, |orientedPotential η ⌊(n : ℝ) * s⌋₊ (orientedFieldSite n s y) -
              orientedPotential η ⌊(n : ℝ) * s'⌋₊ (orientedFieldSite n s' y')| ^ p
              ∂(iidLaw 2 (realLaw ν))) ^ (2 / p)
        ≤ (n : ℝ) ^ (-(1 : ℝ) / 2) * (C * (Real.sqrt h + |(D : ℝ) - (h : ℝ) / 2|)) :=
          mul_le_mul_of_nonneg_left hkey2.2 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = C * ((n : ℝ) ^ (-(1 : ℝ) / 2) * (Real.sqrt h + |(D : ℝ) - (h : ℝ) / 2|)) := by ring

end Parking
end
