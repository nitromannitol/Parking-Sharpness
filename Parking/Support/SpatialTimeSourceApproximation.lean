/- The temporal quadrature in the tested recursion preserves the limiting scenery source. -/
import Parking.Support.SpatialSceneryL1
import Parking.Support.SpaceTimeProjection
import Parking.Generic.TimeTestQuadrature

open MeasureTheory Filter Topology
noncomputable section
namespace Parking
variable {d : ℕ}

/-- The right-endpoint temporal sum appearing in the parabolically rescaled recursion. -/
def sampledTimeIntegral (ψ : ℝ × (Fin d → ℝ) → ℝ) (T R : ℝ) (x : Fin d → ℝ) : ℝ :=
  (1 / R ^ 2) * ∑ k ∈ Finset.range ⌈T * R ^ 2⌉₊,
    ψ ((((k + 1 : ℕ) : ℝ) / R ^ 2), x)

/-- The source's temporal quadrature error vanishes in first mean. This only uses
the scenery's first absolute moment and the condition `d ≤ 3`. -/
theorem exists_tendsto_scenePair_time_quadrature_with_support (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ) :
    ∃ T : ℝ, 0 < T ∧ (∀ p ∈ tsupport ψ, p.1 < T) ∧ (∀ x, ψ (0, x) = 0) ∧
      (∀ R : ℝ, 1 ≤ R → ∀ x, ψ (((⌈T * R ^ 2⌉₊ : ℝ) / R ^ 2), x) = 0) ∧
      Tendsto (fun R : ℝ => ∫ w,
        |scenePair w R (fun x => sampledTimeIntegral ψ T R x - ∫ s : ℝ, ψ (s, x))|
          ∂law d ν) atTop (𝓝 0) := by
  obtain ⟨T, C, hT, hC, hsupport, hquad⟩ := Generic.TimeTest.exists_positive_time_quadrature_bound_with_support
    hψ.1 hψ.2.1 hψ.2.2
  have hmesh : ∀ R : ℝ, 1 ≤ R → 0 < 1 / R ^ 2 ∧ 1 / R ^ 2 ≤ 1 := by
    intro R hR
    have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
    refine ⟨by positivity, (div_le_one (sq_pos_of_pos hRpos)).mpr ?_⟩
    nlinarith
  have hq : ∀ R : ℝ, 1 ≤ R →
      (∀ x, ψ (0, x) = 0) ∧
      (∀ x, ψ (((⌈T * R ^ 2⌉₊ : ℝ) / R ^ 2), x) = 0) ∧
      ∀ x, |sampledTimeIntegral ψ T R x - ∫ s : ℝ, ψ (s, x)| ≤ C / R ^ 2 := by
    intro R hR
    simpa only [sampledTimeIntegral, div_div_eq_mul_div, div_one, mul_one_div] using
      hquad (1 / R ^ 2) (hmesh R hR).1 (hmesh R hR).2
  refine ⟨T, hT, hsupport, (hq 1 le_rfl).1, fun R hR => (hq R hR).2.1, ?_⟩
  obtain ⟨B, hB⟩ := hψ.2.1.isCompact.exists_bound_of_continuousOn
    (f := fun p : ℝ × (Fin d → ℝ) => p.2) continuous_snd.continuousOn
  have hb : 0 < max B 0 + 1 := by linarith [le_max_right B 0]
  apply tendsto_integral_abs_scenePair_of_quadratic_error hd hd3 ν hint hb hC
  · exact Eventually.of_forall fun R x hx => by
      by_contra hn
      have hfar : B < ‖x‖ := lt_of_le_of_lt (by linarith [le_max_left B 0]) (lt_of_not_ge hn)
      have hz : ∀ s : ℝ, ψ (s, x) = 0 := by
        intro s
        by_contra hs
        exact (not_le.mpr hfar) (hB (s, x) (subset_tsupport ψ hs))
      exact hx (by simp [sampledTimeIntegral, hz])
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact (hq R hR).2.2

/-- The time quadrature error tends to zero in first mean. -/
theorem exists_tendsto_scenePair_time_quadrature (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ) :
    ∃ T : ℝ, 0 < T ∧ (∀ x, ψ (0, x) = 0) ∧
      (∀ R : ℝ, 1 ≤ R → ∀ x, ψ (((⌈T * R ^ 2⌉₊ : ℝ) / R ^ 2), x) = 0) ∧
      Tendsto (fun R : ℝ => ∫ w,
        |scenePair w R (fun x => sampledTimeIntegral ψ T R x - ∫ s : ℝ, ψ (s, x))|
          ∂law d ν) atTop (𝓝 0) := by
  obtain ⟨T, hT, _, hzero, hfinal, hlim⟩ :=
    exists_tendsto_scenePair_time_quadrature_with_support hd hd3 ν hint hψ
  exact ⟨T, hT, hzero, hfinal, hlim⟩

end Parking
