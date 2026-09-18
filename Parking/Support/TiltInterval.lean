/-
The tilting interval of `thm:subcritical` and the support point it is applied at.

`parking.tex:2303-2320` chooses `0 < λ₁ < θ` "so small that, for `0 ≤ λ ≤ λ₁`,
the law `P_λ` has nonpositive mean", and adds "such a choice exists by
continuity".  `Parking.exists_lam1` is that choice: the drift is continuous on
`[0, θ/2]` (`Parking.continuousOn_drift`) and positive at `0`, where the tilt is
the law itself, so it stays positive on a right neighbourhood of `0`.

`Parking.integrable_tiltLaw` is the integrability of an observable against the
tilt, which the nonpositive-mean hypothesis of `thm:subcritical` asserts
alongside the inequality, and `Parking.exists_support_pos` produces the integer
`k ≥ 1` in the support of the count at the origin out of `P(η(0) > 0) > 0`.
-/
import Parking.Support.TiltContinuity

open MeasureTheory Set Filter Topology

noncomputable section

namespace Parking

/-- **An observable integrable against the exponential weight is integrable
against the tilt.** -/
theorem integrable_tiltLaw {ν : Measure ℤ} [IsProbabilityMeasure ν] (s : ℝ) (f : ℤ → ℝ)
    (hexps : Integrable (fun k : ℤ => Real.exp (s * k)) ν)
    (h : Integrable (fun k : ℤ => Real.exp (s * k) * f k) ν) :
    Integrable f (tiltLaw ν s) := by
  have hpos : 0 < ∫ k, Real.exp (s * k) ∂ν := integral_exp_pos hexps
  have hmeas : Measurable fun k : ℤ => ENNReal.ofReal (Real.exp (s * k)) :=
    (measurable_int_fun (fun k : ℤ => Real.exp (s * k))).ennreal_ofReal
  have hl : ∫⁻ k, ENNReal.ofReal (Real.exp (s * k)) ∂ν
      = ENNReal.ofReal (∫ k, Real.exp (s * k) ∂ν) := lintegral_ofReal_exp s hexps
  have hne : (∫⁻ k, ENNReal.ofReal (Real.exp (s * k)) ∂ν)⁻¹ ≠ 0 := by
    rw [hl]
    simp
  have htop : (∫⁻ k, ENNReal.ofReal (Real.exp (s * k)) ∂ν)⁻¹ ≠ ⊤ := by
    rw [hl, ENNReal.inv_ne_top]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hpos)
  unfold tiltLaw
  rw [integrable_smul_measure hne htop,
    integrable_withDensity_iff hmeas (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simpa [ENNReal.toReal_ofReal (Real.exp_nonneg _), mul_comm] using h

/-- **The tilting interval of `thm:subcritical` exists.**  The drift is
continuous on `[0, θ/2]` and equals `-E η(0) > 0` at `0`, so it is nonnegative
on `[0, λ₁]` for a positive `λ₁` below `θ`. -/
theorem exists_lam1 {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν < 0) :
    ∃ lam₁ : ℝ, 0 < lam₁ ∧ lam₁ < θ ∧ ∀ s ∈ Set.Icc (0:ℝ) lam₁, 0 ≤ drift ν s := by
  have hs₁ : (0:ℝ) < θ / 2 := by linarith
  have hs₁θ : θ / 2 < θ := by linarith
  have hcont : ContinuousOn (drift ν) (Set.Icc 0 (θ / 2)) := continuousOn_drift hexp hint hs₁θ
  have h0 : 0 < drift ν 0 := by
    unfold drift
    rw [tiltLaw_zero]
    linarith
  have hmem : {s : ℝ | drift ν 0 / 2 < drift ν s} ∈ 𝓝[Set.Icc (0:ℝ) (θ / 2)] (0:ℝ) :=
    (hcont 0 (Set.left_mem_Icc.mpr (le_of_lt hs₁))) (Ioi_mem_nhds (by linarith))
  rw [nhdsWithin_Icc_eq_nhdsGE hs₁] at hmem
  obtain ⟨u, hu0, husub⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp hmem
  refine ⟨min u (θ / 2), lt_min hu0 hs₁, lt_of_le_of_lt (min_le_right _ _) hs₁θ, ?_⟩
  intro s hs
  have hsu : s ∈ Set.Icc (0:ℝ) u := ⟨hs.1, le_trans hs.2 (min_le_left _ _)⟩
  have hlt : drift ν 0 / 2 < drift ν s := husub hsu
  linarith

/-- **A positive count has a positive integer in its support.**  `Set.Ioi 0` in
`ℤ` is countable, so a positive mass on it charges one of its points. -/
theorem exists_support_pos {ν : Measure ℤ} (hpos : 0 < ν (Set.Ioi (0:ℤ))) :
    ∃ k : ℕ, 1 ≤ k ∧ ν {(k : ℤ)} ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hzero : ∀ x ∈ Set.Ioi (0:ℤ), ν {x} = 0 := by
    intro x hx
    have hx1 : (0:ℤ) < x := hx
    have hxn : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg (by omega)
    have h1 : 1 ≤ x.toNat := by omega
    have h2 := hcon x.toNat h1
    rwa [hxn] at h2
  have hcount : (Set.Ioi (0:ℤ)).Countable := Set.to_countable _
  have hU : ν (⋃ x ∈ Set.Ioi (0:ℤ), ({x} : Set ℤ)) = 0 :=
    (MeasureTheory.measure_biUnion_null_iff hcount).mpr hzero
  rw [Set.biUnion_of_singleton] at hU
  rw [hU] at hpos
  exact lt_irrefl 0 hpos

end Parking

end
