/-
Continuity of the tilted mean in the tilting parameter.

`thm:subcritical` (`parking.tex:2478-2482`) needs `δ(0) = -E η(0) > 0` and the
continuity of `δ` to conclude that `a = (1/3) ∫₀^{λ₁} δ` is positive: the
hypothesis of Section 9 gives only `δ ≥ 0` on `[0, λ₁]`, which by itself is
compatible with `δ` vanishing on `(0, λ₁]`.

`s ↦ ∫ e^{sk} dν` is continuous because it is differentiable
(`Support/TiltDeriv.lean`), and `s ↦ ∫ k e^{sk} dν` by dominated convergence
with the bound `e^{θk}/(θ-s₁) + |k|` of `Support/TiltCov.lean`, uniform for
`s ∈ [0, s₁]` with `s₁ < θ`.  The tilted mean is their quotient
(`Parking.integral_tiltLaw`), and the tilt at `0` is the law itself.
-/
import Parking.Support.TiltCov

open MeasureTheory Set Filter Topology

noncomputable section

namespace Parking

/-- The tilt at parameter zero is the law itself. -/
theorem tiltLaw_zero {ν : Measure ℤ} [IsProbabilityMeasure ν] : tiltLaw ν 0 = ν := by
  unfold tiltLaw
  simp

theorem continuousOn_integral_mul_exp {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ : ℝ}
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) {s₁ : ℝ} (hs₁θ : s₁ < θ) :
    ContinuousOn (fun s => ∫ k, (k : ℝ) * Real.exp (s * k) ∂ν) (Set.Icc 0 s₁) := by
  intro s₀ hs₀
  have hts : (0:ℝ) < θ - s₁ := by linarith
  have hmeas : ∀ s : ℝ, Measurable (fun k : ℤ => (k : ℝ) * Real.exp (s * k)) := fun s =>
    (measurable_int_fun (fun k : ℤ => (k : ℝ))).mul
      (Real.measurable_exp.comp (measurable_const.mul
        (measurable_int_fun (fun k : ℤ => (k : ℝ)))))
  refine tendsto_integral_filter_of_dominated_convergence
    (fun k : ℤ => Real.exp (θ * k) / (θ - s₁) + |(k : ℝ)|)
    (Filter.Eventually.of_forall fun s => (hmeas s).aestronglyMeasurable)
    ?_ ((hexp.div_const (θ - s₁)).add hint) ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    refine Filter.Eventually.of_forall fun k => ?_
    have hsθ : s < θ := lt_of_le_of_lt hs.2 hs₁θ
    have hk := abs_mul_exp_le (lam := s) (s₁ := θ) (x := (k : ℝ)) hs.1 hsθ
    have hmono : Real.exp (θ * (k : ℝ)) / (θ - s) ≤ Real.exp (θ * (k : ℝ)) / (θ - s₁) := by
      apply div_le_div_of_nonneg_left (Real.exp_nonneg _) hts
      linarith [hs.2]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos (s * (k : ℝ)))]
    linarith
  · refine Filter.Eventually.of_forall fun k => ?_
    have h1 : Continuous fun s : ℝ => (k : ℝ) * Real.exp (s * (k : ℝ)) :=
      continuous_const.mul (Real.continuous_exp.comp (continuous_id.mul continuous_const))
    exact (h1.continuousAt.tendsto).mono_left nhdsWithin_le_nhds

theorem continuousOn_integral_exp {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ : ℝ}
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) {s₁ : ℝ} (hs₁θ : s₁ < θ) :
    ContinuousOn (fun s => ∫ k, Real.exp (s * k) ∂ν) (Set.Icc 0 s₁) := by
  have hsub : Set.Icc (0:ℝ) s₁ ⊆ Set.Ici (0:ℝ) := fun x hx => hx.1
  intro s₀ hs₀
  have hd := hasDerivWithinAt_integral_exp (P := ν) (S := fun k : ℤ => (k : ℝ))
    (measurable_int_fun (fun k : ℤ => (k : ℝ))) hexp hint
    (f := fun _ : ℤ => (1:ℝ)) measurable_const (fun _ => by norm_num) hs₀.1
    (lt_of_le_of_lt hs₀.2 hs₁θ)
  have hc : ContinuousWithinAt (fun s => ∫ k, Real.exp (s * (k : ℝ)) * (1:ℝ) ∂ν)
      (Set.Icc 0 s₁) s₀ := hd.continuousWithinAt.mono hsub
  simpa using hc

theorem continuousOn_drift {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ : ℝ}
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) {s₁ : ℝ} (hs₁θ : s₁ < θ) :
    ContinuousOn (drift ν) (Set.Icc 0 s₁) := by
  have hden := continuousOn_integral_exp hexp hint hs₁θ
  have hnum := continuousOn_integral_mul_exp hexp hint hs₁θ
  have hne : ∀ s ∈ Set.Icc (0:ℝ) s₁, (∫ k, Real.exp (s * k) ∂ν) ≠ 0 := by
    intro s hs
    exact ne_of_gt (integral_exp_pos (integrable_exp_tilt hexp hs.1
      (le_of_lt (lt_of_le_of_lt hs.2 hs₁θ))))
  have heq : ∀ s ∈ Set.Icc (0:ℝ) s₁, drift ν s =
      -((∫ k, Real.exp (s * k) ∂ν)⁻¹ * ∫ k, (k : ℝ) * Real.exp (s * k) ∂ν) := by
    intro s hs
    have hexps := integrable_exp_tilt hexp hs.1 (le_of_lt (lt_of_le_of_lt hs.2 hs₁θ))
    have h := integral_tiltLaw s (fun k : ℤ => (k : ℝ)) hexps
    have h2 : (∫ k, Real.exp (s * k) * (k : ℝ) ∂ν) = ∫ k, (k : ℝ) * Real.exp (s * k) ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall fun k => by ring)
    unfold drift
    rw [h, h2]
  exact ContinuousOn.congr (((hden.inv₀ hne).mul hnum).neg) heq

/-- **The constant `a` of `thm:subcritical` is positive.**  The drift is
nonnegative on `[0, λ₁]` by the choice of `λ₁` and is positive at `0`, where the
tilt is the law itself; continuity turns that into a positive integral.  Without
continuity the drift could vanish on `(0, λ₁]` and the integral could be zero. -/
theorem intervalIntegral_drift_pos {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ : ℝ}
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν < 0) {lam₁ : ℝ} (hlam₁ : 0 < lam₁) (hlam₁θ : lam₁ < θ)
    (hnonneg : ∀ s ∈ Set.Icc (0:ℝ) lam₁, 0 ≤ drift ν s) :
    0 < ∫ s in (0:ℝ)..lam₁, drift ν s := by
  have hcont : ContinuousOn (drift ν) (Set.Icc 0 lam₁) := continuousOn_drift hexp hint hlam₁θ
  have h0 : 0 < drift ν 0 := by
    unfold drift
    rw [tiltLaw_zero]
    linarith
  have hmem : {s : ℝ | drift ν 0 / 2 < drift ν s} ∈ 𝓝[Set.Icc (0:ℝ) lam₁] (0:ℝ) :=
    (hcont 0 (Set.left_mem_Icc.mpr (le_of_lt hlam₁))) (Ioi_mem_nhds (by linarith))
  rw [nhdsWithin_Icc_eq_nhdsGE hlam₁] at hmem
  obtain ⟨u, hu0, husub⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp hmem
  set e : ℝ := min u lam₁ with hedef
  have he0 : 0 < e := lt_min hu0 hlam₁
  have helam : e ≤ lam₁ := min_le_right _ _
  have hlow : ∀ s ∈ Set.Icc (0:ℝ) e, drift ν 0 / 2 ≤ drift ν s := fun s hs =>
    le_of_lt (husub ⟨hs.1, le_trans hs.2 (min_le_left _ _)⟩)
  have hint1 : IntervalIntegrable (drift ν) MeasureTheory.volume 0 e := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (le_of_lt he0)]
    exact hcont.mono (fun x hx => ⟨hx.1, le_trans hx.2 helam⟩)
  have hint2 : IntervalIntegrable (drift ν) MeasureTheory.volume e lam₁ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le helam]
    exact hcont.mono (fun x hx => ⟨le_trans (le_of_lt he0) hx.1, hx.2⟩)
  have hsplit : (∫ s in (0:ℝ)..e, drift ν s) + ∫ s in e..lam₁, drift ν s
      = ∫ s in (0:ℝ)..lam₁, drift ν s :=
    intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  have hconst : (∫ _s in (0:ℝ)..e, drift ν 0 / 2) ≤ ∫ s in (0:ℝ)..e, drift ν s :=
    intervalIntegral.integral_mono_on (le_of_lt he0) intervalIntegrable_const hint1 hlow
  have hval : (∫ _s in (0:ℝ)..e, drift ν 0 / 2) = e * (drift ν 0 / 2) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have hpos1 : 0 < ∫ s in (0:ℝ)..e, drift ν s := by
    nlinarith [hconst, hval, he0, h0]
  have hpos2 : 0 ≤ ∫ s in e..lam₁, drift ν s :=
    intervalIntegral.integral_nonneg helam
      (fun s hs => hnonneg s ⟨le_trans (le_of_lt he0) hs.1, hs.2⟩)
  linarith [hsplit, hpos1, hpos2]

/-- The same for the absolute first moment against the exponential weight. -/
theorem continuousOn_integral_abs_mul_exp {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ : ℝ}
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) {s₁ : ℝ} (hs₁θ : s₁ < θ) :
    ContinuousOn (fun s => ∫ k, |(k : ℝ)| * Real.exp (s * k) ∂ν) (Set.Icc 0 s₁) := by
  intro s₀ hs₀
  have hts : (0:ℝ) < θ - s₁ := by linarith
  have hmeas : ∀ s : ℝ, Measurable (fun k : ℤ => |(k : ℝ)| * Real.exp (s * k)) := fun s =>
    (measurable_int_fun (fun k : ℤ => |(k : ℝ)|)).mul
      (Real.measurable_exp.comp (measurable_const.mul
        (measurable_int_fun (fun k : ℤ => (k : ℝ)))))
  refine tendsto_integral_filter_of_dominated_convergence
    (fun k : ℤ => Real.exp (θ * k) / (θ - s₁) + |(k : ℝ)|)
    (Filter.Eventually.of_forall fun s => (hmeas s).aestronglyMeasurable)
    ?_ ((hexp.div_const (θ - s₁)).add hint) ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    refine Filter.Eventually.of_forall fun k => ?_
    have hsθ : s < θ := lt_of_le_of_lt hs.2 hs₁θ
    have hk := abs_mul_exp_le (lam := s) (s₁ := θ) (x := (k : ℝ)) hs.1 hsθ
    have hmono : Real.exp (θ * (k : ℝ)) / (θ - s) ≤ Real.exp (θ * (k : ℝ)) / (θ - s₁) := by
      apply div_le_div_of_nonneg_left (Real.exp_nonneg _) hts
      linarith [hs.2]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos (s * (k : ℝ))), abs_abs]
    linarith
  · refine Filter.Eventually.of_forall fun k => ?_
    have h1 : Continuous fun s : ℝ => |(k : ℝ)| * Real.exp (s * (k : ℝ)) :=
      continuous_const.mul (Real.continuous_exp.comp (continuous_id.mul continuous_const))
    exact (h1.continuousAt.tendsto).mono_left nhdsWithin_le_nhds

/-- **The tilted absolute first moment is continuous.**  This is the term
`E_λ|η(0)|` of `thm:subcritical`. -/
theorem continuousOn_tiltAbsMean {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ : ℝ}
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) {s₁ : ℝ} (hs₁θ : s₁ < θ) :
    ContinuousOn (fun s => ∫ k, |(k : ℝ)| ∂(tiltLaw ν s)) (Set.Icc 0 s₁) := by
  have hden := continuousOn_integral_exp hexp hint hs₁θ
  have hnum := continuousOn_integral_abs_mul_exp hexp hint hs₁θ
  have hne : ∀ s ∈ Set.Icc (0:ℝ) s₁, (∫ k, Real.exp (s * k) ∂ν) ≠ 0 := by
    intro s hs
    exact ne_of_gt (integral_exp_pos (integrable_exp_tilt hexp hs.1
      (le_of_lt (lt_of_le_of_lt hs.2 hs₁θ))))
  have heq : ∀ s ∈ Set.Icc (0:ℝ) s₁, (∫ k, |(k : ℝ)| ∂(tiltLaw ν s)) =
      (∫ k, Real.exp (s * k) ∂ν)⁻¹ * ∫ k, |(k : ℝ)| * Real.exp (s * k) ∂ν := by
    intro s hs
    have hexps := integrable_exp_tilt hexp hs.1 (le_of_lt (lt_of_le_of_lt hs.2 hs₁θ))
    have h := integral_tiltLaw s (fun k : ℤ => |(k : ℝ)|) hexps
    have h2 : (∫ k, Real.exp (s * k) * |(k : ℝ)| ∂ν)
        = ∫ k, |(k : ℝ)| * Real.exp (s * k) ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall fun k => by ring)
    rw [h, h2]
  exact ContinuousOn.congr ((hden.inv₀ hne).mul hnum) heq

end Parking

end
