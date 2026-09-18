/-
Differentiating an exponential family under the integral sign.

Step 3 of `lem:product` (`parking.tex:2409-2412`) differentiates
`λ ↦ E_λ F` in the tilting parameter.  The paper's justification is that
`λ₁ < θ`, the threshold of the exponential moment, so the difference quotients
of `e^{λ S}` are dominated uniformly for `λ` in a compact subinterval of
`[0, θ)`.  Only a RIGHT exponential moment is assumed, so at `λ = 0` there is
no two-sided derivative to be had in general and the identity is proved as a
derivative within `Set.Ici 0`; that is all the paper's argument needs, and it
is what identifies the derivative supplied by the frozen statement.

The domination is `Parking.abs_exp_sub_exp_bound`, and the limit of the
difference quotients is taken with dominated convergence along the filter
`𝓝[Set.Ici 0 \ {λ}] λ`, which is exactly the filter of the slope
characterization of a derivative within a set.
-/
import Parking.Support.ExpBound
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory Filter Topology Set

noncomputable section

namespace Parking

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **A bounded observable against the exponential weight is integrable.**
Below the threshold `θ` of the exponential moment the weight `e^{s S}` is
dominated by `1 + e^{θ S}`. -/
theorem integrable_exp_mul_bdd [IsFiniteMeasure P] {S : Ω → ℝ} (hSm : Measurable S) {θ : ℝ}
    (hexp : Integrable (fun ω => Real.exp (θ * S ω)) P)
    {f : Ω → ℝ} (hfm : Measurable f) (hfb : ∀ ω, |f ω| ≤ 1)
    {s : ℝ} (hs0 : 0 ≤ s) (hsθ : s ≤ θ) :
    Integrable (fun ω => Real.exp (s * S ω) * f ω) P := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hexp)
    (((Real.measurable_exp.comp (measurable_const.mul hSm)).mul hfm)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have hpos : (0 : ℝ) < Real.exp (s * S ω) := Real.exp_pos _
  have hθ : (0 : ℝ) < Real.exp (θ * S ω) := Real.exp_pos _
  have hfb1 : |f ω| ≤ 1 := hfb ω
  have hmain : Real.exp (s * S ω) ≤ 1 + Real.exp (θ * S ω) := by
    rcases le_or_gt 0 (S ω) with hk | hk
    · have h1 : s * S ω ≤ θ * S ω := mul_le_mul_of_nonneg_right hsθ hk
      have h2 : Real.exp (s * S ω) ≤ Real.exp (θ * S ω) := Real.exp_le_exp.mpr h1
      linarith
    · have h1 : s * S ω ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs0 (le_of_lt hk)
      have h2 : Real.exp (s * S ω) ≤ 1 := Real.exp_le_one_iff.mpr h1
      linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
  simp only [Pi.add_apply]
  nlinarith [hpos, hθ, hfb1, abs_nonneg (f ω)]

/-- **Differentiating the exponential family within `[0, ∞)`.**  For a bounded
observable `f` and a variable `S` with a right exponential moment of order `θ`
and an absolute first moment, the map `s ↦ ∫ e^{s S} f` has derivative
`∫ S e^{λ S} f` within `Set.Ici 0` at every `λ ∈ [0, θ)`. -/
theorem hasDerivWithinAt_integral_exp [IsFiniteMeasure P]
    {S : Ω → ℝ} (hSm : Measurable S) {θ : ℝ}
    (hexp : Integrable (fun ω => Real.exp (θ * S ω)) P)
    (hint : Integrable (fun ω => |S ω|) P)
    {f : Ω → ℝ} (hfm : Measurable f) (hfb : ∀ ω, |f ω| ≤ 1)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlamθ : lam < θ) :
    HasDerivWithinAt (fun s => ∫ ω, Real.exp (s * S ω) * f ω ∂P)
      (∫ ω, S ω * Real.exp (lam * S ω) * f ω ∂P) (Set.Ici 0) lam := by
  classical
  set s₁ : ℝ := (lam + θ) / 2 with hs₁def
  have hlams₁ : lam < s₁ := by rw [hs₁def]; linarith
  have hs₁θ : s₁ < θ := by rw [hs₁def]; linarith
  have hs₁0 : 0 ≤ s₁ := by linarith
  set l : Filter ℝ := 𝓝[Set.Ici (0:ℝ) \ {lam}] lam with hldef
  set bnd : Ω → ℝ := fun ω => Real.exp (θ * S ω) / (θ - s₁) + |S ω| with hbnddef
  have hbndint : Integrable bnd P := (hexp.div_const _).add hint
  have hFmeas : ∀ s : ℝ, Measurable (fun ω => (s - lam)⁻¹ *
      (Real.exp (s * S ω) * f ω - Real.exp (lam * S ω) * f ω)) := by
    intro s
    exact measurable_const.mul
      ((((Real.measurable_exp.comp (measurable_const.mul hSm)).mul hfm)).sub
        (((Real.measurable_exp.comp (measurable_const.mul hSm)).mul hfm)))
  have hfilt : l ≤ 𝓝[≠] lam := by
    rw [hldef]
    exact nhdsWithin_mono _ (fun x hx => hx.2)
  have hev : ∀ᶠ s in l, 0 ≤ s ∧ s ≤ s₁ ∧ s ≠ lam := by
    have h1 : ∀ᶠ s in l, s ∈ Set.Ici (0:ℝ) \ {lam} := self_mem_nhdsWithin
    have h2 : ∀ᶠ s in l, s < s₁ :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hlams₁)
    filter_upwards [h1, h2] with s hs hlt
    exact ⟨hs.1, le_of_lt hlt, hs.2⟩
  have hslope : ∀ᶠ s in l, slope (fun s => ∫ ω, Real.exp (s * S ω) * f ω ∂P) lam s
      = ∫ ω, (s - lam)⁻¹ * (Real.exp (s * S ω) * f ω - Real.exp (lam * S ω) * f ω) ∂P := by
    filter_upwards [hev] with s hs
    have hI1 : Integrable (fun ω => Real.exp (s * S ω) * f ω) P :=
      integrable_exp_mul_bdd hSm hexp hfm hfb hs.1 (le_of_lt (lt_of_le_of_lt hs.2.1 hs₁θ))
    have hI2 : Integrable (fun ω => Real.exp (lam * S ω) * f ω) P :=
      integrable_exp_mul_bdd hSm hexp hfm hfb hlam0 (le_of_lt hlamθ)
    rw [integral_const_mul, integral_sub hI1 hI2]
    simp [slope_def_field, div_eq_inv_mul]
  have hlim : Tendsto (fun s => ∫ ω, (s - lam)⁻¹ *
      (Real.exp (s * S ω) * f ω - Real.exp (lam * S ω) * f ω) ∂P) l
      (𝓝 (∫ ω, S ω * Real.exp (lam * S ω) * f ω ∂P)) := by
    refine tendsto_integral_filter_of_dominated_convergence bnd
      (Filter.Eventually.of_forall fun s => (hFmeas s).aestronglyMeasurable) ?_ hbndint ?_
    · filter_upwards [hev] with s hs
      refine Filter.Eventually.of_forall fun ω => ?_
      have hne : s - lam ≠ 0 := sub_ne_zero_of_ne hs.2.2
      have hkey := abs_exp_sub_exp_bound hs₁θ hlam0 (le_of_lt hlams₁) hs.1 hs.2.1 (S ω)
      have hfw : |f ω| ≤ 1 := hfb ω
      have hbpos : 0 ≤ bnd ω := by
        rw [hbnddef]
        exact add_nonneg (div_nonneg (Real.exp_nonneg _) (by linarith)) (abs_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_inv, ← sub_mul, abs_mul]
      have h1 : |Real.exp (s * S ω) - Real.exp (lam * S ω)| * |f ω|
          ≤ |s - lam| * bnd ω := by
        calc |Real.exp (s * S ω) - Real.exp (lam * S ω)| * |f ω|
            ≤ (|s - lam| * bnd ω) * 1 := by
              refine mul_le_mul hkey hfw (abs_nonneg _) ?_
              exact mul_nonneg (abs_nonneg _) hbpos
          _ = |s - lam| * bnd ω := by ring
      have habs : 0 < |s - lam| := abs_pos.mpr hne
      have hcancel : |s - lam|⁻¹ * (|s - lam| * bnd ω) = bnd ω := by field_simp
      rw [← hcancel]
      exact mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr habs))
    · refine Filter.Eventually.of_forall fun ω => ?_
      have hd : HasDerivAt (fun s : ℝ => Real.exp (s * S ω) * f ω)
          (S ω * Real.exp (lam * S ω) * f ω) lam := by
        have h1 : HasDerivAt (fun s : ℝ => s * S ω) (S ω) lam := by
          simpa using (hasDerivAt_id lam).mul_const (S ω)
        have h2 : HasDerivAt (fun s : ℝ => Real.exp (s * S ω))
            (Real.exp (lam * S ω) * S ω) lam := h1.exp
        have h3 := h2.mul_const (f ω)
        have heq : Real.exp (lam * S ω) * S ω * f ω = S ω * Real.exp (lam * S ω) * f ω := by
          ring
        rwa [heq] at h3
      have hs := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left hfilt
      refine hs.congr fun s => ?_
      simp [slope_def_field, div_eq_inv_mul, mul_sub]
  rw [hasDerivWithinAt_iff_tendsto_slope]
  exact hlim.congr' (hslope.mono fun s hs => hs.symm)

end Parking

end
