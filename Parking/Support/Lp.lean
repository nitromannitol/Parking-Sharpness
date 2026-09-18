/-
Three general facts about integrals that the proof of `prop:w-moment` uses and
that are not about parking at all.

- Cauchy-Schwarz against the constant one, in the form the paper needs when it
  writes `(E U_n(0)^{r/2})^{2/r} ≤ (E U_n(0)^r)^{1/r}`: on a probability space
  the square of a mean is at most the mean of the square.
- Fatou's lemma, in the form the paper needs when it applies the martingale
  moment inequality to the first `k` increments and lets `k` grow: the number of
  nonzero increments is finite for every realization but unbounded over them, so
  no single `k` works and the bound passes to the limit through the integral.
- The power of a weighted sum against the weighted sum of the powers, which is
  the convexity that turns Minkowski's inequality of the paper's proof into a
  statement about one site: with the weights `Γ`, the lattice sum of the
  quadratic variation is bounded by the total weight times the moment at the
  origin.
-/
import Parking.Support.ConfMoments
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.MeanInequalitiesPow

noncomputable section

namespace Parking

open MeasureTheory Finset

/-! ### A fixed power is a measurable function -/

theorem measurable_rpow_const {r : ℝ} (hr : 0 ≤ r) : Measurable fun x : ℝ => x ^ r :=
  (Real.continuous_rpow_const hr).measurable

/-- The square of a power is the power at twice the exponent. -/
theorem rpow_sq {x : ℝ} (hx : 0 ≤ x) (t : ℝ) : (x ^ t) ^ (2 : ℕ) = x ^ (2 * t) := by
  rw [← Real.rpow_natCast (x ^ t) 2, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

/-- A power of a square is the power at twice the exponent. -/
theorem sq_rpow {x : ℝ} (hx : 0 ≤ x) (t : ℝ) : (x ^ (2 : ℕ)) ^ t = x ^ (2 * t) := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
  norm_num

/-! ### The square of a mean -/

/-- **The square of a mean is at most the mean of the square.**  The difference
is the variance. -/
theorem sq_integral_le_integral_sq {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hfi : Integrable f μ)
    (hsq : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  set c : ℝ := ∫ x, f x ∂μ with hc
  have hcm : Integrable (fun x => 2 * c * f x) μ := hfi.const_mul _
  have hnn : 0 ≤ ∫ x, (f x - c) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hpoint : ∀ x : Ω, (f x - c) ^ 2 = (f x ^ 2 - 2 * c * f x) + c ^ 2 := fun x => by ring
  have hexp : ∫ x, (f x - c) ^ 2 ∂μ = (∫ x, f x ^ 2 ∂μ) - c ^ 2 := by
    calc ∫ x, (f x - c) ^ 2 ∂μ = ∫ x, ((f x ^ 2 - 2 * c * f x) + c ^ 2) ∂μ := by
          simp_rw [hpoint]
      _ = (∫ x, (f x ^ 2 - 2 * c * f x) ∂μ) + ∫ _x : Ω, c ^ 2 ∂μ :=
          integral_add (hsq.sub hcm) (integrable_const _)
      _ = ((∫ x, f x ^ 2 ∂μ) - ∫ x, 2 * c * f x ∂μ) + c ^ 2 := by
          rw [integral_sub hsq hcm, integral_const]
          simp
      _ = (∫ x, f x ^ 2 ∂μ) - c ^ 2 := by
          rw [integral_const_mul]
          rw [← hc]
          ring
  linarith

/-- **Jensen's inequality for a power.**  On a probability space the power of a
mean is at most the mean of the power. -/
theorem rpow_integral_le {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) (hfi : Integrable f μ)
    {r : ℝ} (hr : 1 ≤ r) (hgi : Integrable (fun ω => f ω ^ r) μ) :
    (∫ ω, f ω ∂μ) ^ r ≤ ∫ ω, f ω ^ r ∂μ := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ r) (Set.Ici 0) := by
    exact (Real.continuous_rpow_const (le_trans zero_le_one hr)).continuousOn
  exact (convexOn_rpow hr).map_integral_le hcont isClosed_Ici
    (Filter.Eventually.of_forall fun ω => hf ω) hfi hgi

/-! ### Fatou's lemma for an almost everywhere convergent sequence -/

/-- **Fatou's lemma.**  A nonnegative limit whose approximants have integrals
below `M` has an integral below `M`. -/
theorem integral_le_of_tendsto {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {M : ℝ}
    (hfnn : ∀ k, ∀ ω, 0 ≤ f k ω)
    (hg : Integrable g μ) (hgnn : ∀ ω, 0 ≤ g ω)
    (hconv : ∀ᵐ ω ∂μ, Filter.Tendsto (fun k => f k ω) Filter.atTop (nhds (g ω)))
    (hint : ∀ k, Integrable (f k) μ)
    (hbound : ∀ k, ∫ ω, f k ω ∂μ ≤ M) :
    ∫ ω, g ω ∂μ ≤ M := by
  have hM : 0 ≤ M := le_trans (integral_nonneg fun ω => hfnn 0 ω) (hbound 0)
  have hlint : ∀ k, ∫⁻ ω, ENNReal.ofReal (f k ω) ∂μ ≤ ENNReal.ofReal M := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hint k)
      (Filter.Eventually.of_forall fun ω => hfnn k ω)]
    exact ENNReal.ofReal_le_ofReal (hbound k)
  have hae : (fun ω => ENNReal.ofReal (g ω))
      =ᵐ[μ] fun ω => Filter.liminf (fun k => ENNReal.ofReal (f k ω)) Filter.atTop := by
    refine hconv.mono fun ω hω => ?_
    have : Filter.Tendsto (fun k => ENNReal.ofReal (f k ω)) Filter.atTop
        (nhds (ENNReal.ofReal (g ω))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hω
    exact this.liminf_eq.symm
  have hmeas : ∀ k, AEMeasurable (fun ω => ENNReal.ofReal (f k ω)) μ :=
    fun k => ENNReal.measurable_ofReal.comp_aemeasurable (hint k).aemeasurable
  have hfatou : ∫⁻ ω, ENNReal.ofReal (g ω) ∂μ ≤ ENNReal.ofReal M := by
    rw [lintegral_congr_ae hae]
    refine le_trans (lintegral_liminf_le' hmeas) ?_
    exact Filter.liminf_le_of_frequently_le (Filter.Frequently.of_forall hlint)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => hgnn ω)
    hg.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hM hfatou

/-! ### The power of a weighted sum -/

/-- **The power of a weighted sum against the weighted sum of the powers.**
This is the convexity of `t ↦ t^p` for `p ≥ 1`, with the weights normalized by
their total. -/
theorem rpow_weighted_sum_le {ι : Type} (s : Finset ι) (c V : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (hV : ∀ i ∈ s, 0 ≤ V i) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, c i * V i) ^ p
      ≤ (∑ i ∈ s, c i) ^ p * ∑ i ∈ s, (c i / (∑ j ∈ s, c j)) * V i ^ p := by
  classical
  set T : ℝ := ∑ j ∈ s, c j with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg hc
  have hp0 : p ≠ 0 := by intro h; rw [h] at hp; norm_num at hp
  rcases eq_or_lt_of_le hT0 with hTz | hTpos
  · -- every weight vanishes
    have hzero : ∀ i ∈ s, c i = 0 := by
      intro i hi
      have := (Finset.sum_eq_zero_iff_of_nonneg hc).mp hTz.symm i hi
      exact this
    have hL : ∑ i ∈ s, c i * V i = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hzero i hi, zero_mul]
    rw [hL, Real.zero_rpow hp0, ← hTz, Real.zero_rpow hp0, zero_mul]
  · have hw : ∀ i ∈ s, (0 : ℝ) ≤ c i / T := fun i hi => div_nonneg (hc i hi) hT0
    have hw' : ∑ i ∈ s, c i / T = 1 := by
      rw [← Finset.sum_div, ← hT, div_self (ne_of_gt hTpos)]
    have hjensen := Real.rpow_arith_mean_le_arith_mean_rpow s (fun i => c i / T) V hw hw' hV hp
    have hLsum : ∑ i ∈ s, (c i / T) * V i = (1 / T) * ∑ i ∈ s, c i * V i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [hLsum] at hjensen
    have hsum0 : (0 : ℝ) ≤ ∑ i ∈ s, c i * V i :=
      Finset.sum_nonneg fun i hi => mul_nonneg (hc i hi) (hV i hi)
    have hsplit : ((1 : ℝ) / T * ∑ i ∈ s, c i * V i) ^ p
        = (1 / T) ^ p * (∑ i ∈ s, c i * V i) ^ p :=
      Real.mul_rpow (by positivity) hsum0
    rw [hsplit] at hjensen
    have hTp : (0 : ℝ) < T ^ p := Real.rpow_pos_of_pos hTpos p
    have hinv : ((1 : ℝ) / T) ^ p = (T ^ p)⁻¹ := by
      rw [one_div, Real.inv_rpow hT0]
    rw [hinv] at hjensen
    have hmul := mul_le_mul_of_nonneg_left hjensen (le_of_lt hTp)
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hTp), one_mul] at hmul
    exact hmul

end Parking

end
