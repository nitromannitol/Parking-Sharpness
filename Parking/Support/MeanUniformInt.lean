/- Convergence in distribution together with a uniform `L^r` bound gives convergence
of the means.

This is the soft step between the convergence in distribution of
`n^{-1/4} u⃗_n(0)` and the last clause of `prop:oriented-scaling`
(`parking.tex:3151-3159`), the limit `n^{-1/4} E u⃗_n(0) → μ`.  Convergence in
distribution sees only bounded continuous test functions, so it says nothing about
means by itself; a uniform `L^r` bound with `r > 1` supplies the modulus `C M^{1-r}`
for the error made by truncating at the level `M`, uniformly over the family, and
the two are combined by the usual three-term estimate.  On the side of the limit the
same truncation error tends to zero by dominated convergence, and the nonnegativity
of the limit, which that step needs, is read off from the convergence in
distribution itself at a single test function.
-/
import Parking.Support.Continuum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open MeasureTheory Filter Topology

noncomputable section
namespace Parking

/-! ### Two test functions -/

/-- The truncation `y ↦ 0 ⊔ (y ⊓ M)`, as a bounded continuous function. -/
noncomputable def truncBdd (M : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun y => max 0 (min y M), by fun_prop⟩ |M| (by
      intro x y
      have hx0 : (0:ℝ) ≤ max 0 (min x M) := le_max_left _ _
      have hy0 : (0:ℝ) ≤ max 0 (min y M) := le_max_left _ _
      have hMa : M ≤ |M| := le_abs_self M
      have hxM : max 0 (min x M) ≤ |M| := max_le (abs_nonneg M) ((min_le_right _ _).trans hMa)
      have hyM : max 0 (min y M) ≤ |M| := max_le (abs_nonneg M) ((min_le_right _ _).trans hMa)
      simp only [ContinuousMap.coe_mk]
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith)

@[simp] theorem truncBdd_apply (M y : ℝ) : truncBdd M y = max 0 (min y M) := rfl

/-- The clamp of `-y` into `[0,1]`: a bounded continuous function that vanishes
exactly on the nonnegative half-line. -/
noncomputable def belowZero : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun y => max 0 (min 1 (-y)), by fun_prop⟩ 1 (by
      intro x y
      have hx0 : (0:ℝ) ≤ max 0 (min 1 (-x)) := le_max_left _ _
      have hy0 : (0:ℝ) ≤ max 0 (min 1 (-y)) := le_max_left _ _
      have hx1 : max 0 (min 1 (-x)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
      have hy1 : max 0 (min 1 (-y)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
      simp only [ContinuousMap.coe_mk]
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith)

@[simp] theorem belowZero_apply (y : ℝ) : belowZero y = max 0 (min 1 (-y)) := rfl

theorem belowZero_nonneg (y : ℝ) : 0 ≤ belowZero y := le_max_left _ _

theorem belowZero_le_one (y : ℝ) : belowZero y ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem belowZero_eq_zero_of_nonneg {y : ℝ} (hy : 0 ≤ y) : belowZero y = 0 := by
  rw [belowZero_apply, max_eq_left_iff]
  exact (min_le_right _ _).trans (by linarith)

theorem nonneg_of_belowZero_eq_zero {y : ℝ} (h : belowZero y = 0) : 0 ≤ y := by
  by_contra hy
  have hy : y < 0 := not_le.mp hy
  have h1 : (0:ℝ) < min 1 (-y) := lt_min one_pos (by linarith)
  rw [belowZero_apply, max_eq_left_iff] at h
  linarith

/-! ### The truncation error under an `L^r` bound -/

/-- For `y ≥ 0`, `M > 0` and `r ≥ 1`, the mass cut off by the truncation at level `M`
is at most `y^r M^{1-r}`. -/
theorem sub_trunc_le_rpow_div (r M y : ℝ) (hr : 1 ≤ r) (hM : 0 < M) (hy : 0 ≤ y) :
    y - max 0 (min y M) ≤ y ^ r / M ^ (r - 1) := by
  rcases lt_or_ge y M with h | h
  · have h2 : max 0 (min y M) = y := by
      rw [min_eq_left h.le, max_eq_right hy]
    rw [h2, sub_self]
    positivity
  · have hM0 : (0:ℝ) ≤ M := hM.le
    have h2 : max 0 (min y M) = M := by
      rw [min_eq_right h, max_eq_right hM0]
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le hM h
    have hpow : M ^ (r - 1) ≤ y ^ (r - 1) := Real.rpow_le_rpow hM0 h (by linarith)
    have hsplit : y ^ r = y * y ^ (r - 1) := by
      have hadd := Real.rpow_add hy0 1 (r - 1)
      rw [Real.rpow_one, show (1:ℝ) + (r - 1) = r by ring] at hadd
      exact hadd
    rw [h2, le_div_iff₀ (Real.rpow_pos_of_pos hM (r - 1)), hsplit]
    exact mul_le_mul (by linarith) hpow (Real.rpow_nonneg hM0 _) (by linarith)

/-- The truncation of a random variable is integrable on a finite measure. -/
theorem integrable_truncBdd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (Y : Ω → ℝ) (hY : AEStronglyMeasurable Y P) (M : ℝ) :
    Integrable (fun ω => truncBdd M (Y ω)) P := by
  refine Integrable.mono' (integrable_const |M|)
    ((truncBdd M).continuous.comp_aestronglyMeasurable hY) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  have h0 : (0:ℝ) ≤ max 0 (min (Y ω) M) := le_max_left _ _
  have hMa : M ≤ |M| := le_abs_self M
  have hle : max 0 (min (Y ω) M) ≤ |M| :=
    max_le (abs_nonneg M) ((min_le_right _ _).trans hMa)
  rw [truncBdd_apply, Real.norm_eq_abs, abs_of_nonneg h0]
  exact hle

/-- **The truncation error, bounded by the `r`-th moment.** -/
theorem abs_integral_sub_trunc_le_rpow {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hYnn : ∀ᵐ ω ∂P, 0 ≤ Y ω) (hYint : Integrable Y P)
    (r M C : ℝ) (hr : 1 ≤ r) (hM : 0 < M)
    (hYr : Integrable (fun ω => Y ω ^ r) P) (hYrC : ∫ ω, Y ω ^ r ∂P ≤ C) :
    |(∫ ω, Y ω ∂P) - ∫ ω, truncBdd M (Y ω) ∂P| ≤ C / M ^ (r - 1) := by
  have hMr : (0:ℝ) < M ^ (r - 1) := Real.rpow_pos_of_pos hM _
  have hti := integrable_truncBdd P Y hYint.aestronglyMeasurable M
  have hsub : (∫ ω, Y ω ∂P) - ∫ ω, truncBdd M (Y ω) ∂P
      = ∫ ω, (Y ω - truncBdd M (Y ω)) ∂P := (integral_sub hYint hti).symm
  have hnn : 0 ≤ ∫ ω, (Y ω - truncBdd M (Y ω)) ∂P := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hYnn] with ω hω
    show (0:ℝ) ≤ Y ω - truncBdd M (Y ω)
    rw [truncBdd_apply]
    have h1 : min (Y ω) M ≤ Y ω := min_le_left _ _
    have h2 : max 0 (min (Y ω) M) ≤ Y ω := max_le hω h1
    linarith
  have hle : ∫ ω, (Y ω - truncBdd M (Y ω)) ∂P
      ≤ ∫ ω, Y ω ^ r / M ^ (r - 1) ∂P := by
    refine integral_mono_ae (hYint.sub hti) (hYr.div_const _) ?_
    filter_upwards [hYnn] with ω hω
    show Y ω - truncBdd M (Y ω) ≤ Y ω ^ r / M ^ (r - 1)
    rw [truncBdd_apply]
    exact sub_trunc_le_rpow_div r M (Y ω) hr hM hω
  have hconst : ∫ ω, Y ω ^ r / M ^ (r - 1) ∂P = (∫ ω, Y ω ^ r ∂P) / M ^ (r - 1) :=
    integral_div _ _
  rw [hsub, abs_of_nonneg hnn]
  refine hle.trans ?_
  rw [hconst]
  have h := mul_le_mul_of_nonneg_right hYrC (le_of_lt (inv_pos.mpr hMr))
  simpa [div_eq_mul_inv] using h

/-- **The truncated means of a nonnegative integrable variable converge to its mean.** -/
theorem tendsto_integral_truncBdd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (Z : Ω → ℝ) (hZnn : ∀ᵐ ω ∂P, 0 ≤ Z ω) (hZint : Integrable Z P) :
    Tendsto (fun M : ℕ => ∫ ω, truncBdd (M : ℝ) (Z ω) ∂P) atTop (𝓝 (∫ ω, Z ω ∂P)) := by
  have hmeas : ∀ M : ℕ, AEStronglyMeasurable (fun ω => truncBdd (M : ℝ) (Z ω)) P :=
    fun M => (truncBdd (M : ℝ)).continuous.comp_aestronglyMeasurable hZint.aestronglyMeasurable
  refine tendsto_integral_of_dominated_convergence (fun ω => |Z ω|) hmeas hZint.abs ?_ ?_
  · intro M
    filter_upwards [hZnn] with ω hω
    rw [truncBdd_apply, Real.norm_eq_abs, abs_of_nonneg (le_max_left 0 (min (Z ω) (M : ℝ))),
      abs_of_nonneg hω]
    exact max_le hω (min_le_left _ _)
  · filter_upwards [hZnn] with ω hω
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop ⌈Z ω⌉₊] with M hM
    have hZM : Z ω ≤ (M : ℝ) := (Nat.le_ceil (Z ω)).trans (by exact_mod_cast hM)
    rw [truncBdd_apply, min_eq_left hZM, max_eq_right hω]

/-! ### The three-term estimate -/

/-- A family approximated uniformly by convergent families, with a modulus tending to
zero and with the approximants' limits converging, converges. -/
theorem tendsto_of_uniform_approx {ι : Type*} {l : Filter ι} (G : ι → ℝ) (G' : ℝ)
    (A : ℕ → ι → ℝ) (A' : ℕ → ℝ) (e : ℕ → ℝ)
    (hA : ∀ n, Tendsto (A n) l (𝓝 (A' n)))
    (hA' : Tendsto A' atTop (𝓝 G'))
    (he : Tendsto e atTop (𝓝 0))
    (hap : ∀ᶠ n in atTop, ∀ i, |G i - A n i| ≤ e n) :
    Tendsto G l (𝓝 G') := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h3 : (0:ℝ) < ε / 3 := by linarith
  have hsmall : ∀ᶠ n in atTop, e n < ε / 3 := he.eventually (gt_mem_nhds h3)
  have hlim : ∀ᶠ n in atTop, |A' n - G'| < ε / 3 := by
    filter_upwards [hA'.eventually (Metric.ball_mem_nhds G' h3)] with n hn
    rw [Real.dist_eq] at hn
    exact hn
  obtain ⟨n, hen, hGn, hapn⟩ := (hsmall.and (hlim.and hap)).exists
  have hmid := (hA n).eventually (Metric.ball_mem_nhds (A' n) h3)
  filter_upwards [hmid] with i hi
  have hmid' : |A n i - A' n| < ε / 3 := by
    rw [Real.dist_eq] at hi
    exact hi
  rw [Real.dist_eq]
  have h1 : |G i - A n i| < ε / 3 := lt_of_le_of_lt (hapn i) hen
  calc |G i - G'| ≤ |G i - A n i| + |A n i - G'| := abs_sub_le _ _ _
    _ ≤ |G i - A n i| + (|A n i - A' n| + |A' n - G'|) := by
        gcongr
        exact abs_sub_le _ _ _
    _ < ε / 3 + (ε / 3 + ε / 3) := by gcongr
    _ = ε := by ring

/-! ### Convergence of the means -/

/-- **The limit of a family of nonnegative variables is nonnegative.**  Read off from
the convergence in distribution at the single test function `belowZero`, which
vanishes exactly on the nonnegative half-line. -/
theorem ae_nonneg_of_tendsto_integral_belowZero {ι : Type*} {l : Filter ι} [l.NeBot]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] {P : (i : ι) → Measure (Ω i)}
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : (i : ι) → Ω i → ℝ} {Z : Ω' → ℝ} (hZm : AEStronglyMeasurable Z P')
    (hweak : Tendsto (fun i => ∫ ω, belowZero (X i ω) ∂(P i)) l
      (𝓝 (∫ ω, belowZero (Z ω) ∂P')))
    (hXnn : ∀ i, ∀ᵐ ω ∂(P i), 0 ≤ X i ω) :
    ∀ᵐ ω ∂P', 0 ≤ Z ω := by
  have hzero : ∀ i, ∫ ω, belowZero (X i ω) ∂(P i) = 0 := by
    intro i
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hXnn i] with ω hω
    exact belowZero_eq_zero_of_nonneg hω
  have hconst : Tendsto (fun i => ∫ ω, belowZero (X i ω) ∂(P i)) l (𝓝 0) := by
    simp only [hzero]
    exact tendsto_const_nhds
  have hlim : (∫ ω, belowZero (Z ω) ∂P') = 0 := tendsto_nhds_unique hweak hconst
  have hint : Integrable (fun ω => belowZero (Z ω)) P' := by
    refine Integrable.mono' (integrable_const (1:ℝ))
      (belowZero.continuous.comp_aestronglyMeasurable hZm) ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (belowZero_nonneg _)]
    exact belowZero_le_one _
  have hnn : 0 ≤ᵐ[P'] fun ω => belowZero (Z ω) :=
    Filter.Eventually.of_forall fun ω => belowZero_nonneg _
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hlim] with ω hω
  exact nonneg_of_belowZero_eq_zero hω

/-- **Convergence in distribution together with a uniform `L^r` bound, `r > 1`, gives
convergence of the means.**  The nonnegativity of the limit is not assumed: it is
part of the conclusion of the convergence in distribution. -/
theorem tendsto_integral_of_uniform_rpow {ι : Type*} {l : Filter ι} [l.NeBot]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] {P : (i : ι) → Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (P i)]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : (i : ι) → Ω i → ℝ} {Z : Ω' → ℝ}
    (hweak : ∀ F : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun i => ∫ ω, F (X i ω) ∂(P i)) l (𝓝 (∫ ω, F (Z ω) ∂P')))
    (hXnn : ∀ i, ∀ᵐ ω ∂(P i), 0 ≤ X i ω)
    (hXint : ∀ i, Integrable (X i) (P i))
    (hZm : AEStronglyMeasurable Z P') (hZint : Integrable Z P')
    (r C : ℝ) (hr : 1 < r)
    (hXr : ∀ i, Integrable (fun ω => X i ω ^ r) (P i))
    (hXrC : ∀ i, ∫ ω, X i ω ^ r ∂(P i) ≤ C) :
    Tendsto (fun i => ∫ ω, X i ω ∂(P i)) l (𝓝 (∫ ω, Z ω ∂P')) := by
  have hZnn : ∀ᵐ ω ∂P', 0 ≤ Z ω :=
    ae_nonneg_of_tendsto_integral_belowZero hZm (hweak belowZero) hXnn
  have hr1 : (0:ℝ) < r - 1 := by linarith
  have hmod : Tendsto (fun M : ℕ => C / (M : ℝ) ^ (r - 1)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun M : ℕ => (M : ℝ) ^ (r - 1)) atTop atTop :=
      (tendsto_rpow_atTop hr1).comp tendsto_natCast_atTop_atTop
    exact tendsto_const_nhds.div_atTop hpow
  refine tendsto_of_uniform_approx _ _
    (fun M i => ∫ ω, truncBdd (M : ℝ) (X i ω) ∂(P i))
    (fun M => ∫ ω, truncBdd (M : ℝ) (Z ω) ∂P')
    (fun M => C / (M : ℝ) ^ (r - 1))
    (fun M => hweak (truncBdd (M : ℝ)))
    (tendsto_integral_truncBdd P' Z hZnn hZint) hmod ?_
  filter_upwards [eventually_ge_atTop 1] with M hM i
  have hM0 : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM
  exact abs_integral_sub_trunc_le_rpow (P i) (X i) (hXnn i) (hXint i) r (M : ℝ) C hr.le hM0
    (hXr i) (hXrC i)

end Parking
end
