/-
The continuum overlap kernel of the directed field (`parking.tex:3175-3203`).

The covariance of the continuum directed field at two space-time points is,
up to the factor `Var η(0)`, the time integral of the heat kernel of the
total elapsed time over the common window: the overlap.  This module defines
that kernel, identifies it with the plain integral of the product of the two
test functions of the space-time noise, writes it as a difference of time
primitives, and proves its joint continuity together with a square-root bound
near the diagonal `max s s' = T`.

- `Parking.contHeat_sub`, `Parking.contHeat_zero_neg`: the heat kernel depends
  on the displacement only, and is even in it.
- `Parking.contHeat_zero_eq`, `Parking.contHeat_zero_le`: the exact value and
  the uniform spatial bound of the zero-mean heat kernel.
- `Parking.contOverlap`: the overlap kernel.
- `Parking.integral_contNoiseTest_mul_eq_contOverlap`: the bridge to the
  white-noise test functions.
- `Parking.contHeatTimeIntegral`: the time primitive of the heat kernel.
- `Parking.contOverlap_eq_timeIntegral`: the primitive difference form.
- `Parking.contOverlap_le`: the square-root bound.
- `Parking.continuous_contOverlap`: joint continuity.
-/
import Parking.Support.TightCovHeat

open MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section
namespace Parking

/-- The heat kernel depends only on the displacement. -/
theorem contHeat_sub (t x x' : ℝ) : contHeat t x x' = contHeat t 0 (x' - x) := by
  simp only [contHeat, gaussianPDFReal, sub_zero]

/-- The zero-mean heat kernel is even in space. -/
theorem contHeat_zero_neg (t d : ℝ) : contHeat t 0 (-d) = contHeat t 0 d := by
  simp only [contHeat, gaussianPDFReal, sub_zero, neg_sq]

/-- The heat kernel vanishes at nonpositive times. -/
theorem contHeat_of_nonpos {t : ℝ} (ht : t ≤ 0) (x y : ℝ) : contHeat t x y = 0 := by
  have h0 : Real.toNNReal (t / 4) = 0 := by
    rw [Real.toNNReal_eq_zero]
    linarith
  unfold contHeat
  rw [h0]
  exact congrFun (gaussianPDFReal_zero_var x) y

/-- **Exact value of the zero-mean heat kernel**: the `t^{-1/2}` profile times
the Gaussian factor. -/
theorem contHeat_zero_eq {t : ℝ} (ht : 0 < t) (d : ℝ) :
    contHeat t 0 d = Real.sqrt (2 / Real.pi) * (Real.sqrt t)⁻¹ * Real.exp (-2 * d ^ 2 / t) := by
  have ht4 : (0 : ℝ) ≤ t / 4 := by linarith
  have hcoe : ((Real.toNNReal (t / 4) : NNReal) : ℝ) = t / 4 := Real.coe_toNNReal _ ht4
  simp only [contHeat, gaussianPDFReal]
  rw [hcoe, sub_zero]
  have hsqrt : Real.sqrt (2 * Real.pi * (t / 4))
      = Real.sqrt Real.pi * Real.sqrt t / Real.sqrt 2 := by
    rw [show 2 * Real.pi * (t / 4) = Real.pi * t / 2 by ring,
      Real.sqrt_div (mul_nonneg Real.pi_pos.le ht.le),
      Real.sqrt_mul Real.pi_pos.le]
  have hpref : (Real.sqrt Real.pi * Real.sqrt t / Real.sqrt 2)⁻¹
      = Real.sqrt (2 / Real.pi) * (Real.sqrt t)⁻¹ := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
    ring
  have hexp : -d ^ 2 / (2 * (t / 4)) = -2 * d ^ 2 / t := by
    rw [show (2 : ℝ) * (t / 4) = t / 2 by ring]
    field_simp [ht.ne']
  rw [hsqrt, hpref, hexp]

/-- **The uniform spatial bound** of the zero-mean heat kernel. -/
theorem contHeat_zero_le {t : ℝ} (ht : 0 < t) (d : ℝ) :
    contHeat t 0 d ≤ Real.sqrt (2 / Real.pi) * (Real.sqrt t)⁻¹ := by
  rw [contHeat_zero_eq ht d]
  have hpos : (0 : ℝ) ≤ Real.sqrt (2 / Real.pi) * (Real.sqrt t)⁻¹ :=
    mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hexp1 : Real.exp (-2 * d ^ 2 / t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hnum : (0 : ℝ) ≤ 2 * d ^ 2 := by positivity
    have hquot : (0 : ℝ) ≤ 2 * d ^ 2 / t := div_nonneg hnum ht.le
    rw [show -2 * d ^ 2 / t = -(2 * d ^ 2 / t) by ring]
    exact neg_nonpos.mpr hquot
  calc Real.sqrt (2 / Real.pi) * (Real.sqrt t)⁻¹ * Real.exp (-2 * d ^ 2 / t)
      ≤ Real.sqrt (2 / Real.pi) * (Real.sqrt t)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hexp1 hpos
    _ = Real.sqrt (2 / Real.pi) * (Real.sqrt t)⁻¹ := mul_one _

/-- The heat kernel is continuous in the spatial argument at every time. -/
theorem continuous_contHeat_zero (t : ℝ) : Continuous fun d => contHeat t 0 d := by
  simp only [contHeat, gaussianPDFReal]
  exact continuous_const.mul (Real.continuous_exp.comp
    ((((continuous_id'.sub continuous_const).pow 2).neg).div_const _))

/-- The heat kernel is measurable in time at zero mean. -/
theorem measurable_contHeat_zero (d : ℝ) : Measurable fun ψ : ℝ => contHeat ψ 0 d := by
  have h : (fun ψ : ℝ => contHeat ψ 0 d)
      = (fun q : ℝ × ℝ => contHeat q.1 0 q.2) ∘ (fun ψ : ℝ => (ψ, d)) := rfl
  rw [h]
  exact (measurable_contHeat_uncurry 0).comp (measurable_id.prodMk measurable_const)

/-- Twice the maximum, in displacement form. -/
theorem two_mul_max (a b : ℝ) : 2 * max a b = a + b + |a - b| := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- **The overlap kernel** of the continuum directed field: the time integral
of the heat kernel of the total elapsed time over the common window.  The
covariance of the field at `u` and `u'` is `Var η(0) · contOverlap T u u'`. -/
def contOverlap (T : ℝ) (u u' : Fin 2 → ℝ) : ℝ :=
  ∫ θ : ℝ, Set.indicator (Set.Ioo 0 (T - max (u 0) (u' 0)))
    (fun θ => contHeat (2 * θ + |u 0 - u' 0|) 0 (u 1 - u' 1)) θ

/-- The overlap vanishes when one point is at or beyond the horizon. -/
theorem contOverlap_of_le {T : ℝ} {u u' : Fin 2 → ℝ} (h : T ≤ max (u 0) (u' 0)) :
    contOverlap T u u' = 0 := by
  unfold contOverlap
  rw [Set.Ioo_eq_empty (not_lt.mpr (by linarith : T - max (u 0) (u' 0) ≤ 0))]
  simp

/-- The overlap kernel is nonnegative. -/
theorem contOverlap_nonneg (T : ℝ) (u u' : Fin 2 → ℝ) : 0 ≤ contOverlap T u u' := by
  unfold contOverlap
  refine integral_nonneg fun θ => ?_
  by_cases h : θ ∈ Set.Ioo 0 (T - max (u 0) (u' 0))
  · rw [Set.indicator_of_mem h]
    exact contHeat_nonneg _ _ _
  · simp [Set.indicator_of_notMem h]

/-- **The overlap kernel is the plain integral of the product of the two test
functions** of the space-time noise: substitute `θ = t - max s s'` in the
semigroup overlap of `integral_contNoiseTest_mul`. -/
theorem integral_contNoiseTest_mul_eq_contOverlap (T s s' x x' : ℝ) :
    ∫ p : ℝ × ℝ, contNoiseTest T s x p * contNoiseTest T s' x' p
      = contOverlap T ![s, x] ![s', x'] := by
  rw [integral_contNoiseTest_mul]
  unfold contOverlap
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases hT : max s s' < T
  · rw [MeasureTheory.integral_indicator measurableSet_Ioo,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hT.le]
    have hkey : (∫ t in (max s s')..T, contHeat (2 * t - s - s') x x')
        = ∫ θ in (0 : ℝ)..(T - max s s'), contHeat (2 * θ + |s - s'|) 0 (x - x') := by
      have h1 : (∫ t in (max s s')..T, contHeat (2 * t - s - s') x x')
          = ∫ θ in (max s s' - max s s')..(T - max s s'),
            contHeat (2 * (θ + max s s') - s - s') x x' := by
        have h2 := intervalIntegral.integral_comp_add_right
          (f := fun t : ℝ => contHeat (2 * t - s - s') x x') (max s s')
          (a := max s s' - max s s') (b := T - max s s')
        rw [sub_add_cancel, sub_add_cancel] at h2
        rw [← h2]
      rw [h1, sub_self]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      have e1 : 2 * (θ + max s s') - s - s' = 2 * θ + |s - s'| := by
        rw [show 2 * (θ + max s s') = 2 * θ + 2 * max s s' by ring, two_mul_max]
        ring
      rw [e1, contHeat_sub, show x' - x = -(x - x') by ring, contHeat_zero_neg]
    rw [hkey, intervalIntegral.integral_of_le (sub_nonneg.mpr hT.le),
      MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← MeasureTheory.integral_indicator measurableSet_Ioo]
  · have h1 : Set.Ioo (max s s') T = ∅ := Set.Ioo_eq_empty (not_lt.mpr (le_of_not_gt hT))
    have h2 : Set.Ioo 0 (T - max s s') = ∅ :=
      Set.Ioo_eq_empty (not_lt.mpr (by linarith : T - max s s' ≤ 0))
    rw [h1, h2]
    simp

/-- The overlap kernel is symmetric. -/
theorem contOverlap_symm (T : ℝ) (u u' : Fin 2 → ℝ) :
    contOverlap T u u' = contOverlap T u' u := by
  conv_lhs => rw [show u = ![u 0, u 1] from List.ofFn_inj.mp rfl,
    show u' = ![u' 0, u' 1] from List.ofFn_inj.mp rfl,
    ← integral_contNoiseTest_mul_eq_contOverlap]
  conv_rhs => rw [show u' = ![u' 0, u' 1] from List.ofFn_inj.mp rfl,
    show u = ![u 0, u 1] from List.ofFn_inj.mp rfl,
    ← integral_contNoiseTest_mul_eq_contOverlap]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  ring

/-- The `√(2/π) (√(2θ))⁻¹` bound of the heat kernel collapses to the
`(√(πθ))⁻¹` profile: the constants cancel. -/
theorem sqrt_two_div_pi_mul_sqrt_two_mul_inv {θ : ℝ} (_hθ : 0 < θ) :
    Real.sqrt (2 / Real.pi) * (Real.sqrt (2 * θ))⁻¹ = (Real.sqrt (Real.pi * θ))⁻¹ := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) θ, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_mul Real.pi_pos.le θ, mul_inv, mul_inv, div_eq_mul_inv, mul_right_comm,
    ← mul_assoc, mul_inv_cancel₀ h2.ne', one_mul, mul_comm]

/-- The zero-mean heat kernel is integrable in time on every bounded
interval: it is dominated by the integrable `1/√ψ` profile. -/
theorem integrableOn_contHeat_zero_Ioc (a b : ℝ) (d : ℝ) :
    IntegrableOn (fun ψ : ℝ => contHeat ψ 0 d) (Set.Ioc a b) volume := by
  have hbase : IntegrableOn (fun ψ : ℝ => Real.sqrt 2 * (Real.sqrt (Real.pi * (ψ - 0)))⁻¹)
      (Set.Ioc 0 b) volume := by
    refine IntegrableOn.congr_set_ae
      ((integrableOn_inv_sqrt_pi_sub 0 b).const_mul (Real.sqrt 2)) ?_
    exact Ioo_ae_eq_Ioc.symm
  have hG : Integrable (Set.indicator (Set.Ioc 0 b)
      (fun ψ : ℝ => Real.sqrt 2 * (Real.sqrt (Real.pi * ψ))⁻¹)) volume := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioc]
    refine hbase.congr_fun ?_ measurableSet_Ioc
    intro ψ _
    simp only [sub_zero]
  refine Integrable.mono' (hG.integrableOn)
    ((measurable_contHeat_zero d).aestronglyMeasurable) ?_
  refine (ae_restrict_mem measurableSet_Ioc).mono fun ψ hψ => ?_
  by_cases h0 : (0 : ℝ) < ψ
  · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨h0, hψ.2⟩), Real.norm_eq_abs,
      abs_of_nonneg (contHeat_nonneg _ _ _)]
    calc contHeat ψ 0 d
        ≤ Real.sqrt (2 / Real.pi) * (Real.sqrt ψ)⁻¹ := contHeat_zero_le h0 d
      _ = Real.sqrt 2 * (Real.sqrt (Real.pi * ψ))⁻¹ := by
          rw [Real.sqrt_mul Real.pi_pos.le, mul_inv,
            Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv]
          ring
  · rw [Set.indicator_of_notMem (fun h => h0 h.1),
      contHeat_of_nonpos (not_lt.mp h0) 0 d]
    simp

/-- The zero-mean heat kernel is interval-integrable in time. -/
theorem intervalIntegrable_contHeat_zero (a b : ℝ) (d : ℝ) :
    IntervalIntegrable (fun ψ : ℝ => contHeat ψ 0 d) volume a b :=
  ⟨integrableOn_contHeat_zero_Ioc a b d, integrableOn_contHeat_zero_Ioc b a d⟩

/-- **The time primitive** of the zero-mean heat kernel: the integral over the
window `(0, a)`, which is empty for `a ≤ 0`. -/
def contHeatTimeIntegral (a d : ℝ) : ℝ :=
  ∫ ψ : ℝ, Set.indicator (Set.Ioo 0 a) (fun ψ => contHeat ψ 0 d) ψ

/-- The primitive as an interval integral, for `0 ≤ a`. -/
theorem contHeatTimeIntegral_eq {a : ℝ} (ha : 0 ≤ a) (d : ℝ) :
    contHeatTimeIntegral a d = ∫ ψ in (0 : ℝ)..a, contHeat ψ 0 d := by
  unfold contHeatTimeIntegral
  rw [MeasureTheory.integral_indicator measurableSet_Ioo,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le ha]

/-- The primitive vanishes for `a ≤ 0`. -/
theorem contHeatTimeIntegral_nonpos {a : ℝ} (ha : a ≤ 0) (d : ℝ) :
    contHeatTimeIntegral a d = 0 := by
  unfold contHeatTimeIntegral
  rw [Set.Ioo_eq_empty (not_lt.mpr ha)]
  simp

/-- **The primitive is jointly continuous**: dominated convergence against the
`1/√ψ` profile, which is integrable on every bounded window. -/
theorem continuousAt_contHeatTimeIntegral (a₀ d₀ : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => contHeatTimeIntegral p.1 p.2) (a₀, d₀) := by
  unfold contHeatTimeIntegral
  refine tendsto_integral_filter_of_dominated_convergence
    (Set.indicator (Set.Ioo 0 (max a₀ 0 + 1))
      fun ψ => Real.sqrt (2 / Real.pi) * (Real.sqrt ψ)⁻¹)
    (Filter.Eventually.of_forall fun p : ℝ × ℝ =>
      (((measurable_contHeat_zero p.2).indicator measurableSet_Ioo).aestronglyMeasurable))
    ?_ ?_ ?_
  · have hopen : {p : ℝ × ℝ | p.1 < max a₀ 0 + 1} ∈ 𝓝 (a₀, d₀) := by
      refine (isOpen_lt continuous_fst continuous_const).mem_nhds ?_
      exact lt_of_le_of_lt (le_max_left a₀ 0) (lt_add_one _)
    filter_upwards [hopen] with p hp
    refine Filter.Eventually.of_forall fun ψ => ?_
    by_cases hψ : ψ ∈ Set.Ioo 0 p.1
    · have hψc : ψ ∈ Set.Ioo 0 (max a₀ 0 + 1) := ⟨hψ.1, lt_trans hψ.2 hp⟩
      rw [Set.indicator_of_mem hψ, Set.indicator_of_mem hψc, Real.norm_eq_abs,
        abs_of_nonneg (contHeat_nonneg _ _ _)]
      exact contHeat_zero_le hψ.1 _
    · rw [Set.indicator_of_notMem hψ, Real.norm_eq_abs, abs_zero]
      exact Set.indicator_nonneg (fun θ _ => mul_nonneg (Real.sqrt_nonneg _)
        (inv_nonneg.mpr (Real.sqrt_nonneg _))) ψ
  · have hbase : IntegrableOn (fun ψ : ℝ => Real.sqrt 2 * (Real.sqrt (Real.pi * (ψ - 0)))⁻¹)
        (Set.Ioo 0 (max a₀ 0 + 1)) volume :=
      (integrableOn_inv_sqrt_pi_sub 0 (max a₀ 0 + 1)).const_mul (Real.sqrt 2)
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioo]
    refine hbase.congr_fun ?_ measurableSet_Ioo
    intro ψ _
    show Real.sqrt 2 * (Real.sqrt (Real.pi * (ψ - 0)))⁻¹
        = Real.sqrt (2 / Real.pi) * (Real.sqrt ψ)⁻¹
    rw [sub_zero, Real.sqrt_mul Real.pi_pos.le, mul_inv,
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv]
    ring
  · rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ ((Set.toFinite ({0, a₀} : Set ℝ)).measure_zero volume)
    intro ψ hψ
    by_contra hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
    apply hψ
    rcases hmem with ⟨h0, ha⟩
    rcases lt_trichotomy ψ 0 with hlt | heq | hgt
    · have hz : (fun p : ℝ × ℝ => Set.indicator (Set.Ioo 0 p.1)
          (fun ψ' => contHeat ψ' 0 p.2) ψ) = fun _ => (0 : ℝ) := by
        funext p
        exact Set.indicator_of_notMem (fun h => absurd h.1 (not_lt.mpr hlt.le)) _
      rw [hz, Set.indicator_of_notMem (fun h => absurd h.1 (not_lt.mpr hlt.le))]
      exact tendsto_const_nhds
    · exact absurd heq h0
    · rcases lt_or_gt_of_ne ha with hla | hga
      · have hopen : {p : ℝ × ℝ | ψ < p.1} ∈ 𝓝 (a₀, d₀) :=
          (isOpen_lt continuous_const continuous_fst).mem_nhds hla
        have hev : (fun p : ℝ × ℝ => Set.indicator (Set.Ioo 0 p.1)
              (fun ψ' => contHeat ψ' 0 p.2) ψ)
            =ᶠ[𝓝 (a₀, d₀)] fun p => contHeat ψ 0 p.2 := by
          filter_upwards [hopen] with p hp
          exact Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨hgt, hp⟩) _
        rw [Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨hgt, hla⟩)]
        exact Filter.Tendsto.congr' hev.symm
          (((continuous_contHeat_zero ψ).comp continuous_snd).continuousAt)
      · have hopen : {p : ℝ × ℝ | p.1 < ψ} ∈ 𝓝 (a₀, d₀) :=
          (isOpen_lt continuous_fst continuous_const).mem_nhds hga
        have hev : (fun p : ℝ × ℝ => Set.indicator (Set.Ioo 0 p.1)
              (fun ψ' => contHeat ψ' 0 p.2) ψ)
            =ᶠ[𝓝 (a₀, d₀)] fun _ => (0 : ℝ) := by
          filter_upwards [hopen] with p hp
          exact Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hp.le)) _
        rw [Set.indicator_of_notMem (fun h => absurd h.2 (not_lt.mpr hga.le))]
        exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds

/-- The primitive is jointly continuous. -/
theorem continuous_contHeatTimeIntegral :
    Continuous fun p : ℝ × ℝ => contHeatTimeIntegral p.1 p.2 :=
  continuous_iff_continuousAt.mpr fun ⟨a, d⟩ => continuousAt_contHeatTimeIntegral a d

/-- **The overlap kernel in primitive difference form**, valid below the
horizon: substitute `ψ = 2θ + |s - s'|`. -/
theorem contOverlap_eq_timeIntegral {T s s' : ℝ} (hs : s ≤ T) (hs' : s' ≤ T) (x x' : ℝ) :
    contOverlap T ![s, x] ![s', x']
      = (contHeatTimeIntegral (2 * T - s - s') (x - x')
          - contHeatTimeIntegral |s - s'| (x - x')) / 2 := by
  have hmx : (0 : ℝ) ≤ T - max s s' := by
    have hle : max s s' ≤ T := max_le hs hs'
    linarith
  have hδ : (0 : ℝ) ≤ |s - s'| := abs_nonneg _
  have hB : (0 : ℝ) ≤ 2 * T - s - s' := by linarith
  unfold contOverlap
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [MeasureTheory.integral_indicator measurableSet_Ioo,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hmx]
  have hsub : (∫ θ in (0 : ℝ)..(T - max s s'), contHeat (2 * θ + |s - s'|) 0 (x - x'))
      = (2 : ℝ)⁻¹ • ∫ ψ in (2 * 0 + |s - s'|)..(2 * (T - max s s') + |s - s'|),
        contHeat ψ 0 (x - x') := by
    rw [show (fun θ : ℝ => contHeat (2 * θ + |s - s'|) 0 (x - x'))
        = fun θ => (fun ψ : ℝ => contHeat ψ 0 (x - x')) (2 * θ + |s - s'|) from rfl]
    exact intervalIntegral.integral_comp_mul_add
      (fun ψ : ℝ => contHeat ψ 0 (x - x')) two_ne_zero |s - s'|
  rw [hsub, smul_eq_mul, show 2 * (0 : ℝ) + |s - s'| = |s - s'| by ring,
    show 2 * (T - max s s') + |s - s'| = 2 * T - s - s' by
      rw [show 2 * (T - max s s') = 2 * T - 2 * max s s' by ring, two_mul_max]
      ring]
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_contHeat_zero 0 |s - s'| (x - x'))
    (intervalIntegrable_contHeat_zero |s - s'| (2 * T - s - s') (x - x'))
  rw [← contHeatTimeIntegral_eq hδ, ← contHeatTimeIntegral_eq hB] at hadj
  linarith

/-- **The square-root bound of the overlap kernel**: dominated by the
integrable `1/√(πθ)` profile on the common window. -/
theorem contOverlap_le (T : ℝ) (u u' : Fin 2 → ℝ) :
    contOverlap T u u'
      ≤ 2 * Real.sqrt (max (T - max (u 0) (u' 0)) 0) / Real.sqrt Real.pi := by
  by_cases hmx : max (u 0) (u' 0) < T
  · have hc0 : (0 : ℝ) < T - max (u 0) (u' 0) := by linarith
    have hδ : (0 : ℝ) ≤ |u 0 - u' 0| := abs_nonneg _
    have hGint : Integrable (Set.indicator (Set.Ioo 0 (T - max (u 0) (u' 0)))
        (fun θ : ℝ => (Real.sqrt (Real.pi * θ))⁻¹)) volume := by
      rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioo]
      refine (integrableOn_inv_sqrt_pi_sub 0 (T - max (u 0) (u' 0))).congr_fun ?_
        measurableSet_Ioo
      intro θ _
      simp only [sub_zero]
    have hnorm : ∀ θ : ℝ, ‖Set.indicator (Set.Ioo 0 (T - max (u 0) (u' 0)))
          (fun θ => contHeat (2 * θ + |u 0 - u' 0|) 0 (u 1 - u' 1)) θ‖
        ≤ Set.indicator (Set.Ioo 0 (T - max (u 0) (u' 0)))
          (fun θ => (Real.sqrt (Real.pi * θ))⁻¹) θ := by
      intro θ
      by_cases hθ : θ ∈ Set.Ioo 0 (T - max (u 0) (u' 0))
      · rw [Set.indicator_of_mem hθ, Set.indicator_of_mem hθ, Real.norm_eq_abs,
          abs_of_nonneg (contHeat_nonneg _ _ _)]
        have h2θ : (0 : ℝ) < 2 * θ := by linarith [hθ.1]
        calc contHeat (2 * θ + |u 0 - u' 0|) 0 (u 1 - u' 1)
            ≤ Real.sqrt (2 / Real.pi) * (Real.sqrt (2 * θ + |u 0 - u' 0|))⁻¹ :=
              contHeat_zero_le (by linarith) _
          _ ≤ Real.sqrt (2 / Real.pi) * (Real.sqrt (2 * θ))⁻¹ :=
              mul_le_mul_of_nonneg_left
                (inv_anti₀ (Real.sqrt_pos.mpr h2θ)
                  (Real.sqrt_le_sqrt (by linarith)))
                (Real.sqrt_nonneg _)
          _ = (Real.sqrt (Real.pi * θ))⁻¹ :=
              sqrt_two_div_pi_mul_sqrt_two_mul_inv hθ.1
      · rw [Set.indicator_of_notMem hθ, Real.norm_eq_abs, abs_zero]
        exact Set.indicator_nonneg (fun θ _ => inv_nonneg.mpr (Real.sqrt_nonneg _)) θ
    have hLHSint : Integrable (Set.indicator (Set.Ioo 0 (T - max (u 0) (u' 0)))
        (fun θ : ℝ => contHeat (2 * θ + |u 0 - u' 0|) 0 (u 1 - u' 1))) volume :=
      hGint.mono'
        ((((measurable_contHeat_zero (u 1 - u' 1)).comp
          ((measurable_id.const_mul 2).add_const |u 0 - u' 0|)).indicator
          measurableSet_Ioo).aestronglyMeasurable)
        (Filter.Eventually.of_forall hnorm)
    have hpt : ∀ θ : ℝ, Set.indicator (Set.Ioo 0 (T - max (u 0) (u' 0)))
          (fun θ => contHeat (2 * θ + |u 0 - u' 0|) 0 (u 1 - u' 1)) θ
        ≤ Set.indicator (Set.Ioo 0 (T - max (u 0) (u' 0)))
          (fun θ => (Real.sqrt (Real.pi * θ))⁻¹) θ :=
      fun θ => le_trans (Real.le_norm_self _) (hnorm θ)
    calc contOverlap T u u'
        ≤ ∫ θ : ℝ, Set.indicator (Set.Ioo 0 (T - max (u 0) (u' 0)))
            (fun θ => (Real.sqrt (Real.pi * θ))⁻¹) θ := by
          unfold contOverlap
          exact integral_mono_ae hLHSint hGint (Filter.Eventually.of_forall hpt)
      _ = ∫ θ in Set.Ioo 0 (T - max (u 0) (u' 0)), (Real.sqrt (Real.pi * θ))⁻¹ :=
          MeasureTheory.integral_indicator measurableSet_Ioo
      _ = ∫ θ in Set.Ioo 0 (T - max (u 0) (u' 0)), (Real.sqrt (Real.pi * (θ - 0)))⁻¹ := by
          refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
          simp only [sub_zero]
      _ = 2 * Real.sqrt (T - max (u 0) (u' 0) - 0) / Real.sqrt Real.pi :=
          integral_inv_sqrt_pi_sub hc0.le
      _ = 2 * Real.sqrt (max (T - max (u 0) (u' 0)) 0) / Real.sqrt Real.pi := by
          rw [sub_zero, max_eq_left hc0.le]
  · rw [contOverlap_of_le (le_of_not_gt hmx)]
    exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

/-- **The overlap kernel is jointly continuous.**  Below the horizon this is
the primitive difference form; at and above the horizon the kernel is zero
with the square-root bound. -/
theorem continuous_contOverlap (T : ℝ) :
    Continuous fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => contOverlap T p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  intro ⟨u, u'⟩
  by_cases hmx : max (u 0) (u' 0) < T
  · have hmap1 : Continuous fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
        (2 * T - p.1 0 - p.2 0, p.1 1 - p.2 1) :=
      ((continuous_const.sub ((continuous_apply 0).comp continuous_fst)).sub
        ((continuous_apply 0).comp continuous_snd)).prodMk
        (((continuous_apply 1).comp continuous_fst).sub
          ((continuous_apply 1).comp continuous_snd))
    have hmap2 : Continuous fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
        (|p.1 0 - p.2 0|, p.1 1 - p.2 1) :=
      ((continuous_abs.comp (((continuous_apply 0).comp continuous_fst).sub
        ((continuous_apply 0).comp continuous_snd)))).prodMk
        (((continuous_apply 1).comp continuous_fst).sub
          ((continuous_apply 1).comp continuous_snd))
    have hg : Continuous fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
        (contHeatTimeIntegral (2 * T - p.1 0 - p.2 0) (p.1 1 - p.2 1)
          - contHeatTimeIntegral |p.1 0 - p.2 0| (p.1 1 - p.2 1)) / 2 :=
      ((continuous_contHeatTimeIntegral.comp hmap1).sub
        (continuous_contHeatTimeIntegral.comp hmap2)).div_const 2
    have hopen : {p : (Fin 2 → ℝ) × (Fin 2 → ℝ) | max (p.1 0) (p.2 0) < T}
        ∈ 𝓝 (u, u') :=
      (isOpen_lt (((continuous_apply 0).comp continuous_fst).max
        ((continuous_apply 0).comp continuous_snd)) continuous_const).mem_nhds hmx
    have hev : (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
          (contHeatTimeIntegral (2 * T - p.1 0 - p.2 0) (p.1 1 - p.2 1)
            - contHeatTimeIntegral |p.1 0 - p.2 0| (p.1 1 - p.2 1)) / 2)
        =ᶠ[𝓝 (u, u')] fun p => contOverlap T p.1 p.2 := by
      filter_upwards [hopen] with p hp
      conv_rhs => rw [show p.1 = ![p.1 0, p.1 1] from List.ofFn_inj.mp rfl,
        show p.2 = ![p.2 0, p.2 1] from List.ofFn_inj.mp rfl]
      rw [contOverlap_eq_timeIntegral
        (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hp))
        (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hp))]
    exact hg.continuousAt.congr hev
  · replace hmx : T ≤ max (u 0) (u' 0) := le_of_not_gt hmx
    have hval : contOverlap T u u' = 0 := contOverlap_of_le hmx
    have hcont : Continuous fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
        2 * Real.sqrt (max (T - max (p.1 0) (p.2 0)) 0) / Real.sqrt Real.pi :=
      (continuous_const.mul (Real.continuous_sqrt.comp
        ((continuous_const.sub (((continuous_apply 0).comp continuous_fst).max
          ((continuous_apply 0).comp continuous_snd))).max continuous_const))).div_const _
    have hAt := (hcont.continuousAt (x := (u, u'))).tendsto
    have hval0 : 2 * Real.sqrt (max (T - max ((u, u').1 0) ((u, u').2 0)) 0)
        / Real.sqrt Real.pi = 0 := by
      show 2 * Real.sqrt (max (T - max (u 0) (u' 0)) 0) / Real.sqrt Real.pi = 0
      rw [show max (T - max (u 0) (u' 0)) 0 = 0 from max_eq_right (by linarith),
        Real.sqrt_zero, mul_zero, zero_div]
    rw [hval0] at hAt
    show Filter.Tendsto (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => contOverlap T p.1 p.2) (𝓝 (u, u'))
      (𝓝 (contOverlap T u u'))
    rw [hval]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hAt
      (Filter.Eventually.of_forall fun p => contOverlap_nonneg T p.1 p.2)
      (Filter.Eventually.of_forall fun p => contOverlap_le T p.1 p.2)

end Parking
end
