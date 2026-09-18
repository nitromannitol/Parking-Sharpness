/-
Quantitative bounds on the covariance structure of the continuum noise field
`contZ`, used to build a jointly continuous version of a box-clamped copy of
the field.

The field does not satisfy a single-exponent Kolmogorov condition on the
whole plane at the second moment: its natural local modulus is Hölder-1/2 in
space and Hölder-1/4 in time (the standard feature of a stochastic-heat-type
field), so no exponent `q > 2` bounds the plain `L²` increment by `edist ^ q`
uniformly at every scale of `(s, x)` and `(s', x')`: the pure-space slice
forces `q ≤ 1` and the pure-time slice forces `q ≤ 1/2`, and no exponent
satisfies both requirements simultaneously at every scale (checked directly
against the two slice computations below).  This module proves the two slice
bounds; `TightNoiseModification.lean` combines them on a bounded box and
passes to a higher moment to reach an exponent above `2`.

- `Parking.noiseVarDiff`: the variance of the increment of the noise test
  functions, read off the overlap kernel.
- `Parking.noiseVarDiff_time_le`: the pure-time slice, Hölder-`1/2`.
- `Parking.noiseVarDiff_space_le`: the pure-space slice, Hölder-`1`.
- `Parking.noiseVarDiff_le_two_mul_add`: the triangle bound through an
  intermediate point.
-/
import Parking.Support.TightOverlap

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Parking

/-- The variance of the increment of the noise test functions at two
space-time points, read off the overlap kernel. -/
def noiseVarDiff (T : ℝ) (u u' : Fin 2 → ℝ) : ℝ :=
  contOverlap T u u + contOverlap T u' u' - 2 * contOverlap T u u'

/-- **The bridge to the actual `L²` increment of the test functions.** -/
theorem noiseVarDiff_eq (T s x s' x' : ℝ) :
    (∫ p : ℝ × ℝ, (contNoiseTest T s x p - contNoiseTest T s' x' p) ^ 2)
      = noiseVarDiff T ![s, x] ![s', x'] := by
  have hf : MemLp (contNoiseTest T s x) 2 (volume : Measure (ℝ × ℝ)) := memLp_contNoiseTest T s x
  have hg : MemLp (contNoiseTest T s' x') 2 (volume : Measure (ℝ × ℝ)) :=
    memLp_contNoiseTest T s' x'
  have hfsq : Integrable (fun p : ℝ × ℝ => (contNoiseTest T s x p) ^ 2) volume :=
    integrable_contNoiseTest_sq T s x
  have hgsq : Integrable (fun p : ℝ × ℝ => (contNoiseTest T s' x' p) ^ 2) volume :=
    integrable_contNoiseTest_sq T s' x'
  have hfg : Integrable (fun p : ℝ × ℝ => contNoiseTest T s x p * contNoiseTest T s' x' p)
      volume := hf.integrable_mul hg
  have hcross : Integrable (fun p : ℝ × ℝ =>
      2 * (contNoiseTest T s x p * contNoiseTest T s' x' p)) volume := hfg.const_mul 2
  have hleft : Integrable (fun p : ℝ × ℝ => (contNoiseTest T s x p) ^ 2
      - 2 * (contNoiseTest T s x p * contNoiseTest T s' x' p)) volume := hfsq.sub hcross
  have hexpand : (fun p : ℝ × ℝ => (contNoiseTest T s x p - contNoiseTest T s' x' p) ^ 2)
      = fun p => ((contNoiseTest T s x p) ^ 2
        - 2 * (contNoiseTest T s x p * contNoiseTest T s' x' p))
        + (contNoiseTest T s' x' p) ^ 2 := by
    funext p; ring
  have hd1 : (∫ p : ℝ × ℝ, (contNoiseTest T s x p) ^ 2) = contOverlap T ![s, x] ![s, x] := by
    rw [show (fun p : ℝ × ℝ => (contNoiseTest T s x p) ^ 2)
        = fun p => contNoiseTest T s x p * contNoiseTest T s x p from by funext p; ring]
    exact integral_contNoiseTest_mul_eq_contOverlap T s s x x
  have hd2 : (∫ p : ℝ × ℝ, (contNoiseTest T s' x' p) ^ 2) = contOverlap T ![s', x'] ![s', x'] := by
    rw [show (fun p : ℝ × ℝ => (contNoiseTest T s' x' p) ^ 2)
        = fun p => contNoiseTest T s' x' p * contNoiseTest T s' x' p from by funext p; ring]
    exact integral_contNoiseTest_mul_eq_contOverlap T s' s' x' x'
  rw [hexpand, integral_add hleft hgsq, integral_sub hfsq hcross, integral_const_mul,
    integral_contNoiseTest_mul_eq_contOverlap, hd1, hd2]
  unfold noiseVarDiff
  ring

theorem noiseVarDiff_nonneg (T : ℝ) (u u' : Fin 2 → ℝ) : 0 ≤ noiseVarDiff T u u' := by
  rw [show u = ![u 0, u 1] from List.ofFn_inj.mp rfl,
    show u' = ![u' 0, u' 1] from List.ofFn_inj.mp rfl, ← noiseVarDiff_eq]
  exact integral_nonneg fun p => sq_nonneg _

theorem noiseVarDiff_symm (T : ℝ) (u u' : Fin 2 → ℝ) :
    noiseVarDiff T u u' = noiseVarDiff T u' u := by
  unfold noiseVarDiff
  rw [contOverlap_symm T u u']
  ring

@[simp] theorem noiseVarDiff_self (T : ℝ) (u : Fin 2 → ℝ) : noiseVarDiff T u u = 0 := by
  unfold noiseVarDiff; ring

/-- **The triangle bound through an intermediate point**, from the pointwise
`AM`-`GM` inequality `(a + b) ^ 2 ≤ 2 a ^ 2 + 2 b ^ 2` applied to the two test
function differences. -/
theorem noiseVarDiff_le_two_mul_add (T : ℝ) (u h v : Fin 2 → ℝ) :
    noiseVarDiff T u v ≤ 2 * noiseVarDiff T u h + 2 * noiseVarDiff T h v := by
  rw [show u = ![u 0, u 1] from List.ofFn_inj.mp rfl,
    show h = ![h 0, h 1] from List.ofFn_inj.mp rfl,
    show v = ![v 0, v 1] from List.ofFn_inj.mp rfl,
    ← noiseVarDiff_eq, ← noiseVarDiff_eq, ← noiseVarDiff_eq]
  have hf : MemLp (contNoiseTest T (u 0) (u 1)) 2 (volume : Measure (ℝ × ℝ)) :=
    memLp_contNoiseTest T _ _
  have hg : MemLp (contNoiseTest T (h 0) (h 1)) 2 (volume : Measure (ℝ × ℝ)) :=
    memLp_contNoiseTest T _ _
  have hk : MemLp (contNoiseTest T (v 0) (v 1)) 2 (volume : Measure (ℝ × ℝ)) :=
    memLp_contNoiseTest T _ _
  have h1 : Integrable (fun p : ℝ × ℝ =>
      (contNoiseTest T (u 0) (u 1) p - contNoiseTest T (h 0) (h 1) p) ^ 2) volume :=
    (memLp_two_iff_integrable_sq (hf.sub hg).aestronglyMeasurable).mp (hf.sub hg)
  have h2 : Integrable (fun p : ℝ × ℝ =>
      (contNoiseTest T (h 0) (h 1) p - contNoiseTest T (v 0) (v 1) p) ^ 2) volume :=
    (memLp_two_iff_integrable_sq (hg.sub hk).aestronglyMeasurable).mp (hg.sub hk)
  have h3 : Integrable (fun p : ℝ × ℝ =>
      (contNoiseTest T (u 0) (u 1) p - contNoiseTest T (v 0) (v 1) p) ^ 2) volume :=
    (memLp_two_iff_integrable_sq (hf.sub hk).aestronglyMeasurable).mp (hf.sub hk)
  have h1' : Integrable (fun p : ℝ × ℝ =>
      2 * (contNoiseTest T (u 0) (u 1) p - contNoiseTest T (h 0) (h 1) p) ^ 2) volume :=
    h1.const_mul 2
  have h2' : Integrable (fun p : ℝ × ℝ =>
      2 * (contNoiseTest T (h 0) (h 1) p - contNoiseTest T (v 0) (v 1) p) ^ 2) volume :=
    h2.const_mul 2
  calc (∫ p : ℝ × ℝ, (contNoiseTest T (u 0) (u 1) p - contNoiseTest T (v 0) (v 1) p) ^ 2)
      ≤ ∫ p : ℝ × ℝ, (2 * (contNoiseTest T (u 0) (u 1) p - contNoiseTest T (h 0) (h 1) p) ^ 2
          + 2 * (contNoiseTest T (h 0) (h 1) p - contNoiseTest T (v 0) (v 1) p) ^ 2) := by
        refine integral_mono h3 (h1'.add h2') fun p => ?_
        nlinarith [sq_nonneg (contNoiseTest T (u 0) (u 1) p - 2 * contNoiseTest T (h 0) (h 1) p
          + contNoiseTest T (v 0) (v 1) p)]
    _ = 2 * (∫ p : ℝ × ℝ, (contNoiseTest T (u 0) (u 1) p - contNoiseTest T (h 0) (h 1) p) ^ 2)
        + 2 * (∫ p : ℝ × ℝ, (contNoiseTest T (h 0) (h 1) p - contNoiseTest T (v 0) (v 1) p) ^ 2) := by
        rw [integral_add h1' h2', integral_const_mul, integral_const_mul]

/-- `1 - e^{-u} ≤ min u 1` for `u ≥ 0`. -/
theorem one_sub_exp_neg_le_min_one (u : ℝ) : 1 - Real.exp (-u) ≤ min u 1 := by
  refine le_min ?_ ?_
  · linarith [Real.add_one_le_exp (-u)]
  · linarith [Real.exp_nonneg (-u)]

/-- `min u 1 ≤ √u` for `u ≥ 0`. -/
theorem min_one_le_sqrt {u : ℝ} (hu : 0 ≤ u) : min u 1 ≤ Real.sqrt u := by
  by_cases h : u ≤ 1
  · rw [min_eq_left h]
    nlinarith [Real.sq_sqrt hu, Real.sqrt_nonneg u]
  · rw [min_eq_right (not_le.mp h).le]
    calc (1 : ℝ) ≤ Real.sqrt 1 := by rw [Real.sqrt_one]
      _ ≤ Real.sqrt u := Real.sqrt_le_sqrt (not_le.mp h).le

/-- The pointwise bound on the heat kernel gap, in the `min` form. -/
theorem contHeat_zero_sub_le {t : ℝ} (ht : 0 < t) (d : ℝ) :
    contHeat t 0 0 - contHeat t 0 d
      ≤ Real.sqrt (2 / Real.pi) * (Real.sqrt t)⁻¹ * min (2 * d ^ 2 / t) 1 := by
  have hpref : (0 : ℝ) ≤ Real.sqrt (2 / Real.pi) * (Real.sqrt t)⁻¹ := by positivity
  have h0 : contHeat t 0 0 = Real.sqrt (2 / Real.pi) * (Real.sqrt t)⁻¹ := by
    rw [contHeat_zero_eq ht 0]
    norm_num
  have hd : contHeat t 0 d
      = Real.sqrt (2 / Real.pi) * (Real.sqrt t)⁻¹ * Real.exp (-(2 * d ^ 2 / t)) := by
    rw [contHeat_zero_eq ht d]
    congr 2
    ring
  have hkey := one_sub_exp_neg_le_min_one (2 * d ^ 2 / t)
  calc contHeat t 0 0 - contHeat t 0 d
      = Real.sqrt (2 / Real.pi) * (Real.sqrt t)⁻¹ * (1 - Real.exp (-(2 * d ^ 2 / t))) := by
        rw [h0, hd]; ring
    _ ≤ Real.sqrt (2 / Real.pi) * (Real.sqrt t)⁻¹ * min (2 * d ^ 2 / t) 1 :=
        mul_le_mul_of_nonneg_left hkey hpref

/-- `min u 1 ≤ u ^ θ` for `u ≥ 0` and `θ ∈ (0, 1]`. -/
theorem min_one_le_rpow {u : ℝ} (hu : 0 ≤ u) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    min u 1 ≤ u ^ θ := by
  by_cases h : u ≤ 1
  · rw [min_eq_left h]
    rcases hu.eq_or_lt with hu0 | hu0
    · simp [← hu0, Real.zero_rpow hθ0.ne']
    · calc u = u ^ (1 : ℝ) := (Real.rpow_one u).symm
        _ ≤ u ^ θ := Real.rpow_le_rpow_of_exponent_ge hu0 h hθ1
  · rw [min_eq_right (not_le.mp h).le]
    exact Real.one_le_rpow (not_le.mp h).le hθ0.le

/-- The pointwise heat-kernel-gap bound, in `rpow` form at exponent `θ = 1/4`,
directly in terms of a power of `t` alone. -/
theorem contHeat_zero_sub_le_rpow {t : ℝ} (ht : 0 < t) (d : ℝ) :
    contHeat t 0 0 - contHeat t 0 d
      ≤ Real.sqrt (2 / Real.pi) * (2 * d ^ 2) ^ ((1 : ℝ) / 4) * t ^ (-(3 : ℝ) / 4) := by
  have hpref : (0 : ℝ) ≤ Real.sqrt (2 / Real.pi) * (Real.sqrt t)⁻¹ := by positivity
  have h1 : contHeat t 0 0 - contHeat t 0 d
      ≤ Real.sqrt (2 / Real.pi) * (Real.sqrt t)⁻¹ * (2 * d ^ 2 / t) ^ ((1 : ℝ) / 4) :=
    le_trans (contHeat_zero_sub_le ht d)
      (mul_le_mul_of_nonneg_left
        (min_one_le_rpow (by positivity) (by norm_num) (by norm_num)) hpref)
  have heq : Real.sqrt (2 / Real.pi) * (Real.sqrt t)⁻¹ * (2 * d ^ 2 / t) ^ ((1 : ℝ) / 4)
      = Real.sqrt (2 / Real.pi) * (2 * d ^ 2) ^ ((1 : ℝ) / 4) * t ^ (-(3 : ℝ) / 4) := by
    rw [Real.div_rpow (by positivity) ht.le,
      show Real.sqrt t = t ^ ((1 : ℝ) / 2) from Real.sqrt_eq_rpow t,
      show (-(3 : ℝ) / 4) = -((1 : ℝ) / 2 + (1 : ℝ) / 4) by ring,
      Real.rpow_neg ht.le, Real.rpow_add ht, mul_inv]
    ring
  rwa [heq] at h1

/-- **The space-direction Hölder bound**: the time-integral of the heat
kernel gap between the origin and a displacement `d`, over a window of
length `τ`, is bounded by an explicit multiple of `τ ^ (1/4) * |d| ^ (1/2)`. -/
theorem contHeatTimeIntegral_zero_sub_le {τ : ℝ} (hτ : 0 < τ) (d : ℝ) :
    contHeatTimeIntegral τ 0 - contHeatTimeIntegral τ d
      ≤ 4 * Real.sqrt (2 / Real.pi) * (2 * d ^ 2) ^ ((1 : ℝ) / 4) * τ ^ ((1 : ℝ) / 4) := by
  have hLint : IntervalIntegrable (fun ψ : ℝ => contHeat ψ 0 0) volume 0 τ :=
    intervalIntegrable_contHeat_zero 0 τ 0
  have hRint : IntervalIntegrable (fun ψ : ℝ => contHeat ψ 0 d) volume 0 τ :=
    intervalIntegrable_contHeat_zero 0 τ d
  have hGint : IntervalIntegrable
      (fun ψ : ℝ => Real.sqrt (2 / Real.pi) * (2 * d ^ 2) ^ ((1 : ℝ) / 4) * ψ ^ (-(3 : ℝ) / 4))
      volume 0 τ :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  have hmono : (∫ ψ in (0 : ℝ)..τ, (contHeat ψ 0 0 - contHeat ψ 0 d))
      ≤ ∫ ψ in (0 : ℝ)..τ,
        Real.sqrt (2 / Real.pi) * (2 * d ^ 2) ^ ((1 : ℝ) / 4) * ψ ^ (-(3 : ℝ) / 4) := by
    refine intervalIntegral.integral_mono_on hτ.le (hLint.sub hRint) hGint fun ψ hψ => ?_
    rcases hψ.1.eq_or_lt with hψ0 | hψ0
    · simp [← hψ0, contHeat_of_nonpos le_rfl]
    · exact contHeat_zero_sub_le_rpow hψ0 d
  rw [intervalIntegral.integral_sub hLint hRint] at hmono
  rw [contHeatTimeIntegral_eq hτ.le, contHeatTimeIntegral_eq hτ.le]
  refine le_trans hmono (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(3 : ℝ) / 4)),
    show (-(3 : ℝ) / 4 + 1) = (1 : ℝ) / 4 by norm_num,
    Real.zero_rpow (by norm_num : ((1 : ℝ) / 4) ≠ 0)]
  ring

/-- **The diagonal of the overlap kernel** in terms of the time primitive. -/
theorem contOverlap_diag_eq (T s x : ℝ) :
    contOverlap T ![s, x] ![s, x] = contHeatTimeIntegral (2 * (T - s)) 0 / 2 := by
  rcases le_or_gt s T with hs | hs
  · have h := contOverlap_eq_timeIntegral (T := T) (s := s) (s' := s) hs hs x x
    have e1 : (2 : ℝ) * T - s - s = 2 * (T - s) := by ring
    have e2 : (x : ℝ) - x = 0 := by ring
    have e3 : |s - s| = (0 : ℝ) := by simp
    rw [h, e1, e2, e3, contHeatTimeIntegral_nonpos (le_refl (0 : ℝ)) 0]
    ring
  · have h1 : contOverlap T ![s, x] ![s, x] = 0 :=
      contOverlap_of_le (by simp [max_self, hs.le])
    have h2 : contHeatTimeIntegral (2 * (T - s)) 0 = 0 :=
      contHeatTimeIntegral_nonpos (by linarith) 0
    rw [h1, h2]; ring

/-- **The time primitive at zero displacement, in closed form.** -/
theorem contHeatTimeIntegral_zero_eq {τ : ℝ} (hτ : 0 ≤ τ) :
    contHeatTimeIntegral τ 0 = 2 * Real.sqrt (2 / Real.pi) * Real.sqrt τ := by
  have ht : (0 : ℝ) ≤ τ / 2 := by linarith
  have hkey : contHeatTimeIntegral τ 0 / 2 = 2 * Real.sqrt (τ / 2) / Real.sqrt Real.pi := by
    have h1 := contOverlap_eq_timeIntegral (T := τ / 2) (s := 0) (s' := 0) ht ht 0 0
    have h2 := integral_contNoiseTest_mul_eq_contOverlap (τ / 2) 0 0 0 0
    have h3 : (∫ p : ℝ × ℝ, contNoiseTest (τ / 2) 0 0 p * contNoiseTest (τ / 2) 0 0 p)
        = ∫ p : ℝ × ℝ, (contNoiseTest (τ / 2) 0 0 p) ^ 2 := by
      congr 1; funext p; ring
    have h4 := integral_contNoiseTest_sq (s := (0 : ℝ)) (T := τ / 2) ht 0
    rw [← h2, h3, h4] at h1
    have harg1 : contHeatTimeIntegral (2 * (τ / 2) - 0 - 0) ((0 : ℝ) - 0)
        = contHeatTimeIntegral τ 0 := by congr 1 <;> ring
    have harg2 : contHeatTimeIntegral (|(0 : ℝ) - 0|) ((0 : ℝ) - 0) = 0 := by
      have hzero : |(0 : ℝ) - 0| = (0 : ℝ) := by norm_num
      have hzero' : (0 : ℝ) - 0 = 0 := by ring
      rw [hzero, hzero']
      exact contHeatTimeIntegral_nonpos (le_refl (0 : ℝ)) 0
    have harg3 : τ / 2 - (0 : ℝ) = τ / 2 := by ring
    rw [harg1, harg2, harg3, sub_zero] at h1
    linarith [h1]
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2ne : Real.sqrt 2 ≠ 0 := by positivity
  have hpine : Real.sqrt Real.pi ≠ 0 := by positivity
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2) Real.pi]
  rw [Real.sqrt_div hτ 2] at hkey
  field_simp at hkey ⊢
  refine mul_right_cancel₀ h2ne ?_
  linear_combination hkey - 2 * Real.sqrt τ * h22

/-- `√a + √b ≤ √2 · √(a+b)` for `a, b ≥ 0` (Cauchy-Schwarz / QM-AM). -/
theorem sqrt_add_sqrt_le_sqrt_two_mul_sqrt_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a + Real.sqrt b ≤ Real.sqrt 2 * Real.sqrt (a + b) := by
  have hab : 2 * Real.sqrt a * Real.sqrt b ≤ a + b := by
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb]
  have h1 : (Real.sqrt a + Real.sqrt b) ^ 2 ≤ 2 * (a + b) := by
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, hab]
  have h2 : Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) ≤ Real.sqrt (2 * (a + b)) :=
    Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_mul (by norm_num)] at h2

/-- **The time-direction Hölder bound**: the variance of the increment of the
noise test functions at two space-time points sharing the same spatial
coordinate is bounded by an explicit multiple of `√|s - s'|`. -/
theorem noiseVarDiff_time_le {T s s' x : ℝ} (hs : s ≤ T) (hs' : s' ≤ T) :
    noiseVarDiff T ![s, x] ![s', x] ≤ 2 * Real.sqrt (2 / Real.pi) * Real.sqrt |s - s'| := by
  have ha : (0 : ℝ) ≤ 2 * (T - s) := by linarith
  have hb : (0 : ℝ) ≤ 2 * (T - s') := by linarith
  have hab : (0 : ℝ) ≤ 2 * T - s - s' := by linarith
  have hδ : (0 : ℝ) ≤ |s - s'| := abs_nonneg _
  have hov := contOverlap_eq_timeIntegral hs hs' x x
  have hd1 := contOverlap_diag_eq T s x
  have hd2 := contOverlap_diag_eq T s' x
  have he1 : contHeatTimeIntegral (2 * (T - s)) 0
      = 2 * Real.sqrt (2 / Real.pi) * Real.sqrt (2 * (T - s)) := contHeatTimeIntegral_zero_eq ha
  have he2 : contHeatTimeIntegral (2 * (T - s')) 0
      = 2 * Real.sqrt (2 / Real.pi) * Real.sqrt (2 * (T - s')) := contHeatTimeIntegral_zero_eq hb
  have he3 : contHeatTimeIntegral (2 * T - s - s') ((x : ℝ) - x)
      = 2 * Real.sqrt (2 / Real.pi) * Real.sqrt (2 * T - s - s') := by
    rw [show (x : ℝ) - x = 0 from by ring]; exact contHeatTimeIntegral_zero_eq hab
  have he4 : contHeatTimeIntegral (|s - s'|) ((x : ℝ) - x)
      = 2 * Real.sqrt (2 / Real.pi) * Real.sqrt |s - s'| := by
    rw [show (x : ℝ) - x = 0 from by ring]; exact contHeatTimeIntegral_zero_eq hδ
  have hamqm : Real.sqrt (2 * (T - s)) + Real.sqrt (2 * (T - s'))
      ≤ Real.sqrt 2 * Real.sqrt (2 * (2 * T - s - s')) := by
    have h := sqrt_add_sqrt_le_sqrt_two_mul_sqrt_add ha hb
    rwa [show 2 * (T - s) + 2 * (T - s') = 2 * (2 * T - s - s') from by ring] at h
  have hsimp : Real.sqrt 2 * Real.sqrt (2 * (2 * T - s - s')) = 2 * Real.sqrt (2 * T - s - s') := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← mul_assoc,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hsimp] at hamqm
  have hK : (0 : ℝ) ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  have hfinal := mul_le_mul_of_nonneg_left hamqm hK
  unfold noiseVarDiff
  rw [hd1, hd2, hov, he1, he2, he3, he4]
  nlinarith [hfinal]

/-- **The space-direction Hölder bound**, at the level of `noiseVarDiff`. -/
theorem noiseVarDiff_space_le {T s x x' : ℝ} (hs : s ≤ T) :
    noiseVarDiff T ![s, x] ![s, x']
      ≤ 4 * Real.sqrt (2 / Real.pi) * (2 * (x - x') ^ 2) ^ ((1 : ℝ) / 4)
        * (2 * (T - s)) ^ ((1 : ℝ) / 4) := by
  have hRHSnonneg : (0 : ℝ) ≤ 4 * Real.sqrt (2 / Real.pi) * (2 * (x - x') ^ 2) ^ ((1 : ℝ) / 4)
      * (2 * (T - s)) ^ ((1 : ℝ) / 4) := by positivity
  rcases hs.eq_or_lt with heq | hlt
  · have hτ0 : (2 : ℝ) * (T - s) = 0 := by rw [heq]; ring
    have hd : contOverlap T ![s, x] ![s, x] = 0 := by
      rw [contOverlap_diag_eq, hτ0, contHeatTimeIntegral_nonpos (le_refl (0 : ℝ))]; ring
    have hd' : contOverlap T ![s, x'] ![s, x'] = 0 := by
      rw [contOverlap_diag_eq, hτ0, contHeatTimeIntegral_nonpos (le_refl (0 : ℝ))]; ring
    have hov : contOverlap T ![s, x] ![s, x'] = 0 := by
      have h := contOverlap_eq_timeIntegral hs hs x x'
      have harg : (2 : ℝ) * T - s - s = 0 := by rw [← hτ0]; ring
      have habs : |s - s| = (0 : ℝ) := by simp
      rw [harg, habs, contHeatTimeIntegral_nonpos (le_refl (0 : ℝ))] at h
      linarith [h]
    unfold noiseVarDiff
    rw [hd, hd', hov]
    linarith [hRHSnonneg]
  · have hτ : (0 : ℝ) < 2 * (T - s) := by linarith
    have hb := contHeatTimeIntegral_zero_sub_le hτ (x - x')
    have hov := contOverlap_eq_timeIntegral hs hs x x'
    have hd := contOverlap_diag_eq T s x
    have hd' := contOverlap_diag_eq T s x'
    have harg : (2 : ℝ) * T - s - s = 2 * (T - s) := by ring
    have habs : |s - s| = (0 : ℝ) := by simp
    rw [harg, habs, contHeatTimeIntegral_nonpos (le_refl (0 : ℝ))] at hov
    unfold noiseVarDiff
    rw [hd, hd', hov]
    linarith [hb]

/-- **The combined Hölder bound on a bounded box**: at two points of `[0,T] × [-2A,2A]`,
`noiseVarDiff` is bounded by an explicit multiple of `√(|s1-s2|+|x1-x2|)` — a SINGLE
exponent (`1/2`), valid at every scale within the box (not just near the diagonal),
obtained by combining the time slice (sharp exponent `1/2`) and the space slice (weakened
from its sharp exponent `1` to `1/2` using the box's finite time-extent `T`) through the
intermediate point `(s2, x1)`. -/
theorem noiseVarDiff_of_mem_le {T : ℝ}
    {s1 x1 s2 x2 : ℝ} (hs1 : s1 ∈ Set.Icc (0 : ℝ) T) (hs2 : s2 ∈ Set.Icc (0 : ℝ) T) :
    noiseVarDiff T ![s1, x1] ![s2, x2]
      ≤ (4 * Real.sqrt (2 / Real.pi)
          + 8 * Real.sqrt (2 / Real.pi) * (2 : ℝ) ^ ((1 : ℝ) / 4) * (2 * T) ^ ((1 : ℝ) / 4))
        * Real.sqrt (|s1 - s2| + |x1 - x2|) := by
  set ρ : ℝ := |s1 - s2| + |x1 - x2| with hρdef
  have hρ0 : (0 : ℝ) ≤ ρ := by positivity
  have h1 : |s1 - s2| ≤ ρ := by rw [hρdef]; linarith [abs_nonneg (x1 - x2)]
  have h2 : |x1 - x2| ≤ ρ := by rw [hρdef]; linarith [abs_nonneg (s1 - s2)]
  have hsqrt1 : Real.sqrt |s1 - s2| ≤ Real.sqrt ρ := Real.sqrt_le_sqrt h1
  have hsqrt2 : |x1 - x2| ^ ((1 : ℝ) / 2) ≤ Real.sqrt ρ := by
    rw [Real.sqrt_eq_rpow]
    gcongr
  have hK : (0 : ℝ) ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  have hTs2nonneg : (0 : ℝ) ≤ 2 * (T - s2) := by linarith [hs2.2]
  have h2Tnonneg : (0 : ℝ) ≤ 2 * T := by linarith [hs1.1, hs1.2]
  have hrpow_mono : (2 * (T - s2)) ^ ((1 : ℝ) / 4) ≤ (2 * T) ^ ((1 : ℝ) / 4) := by
    gcongr
    linarith [hs2.1]
  have hxsq : (2 * (x1 - x2) ^ 2) ^ ((1 : ℝ) / 4)
      = (2 : ℝ) ^ ((1 : ℝ) / 4) * |x1 - x2| ^ ((1 : ℝ) / 2) := by
    rw [Real.mul_rpow (by norm_num) (sq_nonneg _)]
    congr 1
    rw [← sq_abs (x1 - x2), ← Real.rpow_natCast |x1 - x2| 2, ← Real.rpow_mul (abs_nonneg _)]
    norm_num
  have htime := noiseVarDiff_time_le (T := T) (s := s1) (s' := s2) (x := x1) hs1.2 hs2.2
  have hspace := noiseVarDiff_space_le (T := T) (s := s2) (x := x1) (x' := x2) hs2.2
  have htri := noiseVarDiff_le_two_mul_add T ![s1, x1] ![s2, x1] ![s2, x2]
  have hxpow_nonneg : (0 : ℝ) ≤ |x1 - x2| ^ ((1 : ℝ) / 2) := by positivity
  have hspace' : noiseVarDiff T ![s2, x1] ![s2, x2]
      ≤ 4 * Real.sqrt (2 / Real.pi) * (2 : ℝ) ^ ((1 : ℝ) / 4) * (2 * T) ^ ((1 : ℝ) / 4)
        * Real.sqrt ρ := by
    calc noiseVarDiff T ![s2, x1] ![s2, x2]
        ≤ 4 * Real.sqrt (2 / Real.pi) * (2 * (x1 - x2) ^ 2) ^ ((1 : ℝ) / 4)
            * (2 * (T - s2)) ^ ((1 : ℝ) / 4) := hspace
      _ = 4 * Real.sqrt (2 / Real.pi) * ((2 : ℝ) ^ ((1 : ℝ) / 4) * |x1 - x2| ^ ((1 : ℝ) / 2))
            * (2 * (T - s2)) ^ ((1 : ℝ) / 4) := by rw [hxsq]
      _ ≤ 4 * Real.sqrt (2 / Real.pi) * ((2 : ℝ) ^ ((1 : ℝ) / 4) * |x1 - x2| ^ ((1 : ℝ) / 2))
            * (2 * T) ^ ((1 : ℝ) / 4) := by
          gcongr
      _ = 4 * Real.sqrt (2 / Real.pi) * (2 : ℝ) ^ ((1 : ℝ) / 4) * (2 * T) ^ ((1 : ℝ) / 4)
            * |x1 - x2| ^ ((1 : ℝ) / 2) := by ring
      _ ≤ 4 * Real.sqrt (2 / Real.pi) * (2 : ℝ) ^ ((1 : ℝ) / 4) * (2 * T) ^ ((1 : ℝ) / 4)
            * Real.sqrt ρ := by
          gcongr
  calc noiseVarDiff T ![s1, x1] ![s2, x2]
      ≤ 2 * noiseVarDiff T ![s1, x1] ![s2, x1] + 2 * noiseVarDiff T ![s2, x1] ![s2, x2] := htri
    _ ≤ 2 * (2 * Real.sqrt (2 / Real.pi) * Real.sqrt |s1 - s2|)
        + 2 * (4 * Real.sqrt (2 / Real.pi) * (2 : ℝ) ^ ((1 : ℝ) / 4) * (2 * T) ^ ((1 : ℝ) / 4)
          * Real.sqrt ρ) := by
        gcongr
    _ ≤ 2 * (2 * Real.sqrt (2 / Real.pi) * Real.sqrt ρ)
        + 2 * (4 * Real.sqrt (2 / Real.pi) * (2 : ℝ) ^ ((1 : ℝ) / 4) * (2 * T) ^ ((1 : ℝ) / 4)
          * Real.sqrt ρ) := by
        gcongr
    _ = (4 * Real.sqrt (2 / Real.pi)
          + 8 * Real.sqrt (2 / Real.pi) * (2 : ℝ) ^ ((1 : ℝ) / 4) * (2 * T) ^ ((1 : ℝ) / 4))
        * Real.sqrt ρ := by ring

/-- **The global Hölder bound after clamping to the box**: for ALL reals `s, x, s', x'`
(not merely those already in the box), `noiseVarDiff` at the box-clamped points is
bounded by the SAME explicit multiple of `√(|s-s'|+|x-x'|)`, since `Set.projIcc` is
`1`-Lipschitz. This is the bound that closes the module docstring's route: it is a
single-exponent (`q = 1/2`) bound valid at EVERY scale of `s, x, s', x' ∈ ℝ`, which the
plain (unclamped) field could never satisfy (see the two slice bounds above). -/
theorem noiseVarDiff_projIcc_le {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (s x s' x' : ℝ) :
    noiseVarDiff T
      ![(Set.projIcc (0 : ℝ) T hT s : ℝ), (Set.projIcc (-(2 * A)) (2 * A) (by linarith) x : ℝ)]
      ![(Set.projIcc (0 : ℝ) T hT s' : ℝ), (Set.projIcc (-(2 * A)) (2 * A) (by linarith) x' : ℝ)]
      ≤ (4 * Real.sqrt (2 / Real.pi)
          + 8 * Real.sqrt (2 / Real.pi) * (2 : ℝ) ^ ((1 : ℝ) / 4) * (2 * T) ^ ((1 : ℝ) / 4))
        * Real.sqrt (|s - s'| + |x - x'|) := by
  have hA2 : -(2 * A) ≤ 2 * A := by linarith
  have hs1 : (Set.projIcc (0 : ℝ) T hT s : ℝ) ∈ Set.Icc (0 : ℝ) T := (Set.projIcc (0 : ℝ) T hT s).2
  have hs2 : (Set.projIcc (0 : ℝ) T hT s' : ℝ) ∈ Set.Icc (0 : ℝ) T :=
    (Set.projIcc (0 : ℝ) T hT s').2
  have hbase := noiseVarDiff_of_mem_le
    (x1 := (Set.projIcc (-(2 * A)) (2 * A) hA2 x : ℝ))
    (x2 := (Set.projIcc (-(2 * A)) (2 * A) hA2 x' : ℝ)) hs1 hs2
  have hd1 : |(Set.projIcc (0 : ℝ) T hT s : ℝ) - (Set.projIcc (0 : ℝ) T hT s' : ℝ)| ≤ |s - s'| :=
    Set.abs_projIcc_sub_projIcc hT
  have hd2 : |(Set.projIcc (-(2 * A)) (2 * A) hA2 x : ℝ)
      - (Set.projIcc (-(2 * A)) (2 * A) hA2 x' : ℝ)| ≤ |x - x'| :=
    Set.abs_projIcc_sub_projIcc hA2
  have hmono : Real.sqrt (|(Set.projIcc (0 : ℝ) T hT s : ℝ) - (Set.projIcc (0 : ℝ) T hT s' : ℝ)|
      + |(Set.projIcc (-(2 * A)) (2 * A) hA2 x : ℝ)
          - (Set.projIcc (-(2 * A)) (2 * A) hA2 x' : ℝ)|)
      ≤ Real.sqrt (|s - s'| + |x - x'|) := by
    apply Real.sqrt_le_sqrt
    linarith [hd1, hd2]
  have hKpos : (0 : ℝ) ≤ 4 * Real.sqrt (2 / Real.pi)
      + 8 * Real.sqrt (2 / Real.pi) * (2 : ℝ) ^ ((1 : ℝ) / 4) * (2 * T) ^ ((1 : ℝ) / 4) := by
    positivity
  exact le_trans hbase (mul_le_mul_of_nonneg_left hmono hKpos)

end Parking

end
