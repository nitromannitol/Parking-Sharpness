/-
**The dimension-split asymptotic `R^{d-4}·spatialStepRate(d,n0+1)² → 0`**, `1 ≤ d ≤ 3`.

`Parking.spatialStepRate d n` does NOT vanish as `n → ∞` (`√(2n+3)` at `d=1`,
`√(1+8log(n+2))` at `d=2`, the constant `√(1+2d·2^{d-1})` at `d=3`), so the grid-gap estimate of
`prop:spatial-scaling`'s Step 1 needs this explicit three-way asymptotic, not a single uniform
bound: the `R^{d/2-2}` rescaling's square `R^{d-4}` decays fast enough to dominate
`spatialStepRate`'s growth in every one of the three dimensions.
-/
import Parking.Support.SpatGreenShiftLowDim

open Filter Topology

noncomputable section

namespace Parking

variable {d : ℕ}

/-! ### An elementary logarithm bound -/

/-- **`log t ≤ 2√t` for `t > 0`.**  From `log(√t) ≤ √t - 1` and `log(√t) = (log t)/2`. -/
theorem log_le_two_mul_sqrt {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * Real.sqrt t := by
  have h1 : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr ht)
  have h2 : Real.log (Real.sqrt t) = Real.log t / 2 := Real.log_sqrt ht.le
  rw [h2] at h1
  nlinarith [Real.sqrt_nonneg t]

/-! ### The floor bound feeding every case -/

/-- **`⌊sR²⌋₊ + 1 ≤ sR² + 1`, dropping the floor.** -/
theorem natFloor_sq_add_one_le {s : ℝ} (hs : 0 < s) (R : ℝ) :
    ((⌊s * R ^ 2⌋₊ : ℕ) : ℝ) + 1 ≤ s * R ^ 2 + 1 := by
  have h : ((⌊s * R ^ 2⌋₊ : ℕ) : ℝ) ≤ s * R ^ 2 := Nat.floor_le (by positivity)
  linarith

/-! ### The three cases -/

/-- **`d = 1`: `R^{-3}·(2(⌊sR²⌋₊+1)+3) → 0`.** -/
theorem tendsto_rpow_sub_four_mul_stepRate_sq_one {s : ℝ} (hs : 0 < s) :
    Tendsto (fun R : ℝ =>
        R ^ ((1 : ℝ) - 4) * (spatialStepRate 1 (⌊s * R ^ 2⌋₊ + 1)) ^ 2) atTop (𝓝 0) := by
  have hbound : ∀ᶠ R : ℝ in atTop, 0 < R ∧
      R ^ ((1 : ℝ) - 4) * (spatialStepRate 1 (⌊s * R ^ 2⌋₊ + 1)) ^ 2
        ≤ (2 * s) * R ^ (-(1 : ℝ)) + 5 * R ^ (-(3 : ℝ)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
    refine ⟨hR, ?_⟩
    have hif : spatialStepRate 1 (⌊s * R ^ 2⌋₊ + 1)
        = Real.sqrt (2 * (((⌊s * R ^ 2⌋₊ : ℕ) : ℝ) + 1) + 3) := by
      unfold spatialStepRate; norm_num
    have hrate : (spatialStepRate 1 (⌊s * R ^ 2⌋₊ + 1)) ^ 2
        = 2 * (((⌊s * R ^ 2⌋₊ : ℕ) : ℝ) + 1) + 3 := by
      rw [hif, Real.sq_sqrt (by positivity)]
    rw [hrate]
    have hpoly : 2 * (((⌊s * R ^ 2⌋₊ : ℕ) : ℝ) + 1) + 3 ≤ 2 * s * R ^ 2 + 5 := by
      have := natFloor_sq_add_one_le hs R
      linarith
    have hR2 : R ^ (2:ℝ) = R ^ 2 := by rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    have hstep1 : R ^ ((1:ℝ) - 4) * (2 * (((⌊s * R ^ 2⌋₊ : ℕ) : ℝ) + 1) + 3)
        ≤ R ^ ((1:ℝ) - 4) * (2 * s * R ^ 2 + 5) :=
      mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg hR.le _)
    refine hstep1.trans ?_
    have hexpand : R ^ ((1:ℝ) - 4) * (2 * s * R ^ 2 + 5)
        = (2 * s) * (R ^ ((1:ℝ) - 4) * R ^ (2:ℝ)) + 5 * R ^ ((1:ℝ) - 4) := by
      rw [hR2]; ring
    rw [hexpand]
    have hcomb : R ^ ((1:ℝ) - 4) * R ^ (2:ℝ) = R ^ (-(1:ℝ)) := by
      rw [← Real.rpow_add hR]; norm_num
    have hexp3 : R ^ ((1:ℝ) - 4) = R ^ (-(3:ℝ)) := by norm_num
    rw [hcomb, hexp3]
  have hz1 : Tendsto (fun R : ℝ => (2 * s) * R ^ (-(1 : ℝ))) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (y := (1:ℝ)) (by norm_num)
    simpa using this.const_mul (2 * s)
  have hz2 : Tendsto (fun R : ℝ => 5 * R ^ (-(3 : ℝ))) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (y := (3:ℝ)) (by norm_num)
    simpa using this.const_mul 5
  have hz : Tendsto (fun R : ℝ => (2 * s) * R ^ (-(1 : ℝ)) + 5 * R ^ (-(3 : ℝ))) atTop (𝓝 0) := by
    simpa using hz1.add hz2
  refine squeeze_zero' ?_ ?_ hz
  · filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with R hR; positivity
  · filter_upwards [hbound] with R hR using hR.2

/-- **`d = 2`: `R^{-2}·(1+8log(⌊sR²⌋₊+1+2)) → 0`.** -/
theorem tendsto_rpow_sub_four_mul_stepRate_sq_two {s : ℝ} (hs : 0 < s) :
    Tendsto (fun R : ℝ =>
        R ^ ((2 : ℝ) - 4) * (spatialStepRate 2 (⌊s * R ^ 2⌋₊ + 1)) ^ 2) atTop (𝓝 0) := by
  have hbound : ∀ᶠ R : ℝ in atTop, 0 < R ∧
      R ^ ((2 : ℝ) - 4) * (spatialStepRate 2 (⌊s * R ^ 2⌋₊ + 1)) ^ 2
        ≤ R ^ (-(2 : ℝ)) + 16 * Real.sqrt (s * R ^ 2 + 3) * R ^ (-(2 : ℝ)) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
    refine ⟨hR, ?_⟩
    have hif : spatialStepRate 2 (⌊s * R ^ 2⌋₊ + 1)
        = Real.sqrt (1 + 8 * Real.log (((⌊s * R ^ 2⌋₊ : ℕ) : ℝ) + 1 + 2)) := by
      unfold spatialStepRate; norm_num
    have hnn : (0:ℝ) ≤ 1 + 8 * Real.log (((⌊s * R ^ 2⌋₊ : ℕ) : ℝ) + 1 + 2) := by
      have h1 : (1:ℝ) ≤ ((⌊s * R ^ 2⌋₊ : ℕ) : ℝ) + 1 + 2 := by
        have := (Nat.cast_nonneg (⌊s * R ^ 2⌋₊ : ℕ) : (0:ℝ) ≤ ((⌊s * R ^ 2⌋₊ : ℕ) : ℝ))
        linarith
      have h2 : (0:ℝ) ≤ Real.log (((⌊s * R ^ 2⌋₊ : ℕ) : ℝ) + 1 + 2) := Real.log_nonneg h1
      linarith
    have hrate : (spatialStepRate 2 (⌊s * R ^ 2⌋₊ + 1)) ^ 2
        = 1 + 8 * Real.log (((⌊s * R ^ 2⌋₊ : ℕ) : ℝ) + 1 + 2) := by
      rw [hif, Real.sq_sqrt hnn]
    rw [hrate]
    have htpos : (0:ℝ) < ((⌊s * R ^ 2⌋₊ : ℕ) : ℝ) + 1 + 2 := by positivity
    have hlogb : Real.log (((⌊s * R ^ 2⌋₊ : ℕ) : ℝ) + 1 + 2)
        ≤ 2 * Real.sqrt (s * R ^ 2 + 3) := by
      have hle : ((⌊s * R ^ 2⌋₊ : ℕ) : ℝ) + 1 + 2 ≤ s * R ^ 2 + 3 := by
        have := natFloor_sq_add_one_le hs R; linarith
      have h1 := log_le_two_mul_sqrt htpos
      have h2 : Real.log (((⌊s * R ^ 2⌋₊ : ℕ) : ℝ) + 1 + 2) ≤ Real.log (s * R ^ 2 + 3) :=
        Real.log_le_log htpos hle
      exact h2.trans (by
        have h3 : Real.sqrt (s * R ^ 2 + 3) ≥ 0 := Real.sqrt_nonneg _
        nlinarith [log_le_two_mul_sqrt (show (0:ℝ) < s * R^2 + 3 by positivity)])
    have hstep : (1 + 8 * Real.log (((⌊s * R ^ 2⌋₊ : ℕ) : ℝ) + 1 + 2))
        ≤ 1 + 16 * Real.sqrt (s * R ^ 2 + 3) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hR.le ((2:ℝ) - 4))
    refine hmul.trans ?_
    have hexpand : R ^ ((2:ℝ) - 4) * (1 + 16 * Real.sqrt (s * R ^ 2 + 3))
        = R ^ (-(2:ℝ)) + 16 * Real.sqrt (s * R ^ 2 + 3) * R ^ (-(2:ℝ)) := by
      have hexp2 : R ^ ((2:ℝ) - 4) = R ^ (-(2:ℝ)) := by norm_num
      rw [hexp2]; ring
    rw [hexpand]
  have hz1 : Tendsto (fun R : ℝ => R ^ (-(2 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (y := (2:ℝ)) (by norm_num)
  have hz2 : Tendsto (fun R : ℝ => 16 * Real.sqrt (s * R ^ 2 + 3) * R ^ (-(2 : ℝ))) atTop (𝓝 0) := by
    -- `√(sR²+3) / R² → 0`: bound `√(sR²+3) ≤ √s·R + 2` for `R` large, then combine.
    have hbound2 : ∀ᶠ R : ℝ in atTop, Real.sqrt (s * R ^ 2 + 3) ≤ Real.sqrt s * R + 2 := by
      filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with R hR1
      have hR0 : (0:ℝ) ≤ R := by linarith
      have hrhs0 : (0:ℝ) ≤ Real.sqrt s * R + 2 := by positivity
      rw [show s * R ^ 2 + 3 = (Real.sqrt s * R) ^ 2 + 3 by
        rw [mul_pow, Real.sq_sqrt hs.le]]
      have hsq2 : ((Real.sqrt s * R) ^ 2 + 3 : ℝ) ≤ (Real.sqrt s * R + 2) ^ 2 := by
        nlinarith [mul_nonneg (Real.sqrt_nonneg s) hR0]
      calc Real.sqrt ((Real.sqrt s * R) ^ 2 + 3) ≤ Real.sqrt ((Real.sqrt s * R + 2) ^ 2) :=
            Real.sqrt_le_sqrt hsq2
        _ = Real.sqrt s * R + 2 := Real.sqrt_sq hrhs0
    have hz2' : Tendsto (fun R : ℝ => 16 * (Real.sqrt s * R + 2) * R ^ (-(2:ℝ))) atTop (𝓝 0) := by
      have heq : ∀ᶠ R : ℝ in atTop, 16 * (Real.sqrt s * R + 2) * R ^ (-(2:ℝ))
          = 16 * Real.sqrt s * (R * R ^ (-(2:ℝ))) + 32 * R ^ (-(2:ℝ)) := by
        filter_upwards [] with R; ring
      have hRexp : Tendsto (fun R : ℝ => R * R ^ (-(2:ℝ))) atTop (𝓝 0) := by
        have heq2 : ∀ᶠ R : ℝ in atTop, R * R ^ (-(2:ℝ)) = R ^ (-(1:ℝ)) := by
          filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with R hR
          have e1 : R ^ (-(1:ℝ)) = R ^ (1:ℝ) * R ^ (-(2:ℝ)) := by
            rw [← Real.rpow_add hR]; congr 1; norm_num
          rw [e1, Real.rpow_one]
        exact (tendsto_rpow_neg_atTop (y := (1:ℝ)) (by norm_num)).congr'
          (heq2.mono fun R hR => hR.symm)
      have hsum : Tendsto (fun R : ℝ => 16 * Real.sqrt s * (R * R ^ (-(2:ℝ))) + 32 * R ^ (-(2:ℝ)))
          atTop (𝓝 0) := by
        simpa using (hRexp.const_mul (16 * Real.sqrt s)).add (hz1.const_mul 32)
      exact hsum.congr' (heq.mono fun R hR => hR.symm)
    have hnonneg : ∀ᶠ R : ℝ in atTop, (0:ℝ) ≤ 16 * Real.sqrt (s * R ^ 2 + 3) * R ^ (-(2:ℝ)) := by
      filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with R hR
      positivity
    have hub : ∀ᶠ R : ℝ in atTop,
        16 * Real.sqrt (s * R ^ 2 + 3) * R ^ (-(2:ℝ))
          ≤ 16 * (Real.sqrt s * R + 2) * R ^ (-(2:ℝ)) := by
      filter_upwards [hbound2, Filter.eventually_gt_atTop (0:ℝ)] with R hb hR
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hR.le _)
    exact squeeze_zero' hnonneg hub hz2'
  have hz : Tendsto (fun R : ℝ => R ^ (-(2 : ℝ)) + 16 * Real.sqrt (s * R ^ 2 + 3) * R ^ (-(2 : ℝ)))
      atTop (𝓝 0) := by simpa using hz1.add hz2
  refine squeeze_zero' ?_ ?_ hz
  · filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with R hR; positivity
  · filter_upwards [hbound] with R hR using hR.2

/-- **`d = 3`: `R^{-1}·25 → 0`.**  `spatialStepRate 3` does not depend on `n`, hence not on `s`
or `R` either. -/
theorem tendsto_rpow_sub_four_mul_stepRate_sq_three {s : ℝ} :
    Tendsto (fun R : ℝ =>
        R ^ ((3 : ℝ) - 4) * (spatialStepRate 3 (⌊s * R ^ 2⌋₊ + 1)) ^ 2) atTop (𝓝 0) := by
  have hrate : ∀ n : ℕ, (spatialStepRate 3 n) ^ 2 = 25 := by
    intro n
    have hif : spatialStepRate 3 n = Real.sqrt (1 + 2 * ((3:ℕ):ℝ) * 2 ^ ((3:ℕ) - 1)) := by
      unfold spatialStepRate; norm_num
    rw [hif, Real.sq_sqrt (by positivity)]
    norm_num
  have heq : (fun R : ℝ =>
      R ^ ((3 : ℝ) - 4) * (spatialStepRate 3 (⌊s * R ^ 2⌋₊ + 1)) ^ 2)
      = fun R : ℝ => 25 * R ^ (-(1:ℝ)) := by
    funext R
    rw [hrate]
    have : ((3:ℝ) - 4) = -(1:ℝ) := by norm_num
    rw [this]; ring
  rw [heq]
  simpa using (tendsto_rpow_neg_atTop (y := (1:ℝ)) (by norm_num)).const_mul 25

/-! ### `spatialStepRate` is at least `1` and monotone, `1 ≤ d ≤ 3` -/

/-- **`1 ≤ spatialStepRate d n`, `1 ≤ d ≤ 3`.** -/
theorem one_le_spatialStepRate (hd1 : 1 ≤ d) (hd3 : d ≤ 3) (n : ℕ) :
    1 ≤ spatialStepRate d n := by
  interval_cases d
  · have hif : spatialStepRate 1 n = Real.sqrt (2 * (n:ℝ) + 3) := by
      unfold spatialStepRate; norm_num
    rw [hif, Real.le_sqrt (by norm_num) (by positivity)]
    have := (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ)); nlinarith
  · have hif : spatialStepRate 2 n = Real.sqrt (1 + 8 * Real.log ((n:ℝ) + 2)) := by
      unfold spatialStepRate; norm_num
    have hlog : (0:ℝ) ≤ Real.log ((n:ℝ) + 2) :=
      Real.log_nonneg (by have := (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ)); linarith)
    rw [hif, Real.le_sqrt (by norm_num) (by linarith)]
    nlinarith
  · have hif : spatialStepRate 3 n = Real.sqrt (1 + 2 * ((3:ℕ):ℝ) * 2 ^ ((3:ℕ) - 1)) := by
      unfold spatialStepRate; norm_num
    rw [hif, Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num

/-- **`spatialStepRate d` is monotone, `1 ≤ d ≤ 3`.** -/
theorem spatialStepRate_mono (hd1 : 1 ≤ d) (hd3 : d ≤ 3) {m n : ℕ} (hmn : m ≤ n) :
    spatialStepRate d m ≤ spatialStepRate d n := by
  have hmn' : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
  interval_cases d
  · have hifm : spatialStepRate 1 m = Real.sqrt (2 * (m:ℝ) + 3) := by
      unfold spatialStepRate; norm_num
    have hifn : spatialStepRate 1 n = Real.sqrt (2 * (n:ℝ) + 3) := by
      unfold spatialStepRate; norm_num
    rw [hifm, hifn]
    exact Real.sqrt_le_sqrt (by linarith)
  · have hifm : spatialStepRate 2 m = Real.sqrt (1 + 8 * Real.log ((m:ℝ) + 2)) := by
      unfold spatialStepRate; norm_num
    have hifn : spatialStepRate 2 n = Real.sqrt (1 + 8 * Real.log ((n:ℝ) + 2)) := by
      unfold spatialStepRate; norm_num
    rw [hifm, hifn]
    refine Real.sqrt_le_sqrt ?_
    have := Real.log_le_log (by positivity) (show (m:ℝ) + 2 ≤ (n:ℝ) + 2 by linarith)
    linarith
  · have hifm : spatialStepRate 3 m = Real.sqrt (1 + 2 * ((3:ℕ):ℝ) * 2 ^ ((3:ℕ) - 1)) := by
      unfold spatialStepRate; norm_num
    have hifn : spatialStepRate 3 n = Real.sqrt (1 + 2 * ((3:ℕ):ℝ) * 2 ^ ((3:ℕ) - 1)) := by
      unfold spatialStepRate; norm_num
    rw [hifm, hifn]

/-- **The dimension-split asymptotic, `1 ≤ d ≤ 3`.** -/
theorem tendsto_rpow_spatialStepRate_sq_zero (hd1 : 1 ≤ d) (hd3 : d ≤ 3) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun R : ℝ => R ^ ((d : ℝ) - 4) * (spatialStepRate d (⌊s * R ^ 2⌋₊ + 1)) ^ 2)
      atTop (𝓝 0) := by
  interval_cases d
  · simpa using tendsto_rpow_sub_four_mul_stepRate_sq_one hs
  · simpa using tendsto_rpow_sub_four_mul_stepRate_sq_two hs
  · simpa using tendsto_rpow_sub_four_mul_stepRate_sq_three (s := s)

end Parking

end
