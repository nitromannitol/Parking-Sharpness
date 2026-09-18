/- Step 3 of the proof of `thm:oriented-walk` (`parking.tex:3302-3322`): the
particle odometer and the divisible odometer have the same mean to order
`n^{1/8}[log(n+1)]^{3/4}`, which is `o(n^{1/4})`.
-/
import Parking.Support.OrientedStepMoments
import Parking.Support.OrientedMeanBound
import Parking.Support.OrientedMeanComparison

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset

/-- `log(n+1) ≤ 3√n`. -/
theorem log_le_three_sqrt (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1) ≤ 3 * Real.sqrt (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hsq : Real.log (Real.sqrt ((n : ℝ) + 1)) = Real.log ((n : ℝ) + 1) / 2 :=
    Real.log_sqrt (by linarith)
  have hle : Real.log (Real.sqrt ((n : ℝ) + 1)) ≤ Real.sqrt ((n : ℝ) + 1) - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hpos)
  have h2 : Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt (2 * (n : ℝ)) :=
    Real.sqrt_le_sqrt (by linarith)
  have h3 : Real.sqrt (2 * (n : ℝ)) = Real.sqrt 2 * Real.sqrt (n : ℝ) :=
    Real.sqrt_mul (by norm_num) _
  have h4 : Real.sqrt 2 ≤ 1.5 := by
    have : Real.sqrt 2 ≤ Real.sqrt 2.25 := Real.sqrt_le_sqrt (by norm_num)
    have h : Real.sqrt 2.25 = 1.5 := by
      rw [show (2.25 : ℝ) = 1.5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have h5 : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  rw [hsq] at hle
  nlinarith

/-- The `L^{r}` bound on the directed particle odometer at `d = 2` with the
logarithmic exponent of Step 3. -/
theorem exists_oriented_two_log_moment (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration) (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (∫ ω : Data 2, (U ω n 0 : ℝ) ^ (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ) ∂(orientedLaw 2 ν)) ^
          ((1 : ℝ) / (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ))
        ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (Real.log ((n : ℝ) + 1)) := by
  haveI := hν.prob
  obtain ⟨C₀, hC₀, hrec⟩ := exists_oriented_U_moment_recursion hBern
  obtain ⟨C₁, hC₁, hu⟩ := exists_oriented_uOriented_norm (d := 2) (by norm_num) hConc ν hν
  obtain ⟨θ, hθ, hexp⟩ := hν.expMoment
  have hmom8 : Integrable (fun k : ℤ => |(k : ℝ)| ^ (8 : ℝ)) ν := by
    obtain ⟨K, hK, hbd⟩ := rpow_le_const_mul_exp (by norm_num : (0:ℝ) ≤ (8:ℝ)) hθ
    refine Integrable.mono' (hexp.const_mul K)
      (measurable_from_countable' (fun k : ℤ => |(k : ℝ)| ^ (8 : ℝ))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact hbd _ (abs_nonneg _)
  obtain ⟨C₂, hC₂, hmean⟩ := exists_meanuOriented_two_upper ν hν.mean 8 (by norm_num) hmom8
  refine ⟨2 * (2 * C₂ + 2 * C₁ + 4 * Real.sqrt 3 * C₁)
    + (9 * C₀ ^ 2 + 6 * C₀) * 4 * Real.sqrt 3, by positivity, fun n hn => ?_⟩
  set L : ℝ := Real.log ((n : ℝ) + 1) with hL
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hL0 : 0 < L := by linarith
  have hsqL : Real.sqrt (Real.log 2) ≤ Real.sqrt L := Real.sqrt_le_sqrt hL2
  have hsqL0 : (0.8 : ℝ) ≤ Real.sqrt L := by
    have h : Real.sqrt (0.64 : ℝ) ≤ Real.sqrt (Real.log 2) := Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt (0.64 : ℝ) = 0.8 := by
      rw [show (0.64 : ℝ) = 0.8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have hsqLsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  -- `√L ≤ √3 n^{1/4}`
  have hq4 : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hq4sq : (n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4) = Real.sqrt (n : ℝ) := by
    rw [← Real.rpow_add (by linarith), Real.sqrt_eq_rpow]
    norm_num
  have hsqLq : Real.sqrt L ≤ Real.sqrt 3 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have h1 : L ≤ 3 * Real.sqrt (n : ℝ) := by rw [hL]; exact log_le_three_sqrt n hn
    have h2 : Real.sqrt L ≤ Real.sqrt (3 * Real.sqrt (n : ℝ)) := Real.sqrt_le_sqrt h1
    have h3 : Real.sqrt (3 * Real.sqrt (n : ℝ))
        = Real.sqrt 3 * Real.sqrt (Real.sqrt (n : ℝ)) := Real.sqrt_mul (by norm_num) _
    have h4 : Real.sqrt (Real.sqrt (n : ℝ)) = (n : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n)]
      norm_num
    rw [h3, h4] at h2
    exact h2
  set rn : ℝ := (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ) with hrn
  have hrn2 : (2 : ℝ) ≤ rn := le_max_left _ _
  have hrnL : L ≤ rn := le_trans (Nat.le_ceil L) (le_max_right _ _)
  have hrnub : rn ≤ 2 + L := by
    refine max_le (by linarith) ?_
    have := Nat.ceil_lt_add_one (le_of_lt hL0)
    linarith
  have hrn4 : rn ≤ 4 * L := by linarith
  have hrn0 : (0 : ℝ) ≤ rn := by linarith
  set A : ℝ := (∫ ω : Data 2, (U ω n 0 : ℝ) ^ rn ∂(orientedLaw 2 ν)) ^ ((1 : ℝ) / rn) with hA
  have hI0 : (0 : ℝ) ≤ ∫ ω : Data 2, (U ω n 0 : ℝ) ^ rn ∂(orientedLaw 2 ν) :=
    integral_nonneg fun ω => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hA0 : 0 ≤ A := Real.rpow_nonneg hI0 _
  -- the divisible moment at the logarithmic exponent
  have hkappa : orientedKappa 2 n = Real.sqrt (n : ℝ) := by
    rw [orientedKappa, if_pos rfl, Real.sqrt_eq_rpow]
  have hsq : Real.sqrt (rn * orientedKappa 2 n)
      ≤ 2 * Real.sqrt L * (n : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [hkappa]
    have h1 : rn * Real.sqrt (n : ℝ) ≤ (4 * L) * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_right hrn4 (Real.sqrt_nonneg _)
    refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
    rw [← hq4sq, show (4 : ℝ) * L * ((n : ℝ) ^ ((1:ℝ)/4) * (n : ℝ) ^ ((1:ℝ)/4))
        = (2 * Real.sqrt L * (n : ℝ) ^ ((1:ℝ)/4)) ^ 2 by
      rw [mul_pow, mul_pow]; rw [Real.sq_sqrt hL0.le]; ring]
    exact Real.sqrt_sq (by positivity)
  have hDu : (∫ ω : Data 2, |uOriented (confReal ω) n 0| ^ rn ∂(orientedLaw 2 ν)) ^
      ((1 : ℝ) / rn)
      ≤ (2 * C₂ + 2 * C₁ + 4 * Real.sqrt 3 * C₁) * ((n : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt L) := by
    refine (hu n hn rn hrn2).trans ?_
    have h1 := hmean n hn
    have h2 : rn ≤ 4 * Real.sqrt 3 * ((n : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt L) := by
      have : rn ≤ 4 * (Real.sqrt L * Real.sqrt L) := by rw [hsqLsq]; linarith
      nlinarith [hsqLq, Real.sqrt_nonneg L]
    have hCq : (0 : ℝ) ≤ C₂ * (n : ℝ) ^ ((1 : ℝ) / 4) := mul_nonneg hC₂.le hq4
    have h3 : C₂ * (n : ℝ) ^ ((1 : ℝ) / 4)
        ≤ 2 * C₂ * ((n : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt L) := by
      have h := mul_le_mul_of_nonneg_left hsqL0 hCq
      nlinarith [h]
    have h4 : C₁ * (Real.sqrt (rn * orientedKappa 2 n) + rn)
        ≤ C₁ * (2 * Real.sqrt L * (n : ℝ) ^ ((1 : ℝ) / 4)
          + 4 * Real.sqrt 3 * ((n : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt L)) :=
      mul_le_mul_of_nonneg_left (by linarith [hsq, h2]) hC₁.le
    linarith [h3, h4, h1]
  -- the recursion and Young's inequality
  have hstep := hrec 2 (by norm_num) ν hν n rn hrn2
  have hpre : ((n : ℝ) + 1) ^ ((1 : ℝ) / rn) ≤ 3 := by
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hle : Real.log ((n : ℝ) + 1) * (1 / rn) ≤ 1 := by
      rw [mul_one_div, div_le_one (by linarith)]
      exact hrnL
    rw [Real.rpow_def_of_pos hpos]
    calc Real.exp (Real.log ((n : ℝ) + 1) * (1 / rn)) ≤ Real.exp 1 := Real.exp_le_exp.mpr hle
      _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hsqrtA : Real.sqrt rn * A ^ ((1 : ℝ) / 2) = Real.sqrt (rn * A) := by
    rw [Real.sqrt_mul hrn0, Real.sqrt_eq_rpow A]
  set Du : ℝ := (∫ ω : Data 2, |uOriented (confReal ω) n 0| ^ rn ∂(orientedLaw 2 ν)) ^
    ((1 : ℝ) / rn) with hDudef
  have hDu0 : 0 ≤ Du :=
    Real.rpow_nonneg (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _) _
  have hyoung : A ≤ Du + (3 * C₀) * (Real.sqrt (rn * A) + rn) := by
    have h0 : (0 : ℝ) ≤ Real.sqrt (rn * A) + rn := by
      have := Real.sqrt_nonneg (rn * A); linarith
    have h1 : C₀ * ((n : ℝ) + 1) ^ ((1 : ℝ) / rn) ≤ C₀ * 3 :=
      mul_le_mul_of_nonneg_left hpre hC₀.le
    rw [hsqrtA] at hstep
    have h2 : C₀ * ((n : ℝ) + 1) ^ ((1 : ℝ) / rn) * (Real.sqrt (rn * A) + rn)
        ≤ (3 * C₀) * (Real.sqrt (rn * A) + rn) := by
      have h := mul_le_mul_of_nonneg_right h1 h0
      linarith [h]
    linarith [hstep, h2]
  have habs := young_absorb hA0 hrn0 hyoung
  have hrnq : rn ≤ 4 * Real.sqrt 3 * ((n : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt L) := by
    have : rn ≤ 4 * (Real.sqrt L * Real.sqrt L) := by rw [hsqLsq]; linarith
    nlinarith [hsqLq, Real.sqrt_nonneg L]
  rw [mul_assoc]
  set P : ℝ := (n : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt L with hP
  have hcoef : (0 : ℝ) ≤ (3 * C₀) ^ 2 + 2 * (3 * C₀) := by positivity
  have h2 : ((3 * C₀) ^ 2 + 2 * (3 * C₀)) * rn
      ≤ ((3 * C₀) ^ 2 + 2 * (3 * C₀)) * (4 * Real.sqrt 3 * P) :=
    mul_le_mul_of_nonneg_left hrnq hcoef
  linarith [habs, hDu, h2]

/-- **Step 3.**  The directed particle mean and the directed divisible mean agree
to order `n^{1/8}[log(n+1)]^{3/4}`. -/
theorem exists_oriented_herr (hBern : Parking.External.Bernstein)
    (hConc : Parking.External.UConcentration) (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      |meanU (orientedLaw 2 ν) n - meanuOriented (orientedLaw 2 ν) n| ≤
        C * (n : ℝ) ^ ((1 : ℝ) / 8) * Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (orientedLaw 2 ν) := orientedLaw_isProbability (by norm_num) ν
  obtain ⟨C₀, hC₀, hb⟩ := exists_oriented_wErr_moment_law hBern
  obtain ⟨C₄, hC₄, hAb⟩ := exists_oriented_two_log_moment hBern hConc ν hν
  refine ⟨4 * C₀ * (2 * Real.sqrt C₄ + 24), by positivity, fun n hn => ?_⟩
  set L : ℝ := Real.log ((n : ℝ) + 1) with hL
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hL0 : 0 < L := by linarith
  set rn : ℝ := (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ) with hrn
  have hrn2 : (2 : ℝ) ≤ rn := le_max_left _ _
  have hrn1 : (1 : ℝ) ≤ rn := by linarith
  have hrnL : L ≤ rn := le_trans (Nat.le_ceil L) (le_max_right _ _)
  have hrnub : rn ≤ 2 + L := by
    refine max_le (by linarith) ?_
    have := Nat.ceil_lt_add_one (le_of_lt hL0)
    linarith
  have hrn4 : rn ≤ 4 * L := by linarith
  have hrn0 : (0 : ℝ) ≤ rn := by linarith
  set A : ℝ := (∫ ω : Data 2, (U ω n 0 : ℝ) ^ rn ∂(orientedLaw 2 ν)) ^ ((1 : ℝ) / rn) with hA
  have hI0 : (0 : ℝ) ≤ ∫ ω : Data 2, (U ω n 0 : ℝ) ^ rn ∂(orientedLaw 2 ν) :=
    integral_nonneg fun ω => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hA0 : 0 ≤ A := Real.rpow_nonneg hI0 _
  set q8 : ℝ := (n : ℝ) ^ ((1 : ℝ) / 8) with hq8
  have hq80 : (0 : ℝ) < q8 := Real.rpow_pos_of_pos hnpos _
  set M : ℝ := L ^ ((3 : ℝ) / 4) with hM
  have hM0 : (0 : ℝ) < M := Real.rpow_pos_of_pos hL0 _
  -- `L ≤ 2 q8 M`
  have hL14 : L ^ ((1 : ℝ) / 4) ≤ 2 * q8 := by
    have h1 : L ≤ 3 * (n : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [hL, ← Real.sqrt_eq_rpow]; exact log_le_three_sqrt n hn
    have h2 : L ^ ((1 : ℝ) / 4) ≤ (3 * (n : ℝ) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow hL0.le h1 (by norm_num)
    have h3 : (3 * (n : ℝ) ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 4)
        = (3 : ℝ) ^ ((1 : ℝ) / 4) * q8 := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _),
        ← Real.rpow_mul (Nat.cast_nonneg n), hq8]
      norm_num
    have h4 : (3 : ℝ) ^ ((1 : ℝ) / 4) ≤ 2 := by
      calc (3 : ℝ) ^ ((1 : ℝ) / 4) ≤ (16 : ℝ) ^ ((1 : ℝ) / 4) :=
            Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
        _ = 2 := by
            rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 4,
              ← Real.rpow_mul (by norm_num)]
            norm_num
    rw [h3] at h2
    nlinarith [hq80.le]
  have hLsplit : L = L ^ ((1 : ℝ) / 4) * M := by
    rw [hM, ← Real.rpow_add hL0]; norm_num
  have hLle : L ≤ 2 * q8 * M := by
    rw [hLsplit]
    exact mul_le_mul_of_nonneg_right hL14 hM0.le
  -- `√rn * A^{1/2} ≤ 2 √C₄ q8 M`
  have hAhalf : A ^ ((1 : ℝ) / 2)
      ≤ Real.sqrt C₄ * (q8 * L ^ ((1 : ℝ) / 4)) := by
    have h1 : A ≤ C₄ * (n : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt L := hAb n hn
    have hRnn : (0 : ℝ) ≤ C₄ * (n : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt L := by positivity
    have h2 : A ^ ((1 : ℝ) / 2)
        ≤ (C₄ * (n : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt L) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow hA0 h1 (by norm_num)
    have h3 : (C₄ * (n : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt L) ^ ((1 : ℝ) / 2)
        = Real.sqrt C₄ * (q8 * L ^ ((1 : ℝ) / 4)) := by
      rw [Real.sqrt_eq_rpow L, Real.mul_rpow (by positivity)
          (Real.rpow_nonneg hL0.le _),
        Real.mul_rpow hC₄.le (Real.rpow_nonneg (Nat.cast_nonneg n) _),
        ← Real.rpow_mul (Nat.cast_nonneg n), ← Real.rpow_mul hL0.le,
        Real.sqrt_eq_rpow C₄, hq8]
      norm_num
      ring
    rw [h3] at h2
    exact h2
  have hrnhalf : Real.sqrt rn ≤ 2 * L ^ ((1 : ℝ) / 2) := by
    have h1 : Real.sqrt rn ≤ Real.sqrt (4 * L) := Real.sqrt_le_sqrt hrn4
    have h2 : Real.sqrt (4 * L) = 2 * L ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow L,
        show Real.sqrt 4 = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    linarith [h1, h2.le, h2.ge]
  have hLprod : L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 4) = M := by
    rw [← Real.rpow_add hL0, hM]; norm_num
  have hmix : Real.sqrt rn * A ^ ((1 : ℝ) / 2) ≤ 2 * Real.sqrt C₄ * (q8 * M) := by
    have hAh0 : 0 ≤ A ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hA0 _
    have h := mul_le_mul hrnhalf hAhalf hAh0 (by positivity)
    calc Real.sqrt rn * A ^ ((1 : ℝ) / 2)
        ≤ (2 * L ^ ((1 : ℝ) / 2)) * (Real.sqrt C₄ * (q8 * L ^ ((1 : ℝ) / 4))) := h
      _ = 2 * Real.sqrt C₄ * (q8 * (L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 4))) := by ring
      _ = 2 * Real.sqrt C₄ * (q8 * M) := by rw [hLprod]
  -- the moment bound on the error field at every round up to `n`
  set B : ℝ := C₀ * (Real.sqrt rn * A ^ ((1 : ℝ) / 2) + rn) with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ Real.sqrt rn * A ^ ((1 : ℝ) / 2) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hA0 _)
    have : 0 ≤ Real.sqrt rn * A ^ ((1 : ℝ) / 2) + rn := by linarith
    exact mul_nonneg hC₀.le this
  have hbnd : ∀ m ≤ n,
      (∫ ω : Data 2, |wErrOriented ω.1 ω.2.1 m 0| ^ rn ∂(orientedLaw 2 ν)) ^ (1 / rn) ≤ B := by
    intro m hm
    refine (hb 2 (by norm_num) ν hν m rn hrn2).trans ?_
    have hhalf := oriented_half_moment_le (d := 2) (by norm_num) ν hν hrn2
      (m := m - 1) (n := n) (by omega)
    have := mul_le_mul_of_nonneg_left hhalf (Real.sqrt_nonneg rn)
    exact mul_le_mul_of_nonneg_left (by linarith) hC₀.le
  -- the four integrabilities
  have hIU : Integrable (fun ω : Data 2 => (U ω n 0 : ℝ)) (orientedLaw 2 ν) :=
    integrable_oriented_U (by norm_num) ν hν n 0
  have hIu : Integrable (fun ω : Data 2 => uOriented (fun y => (ω.1 y : ℝ)) n 0)
      (orientedLaw 2 ν) :=
    integrable_abs_of_rpow _ hrn1 _
      ((measurable_uOriented n 0).comp measurable_confReal).aestronglyMeasurable
      (integrable_oriented_uOriented_rpow (by norm_num) ν hν hrn1 n 0)
  have hIwr : Integrable (fun ω : Data 2 => |wErrOriented ω.1 ω.2.1 n 0|)
      (orientedLaw 2 ν) :=
    (integrable_abs_of_rpow _ hrn1 _ (measurable_wErrOriented n 0).aestronglyMeasurable
      (integrable_abs_wErrOriented_rpow (by norm_num) ν hν hrn1 n 0)).abs
  have hWabs : (fun ω : Data 2 => |wStarOriented ω.1 ω.2.1 n 0| ^ rn)
      = fun ω : Data 2 => wStarOriented ω.1 ω.2.1 n 0 ^ rn := by
    funext ω; rw [abs_of_nonneg (wStarOriented_nonneg _ _ n 0)]
  have hIws : Integrable (fun ω : Data 2 => wStarOriented ω.1 ω.2.1 n 0 ^ rn)
      (orientedLaw 2 ν) := integrable_wStarOriented_rpow (by norm_num) ν hν hrn1 n
  have hIs : Integrable (fun ω : Data 2 => wStarOriented ω.1 ω.2.1 n 0) (orientedLaw 2 ν) :=
    integrable_abs_of_rpow _ hrn1 _
      (measurable_wStarOriented (by norm_num) n 0).aestronglyMeasurable (by rw [hWabs]; exact hIws)
  -- the two error integrals
  have hwr : (∫ ω : Data 2, |wErrOriented ω.1 ω.2.1 n 0| ∂(orientedLaw 2 ν)) ≤ B := by
    refine le_trans (integral_le_rNorm (fun ω => abs_nonneg _) hIwr hrn1 ?_) ?_
    · exact integrable_abs_wErrOriented_rpow (by norm_num) ν hν hrn1 n 0
    · exact hbnd n le_rfl
  have hws : (∫ ω : Data 2, wStarOriented ω.1 ω.2.1 n 0 ∂(orientedLaw 2 ν)) ≤ 3 * B := by
    refine le_trans (integral_le_rNorm (fun ω => wStarOriented_nonneg _ _ n 0) hIs hrn1 hIws) ?_
    refine (wStarOriented_moment_le (by norm_num) ν hν hrn1 n B hB0 hbnd).trans ?_
    have hpre : ((n : ℝ) + 1) ^ ((1 : ℝ) / rn) ≤ 3 := by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
      have hle : Real.log ((n : ℝ) + 1) * (1 / rn) ≤ 1 := by
        rw [mul_one_div, div_le_one (by linarith)]
        exact hrnL
      rw [Real.rpow_def_of_pos hpos]
      calc Real.exp (Real.log ((n : ℝ) + 1) * (1 / rn)) ≤ Real.exp 1 := Real.exp_le_exp.mpr hle
        _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
    exact mul_le_mul_of_nonneg_right hpre hB0
  -- the comparison of the two means
  have hlow := meanuOriented_le_meanU (d := 2) (by norm_num) ν hν n
  have hupp := meanU_oriented_le_meanu_add_errors (d := 2) (by norm_num) ν n hIU hIu hIwr hIs
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ meanU (orientedLaw 2 ν) n
    - meanuOriented (orientedLaw 2 ν) n)]
  have hBle : B ≤ C₀ * (2 * Real.sqrt C₄ + 24) * (q8 * M) := by
    have h1 : rn ≤ 4 * (2 * q8 * M) := by linarith
    have h2 : Real.sqrt rn * A ^ ((1 : ℝ) / 2) + rn
        ≤ (2 * Real.sqrt C₄ + 24) * (q8 * M) := by nlinarith [hmix, h1]
    calc B ≤ C₀ * ((2 * Real.sqrt C₄ + 24) * (q8 * M)) :=
          mul_le_mul_of_nonneg_left h2 hC₀.le
      _ = C₀ * (2 * Real.sqrt C₄ + 24) * (q8 * M) := by ring
  have hfinal : meanU (orientedLaw 2 ν) n - meanuOriented (orientedLaw 2 ν) n ≤ 4 * B := by
    linarith [hupp, hwr, hws]
  calc meanU (orientedLaw 2 ν) n - meanuOriented (orientedLaw 2 ν) n ≤ 4 * B := hfinal
    _ ≤ 4 * (C₀ * (2 * Real.sqrt C₄ + 24) * (q8 * M)) := by linarith
    _ = 4 * C₀ * (2 * Real.sqrt C₄ + 24) * q8 * M := by ring

end Parking
end
