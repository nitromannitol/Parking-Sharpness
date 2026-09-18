import Parking.Support.MomentTail

noncomputable section
namespace Parking
open MeasureTheory

/-- A sufficiently small multiple of the mean gives a norm at most a quarter of it. -/
theorem exists_small_moment_scale {C g : ℝ} (hC : 0 < C) (hg : 1 ≤ g) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℝ, 0 ≤ m →
      C * (Real.sqrt ((δ * m) * (m + δ * m)) + δ * m) ≤ m / (4 * g) := by
  let a := 1 / (16 * g * (C + 1))
  have hg0 : 0 < g := by linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hae : 16 * g * (C + 1) * a = 1 := by dsimp [a]; field_simp
  have ha1 : a ≤ 1 := by
    dsimp [a]
    apply (div_le_one (by positivity)).mpr
    nlinarith
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hca : 3 * C * a ≤ 1 / (4 * g) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [mul_pos hg0 ha]
  refine ⟨a ^ 2, sq_pos_of_pos ha, fun m hm => ?_⟩
  have hsq : Real.sqrt ((a ^ 2 * m) * (m + a ^ 2 * m)) ≤ 2 * a * m := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [mul_nonneg (sq_nonneg (a * m)) (sub_nonneg.mpr ha2)]
  have ham : a ^ 2 * m ≤ a * m := mul_le_mul_of_nonneg_right (by nlinarith : a ^ 2 ≤ a) hm
  have hmca := mul_le_mul_of_nonneg_right hca hm
  have he : 1 / (4 * g) * m = m / (4 * g) := by ring
  rw [he] at hmca
  nlinarith [mul_le_mul_of_nonneg_left hsq hC.le, mul_le_mul_of_nonneg_left ham hC.le]

/-- Bernstein moment growth implies an exponential lower tail at half the mean scale. -/
theorem exists_exponential_lower_tail {Ω : Type} [MeasurableSpace Ω]
    {C g : ℝ} (hC : 0 < C) (hg : 1 ≤ g) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (μ : Measure Ω), IsProbabilityMeasure μ →
      ∀ (X : Ω → ℝ) (m b : ℝ), 0 ≤ m → m / g ≤ b →
      (∀ r : ℝ, 2 ≤ r → Integrable (fun ω => |X ω - b| ^ r) μ) →
      (∀ r : ℝ, 2 ≤ r → rNorm μ r (fun ω => X ω - b) ≤
        C * (Real.sqrt (r * (m + r)) + r)) →
      (μ {ω | X ω < m / (2 * g)}).toReal ≤ A * Real.exp (-c * m) := by
  obtain ⟨δ, hδ, hscale⟩ := exists_small_moment_scale hC hg
  let l := -Real.log (1 / 2 : ℝ)
  have hl : 0 < l := neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num))
  refine ⟨Real.exp (2 * l), δ * l, Real.exp_pos _, mul_pos hδ hl, fun μ hμ X m b hm hb hi hn => ?_⟩
  letI := hμ
  have hg0 : 0 < g := by linarith
  by_cases hr : 2 ≤ δ * m
  · have hm0 : 0 < m := by nlinarith
    have ha : 0 < m / (2 * g) := by positivity
    have hsub : (μ {ω | X ω < m / (2 * g)}).toReal ≤
        (μ {ω | m / (2 * g) < |X ω - b|}).toReal := by
      apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono _)
      intro ω hω
      have he : m / g = 2 * (m / (2 * g)) := by field_simp
      change X ω < m / (2 * g) at hω
      have hab := neg_le_abs (X ω - b)
      change m / (2 * g) < |X ω - b|
      rw [he] at hb
      linarith
    have hnorm := (hn (δ * m) hr).trans (hscale m hm)
    have hratio : rNorm μ (δ * m) (fun ω => X ω - b) / (m / (2 * g)) ≤ 1 / 2 := by
      apply (div_le_iff₀ ha).mpr
      have he : (1 / 2 : ℝ) * (m / (2 * g)) = m / (4 * g) := by ring
      rwa [he]
    have hmkv := measure_gt_le_rNorm_div_rpow μ (fun ω => X ω - b) (by linarith : 0 < δ * m) ha (hi _ hr)
    have hpow := Real.rpow_le_rpow (div_nonneg (rNorm_nonneg _ _ _) ha.le) hratio (by linarith : 0 ≤ δ * m)
    have he : (1 / 2 : ℝ) ^ (δ * m) = Real.exp (-(δ * l) * m) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      congr 1
      dsimp [l]
      ring
    rw [he] at hpow
    apply (hsub.trans (hmkv.trans hpow)).trans
    exact le_mul_of_one_le_left (Real.exp_pos _).le (Real.one_le_exp_iff.mpr (by positivity))
  · have hprob : (μ {ω | X ω < m / (2 * g)}).toReal ≤ 1 := by
      exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))).trans_eq (by simp)
    apply hprob.trans
    rw [← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith
end Parking
