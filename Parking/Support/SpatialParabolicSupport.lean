/- A fixed positive-time compact set contains the parabolic test coefficients. -/
import Parking.Support.SpatialCellIntegral

open Set Filter Topology LatticeProb MeasureTheory
noncomputable section
namespace Parking
variable {d : ℕ}

theorem parabolicTime_nonneg {R : ℝ} (s : ℝ) : 0 ≤ parabolicTime R s := by
  unfold parabolicTime
  positivity

theorem parabolicTime_le {R s : ℝ} (hR : 0 < R) (hs : 0 ≤ s) : parabolicTime R s ≤ s :=
  (div_le_iff₀ (sq_pos_of_pos hR)).mpr (Nat.floor_le (mul_nonneg hs (sq_nonneg R)))

theorem parabolicTime_eq_zero_of_nonpos {R s : ℝ} (hs : s ≤ 0) : parabolicTime R s = 0 := by
  simp [parabolicTime, Nat.floor_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hs (sq_nonneg R))]

theorem parabolicTests_eq_zero_of_timeSlices {ψ : ℝ × (Fin d → ℝ) → ℝ} {R : ℝ}
    (p : ℝ × (Fin d → ℝ))
    (hzero : ∀ x, ψ (parabolicTime R p.1, x) = 0)
    (hnext : ∀ x, ψ (parabolicTime R p.1 + 1 / R ^ 2, x) = 0) :
    parabolicTimeTest ψ R p = 0 ∧ parabolicSpaceTest ψ R p = 0 := by
  constructor
  · simp only [parabolicTimeTest, hzero, hnext, sub_self, mul_zero]
  · simp only [parabolicSpaceTest, scaledWalkTest, hnext, walkOp, nbrSum, add_zero,
      Finset.sum_const_zero, zero_div, sub_self, mul_zero]

theorem parabolicTests_eq_zero_of_time_lt {ψ : ℝ × (Fin d → ℝ) → ℝ}
    {a R : ℝ} (ha : 0 < a) (hR : 0 < R) (hmesh : 1 / R ^ 2 < a)
    (hlow : ∀ s x, s < 2 * a → ψ (s, x) = 0)
    {p : ℝ × (Fin d → ℝ)} (hp : p.1 < a) :
    parabolicTimeTest ψ R p = 0 ∧ parabolicSpaceTest ψ R p = 0 := by
  have ht : parabolicTime R p.1 < a := by
    by_cases hs : 0 ≤ p.1
    · exact (parabolicTime_le hR hs).trans_lt hp
    · rw [parabolicTime_eq_zero_of_nonpos (le_of_not_ge hs)]
      exact ha
  exact parabolicTests_eq_zero_of_timeSlices p
    (fun x => hlow _ x (by linarith)) (fun x => hlow _ x (by linarith))

theorem parabolicTests_eq_zero_of_time_gt {ψ : ℝ × (Fin d → ℝ) → ℝ}
    {T R : ℝ} (hT : 0 < T) (hR : 1 ≤ R)
    (hhigh : ∀ s x, T ≤ s → ψ (s, x) = 0)
    {p : ℝ × (Fin d → ℝ)} (hp : T + 1 < p.1) :
    parabolicTimeTest ψ R p = 0 ∧ parabolicSpaceTest ψ R p = 0 := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have hm : 1 / R ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hRpos)).mpr (by nlinarith)
  have habs := abs_parabolicTime_sub_le hRpos (by linarith : 0 ≤ p.1)
  have ht : T ≤ parabolicTime R p.1 := by linarith [neg_le_of_abs_le habs]
  exact parabolicTests_eq_zero_of_timeSlices p
    (fun x => hhigh _ x ht) (fun x => hhigh _ x (by linarith [one_div_pos.mpr (sq_pos_of_pos hRpos)]))

theorem parabolicTests_eq_zero_of_space_gt {ψ : ℝ × (Fin d → ℝ) → ℝ}
    {B R : ℝ} (hR : 1 ≤ R) (hb : ∀ s x, ψ (s, x) ≠ 0 → ‖x‖ ≤ B)
    {p : ℝ × (Fin d → ℝ)} (hp : B + 2 < ‖p.2‖) :
    parabolicTimeTest ψ R p = 0 ∧ parabolicSpaceTest ψ R p = 0 := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  let z : Fin d → ℝ := fun i => ((latticePoint R p.2) i : ℝ) / R
  have hz : ‖z - p.2‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    exact (abs_floor_mul_div_sub_le hRpos (p.2 i)).trans ((div_le_one hRpos).mpr hR)
  have hfar : B < ‖z‖ := by
    have htri := norm_sub_le z (z - p.2)
    have he : z - (z - p.2) = p.2 := by abel
    rw [he] at htri
    linarith
  have hzero : ∀ s, ψ (s, z) = 0 := by
    intro s
    by_contra hn
    exact (not_le.mpr hfar) (hb s z hn)
  constructor
  · change R ^ 2 * (ψ (_, z) - ψ (_, z)) = 0
    simp only [hzero, sub_self, mul_zero]
  · exact scaledWalkTest_eq_zero_of_norm_gt (hb _) hR hp

/-- Both discrete coefficients are supported on one fixed compact subset of positive times. -/
theorem parabolicTests_support_subset {ψ : ℝ × (Fin d → ℝ) → ℝ}
    {a B T R : ℝ} (ha : 0 < a) (hT : 0 < T) (hR : 1 ≤ R) (hmesh : 1 / R ^ 2 < a)
    (hlow : ∀ s x, s < 2 * a → ψ (s, x) = 0)
    (hhigh : ∀ s x, T ≤ s → ψ (s, x) = 0)
    (hb : ∀ s x, ψ (s, x) ≠ 0 → ‖x‖ ≤ B) :
    Function.support (parabolicTimeTest ψ R) ⊆ Icc a (T + 1) ×ˢ Metric.closedBall 0 (B + 2) ∧
    Function.support (parabolicSpaceTest ψ R) ⊆ Icc a (T + 1) ×ˢ Metric.closedBall 0 (B + 2) := by
  have hz : ∀ p : ℝ × (Fin d → ℝ), p ∉ Icc a (T + 1) ×ˢ Metric.closedBall 0 (B + 2) →
      parabolicTimeTest ψ R p = 0 ∧ parabolicSpaceTest ψ R p = 0 := by
    intro p hp
    by_cases hlo : p.1 < a
    · exact parabolicTests_eq_zero_of_time_lt ha (lt_of_lt_of_le one_pos hR) hmesh hlow hlo
    by_cases hhi : T + 1 < p.1
    · exact parabolicTests_eq_zero_of_time_gt hT hR hhigh hhi
    have hx : B + 2 < ‖p.2‖ := by
      by_contra hn
      apply hp
      exact ⟨⟨le_of_not_gt hlo, le_of_not_gt hhi⟩, by simpa using le_of_not_gt hn⟩
    exact parabolicTests_eq_zero_of_space_gt hR hb hx
  exact ⟨fun p hp => by by_contra hn; exact hp (hz p hn).1,
    fun p hp => by by_contra hn; exact hp (hz p hn).2⟩

/-- Past the terminal mesh point, the two sampled time slices both vanish. -/
theorem parabolicTests_eq_zero_outside_strip {ψ : ℝ × (Fin d → ℝ) → ℝ}
    {a T R : ℝ} (ha : 0 < a) (_hT : 0 < T) (hR : 1 ≤ R) (hmesh : 1 / R ^ 2 < a)
    (hlow : ∀ s x, s < 2 * a → ψ (s, x) = 0)
    (hhigh : ∀ s x, T ≤ s → ψ (s, x) = 0)
    {p : ℝ × (Fin d → ℝ)}
    (hp : p.1 ∉ Ico 0 ((⌈T * R ^ 2⌉₊ : ℝ) / R ^ 2)) :
    parabolicTimeTest ψ R p = 0 ∧ parabolicSpaceTest ψ R p = 0 := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  by_cases hs : 0 ≤ p.1
  · have he : (⌈T * R ^ 2⌉₊ : ℝ) / R ^ 2 ≤ p.1 := by
      by_contra hn
      exact hp ⟨hs, lt_of_not_ge hn⟩
    have hn : ⌈T * R ^ 2⌉₊ ≤ ⌊p.1 * R ^ 2⌋₊ :=
      (Nat.le_floor_iff (mul_nonneg hs (sq_nonneg R))).mpr ((div_le_iff₀ (sq_pos_of_pos hRpos)).mp he)
    have ht : T ≤ parabolicTime R p.1 := by
      apply (le_div_iff₀ (sq_pos_of_pos hRpos)).mpr
      exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
    exact parabolicTests_eq_zero_of_timeSlices p
      (fun x => hhigh _ x ht) (fun x => hhigh _ x (by linarith [one_div_pos.mpr (sq_pos_of_pos hRpos)]))
  · exact parabolicTests_eq_zero_of_time_lt ha hRpos hmesh hlow (by linarith)

end Parking
