/-
The pathwise nearest comparison of `parking.tex:1820-1831`.
A positive odometer excludes an unfilled hole. A positive signed pairing
against nonnegative weights finds an active site in their support.
-/
import Parking.Support.HoleCloserEvent
import Parking.Support.NearestHoleFilled
import Parking.Support.NoBoth
import Parking.Support.Continuum

noncomputable section
open MeasureTheory LatticeProb Filter Topology

theorem Parking.not_HoleCloser_of_cleared_ball {d : ℕ} (ω : Parking.Data d) (t : ℕ) (r : ℝ)
    (hh : ∀ x : Parking.Site d, (Parking.graphNorm x : ℝ) ≤ r → Parking.H ω t x = 0)
    (ha : ∃ x : Parking.Site d, (Parking.graphNorm x : ℝ) ≤ r ∧ 0 < Parking.A ω t x) :
    ¬ Parking.HoleCloser ω t := by
  intro hc
  obtain ⟨y, hy, hya⟩ := (Parking.HoleCloser_iff ω t).mp hc
  obtain ⟨x, hx, hax⟩ := ha
  have hn : Parking.graphNorm y < Parking.graphNorm x := by
    simpa [Parking.graphNorm] using hya x hax
  have hnR : (Parking.graphNorm y : ℝ) < (Parking.graphNorm x : ℝ) := by exact_mod_cast hn
  have := hh y (hnR.le.trans hx)
  omega

theorem Parking.latticePoint_div {d : ℕ} {R : ℝ} (hR : R ≠ 0) (y : Parking.Site d) :
    Parking.latticePoint R (fun i => (y i : ℝ) / R) = y := by
  funext i
  simp [Parking.latticePoint, mul_div_cancel₀ _ hR]

theorem Parking.exists_positive_weight_of_tsum_pos {ι : Type*} (a h : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : 0 < ∑' i, ((a i : ℝ) - (h i : ℝ)) * w i) :
    ∃ i, 0 < a i ∧ 0 < w i := by
  by_contra! hn
  have hsum : (∑' i, ((a i : ℝ) - (h i : ℝ)) * w i) ≤ 0 := by
    apply tsum_nonpos
    intro i
    by_cases ha : 0 < a i
    · have hz : w i = 0 := le_antisymm (hn i ha) (hw i)
      simp [hz]
    · have hz : a i = 0 := by omega
      simp only [hz, Nat.cast_zero, zero_sub]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (hw i)
  linarith

theorem Parking.graphNorm_rescale {d : ℕ} {R : ℝ} (hR : 0 < R) (y : Parking.Site d) :
    (∑ i : Fin d, |(y i : ℝ) / R|) = (Parking.graphNorm y : ℝ) / R := by
  simp [abs_div, abs_of_pos hR, Parking.graphNorm, Nat.cast_sum, Nat.cast_natAbs,
    Int.cast_abs, Finset.sum_div]

theorem Parking.U_pos_of_barOdometer_pos {d : ℕ} (ω : Parking.Data d) (R s : ℝ)
    (x : Fin d → ℝ) (h : 0 < Parking.barOdometer ω R s x) :
    0 < Parking.U ω ⌊s * R ^ 2⌋₊ (Parking.latticePoint R x) := by
  by_contra! hz
  have he : Parking.U ω ⌊s * R ^ 2⌋₊ (Parking.latticePoint R x) = 0 := by omega
  simp [Parking.barOdometer, he] at h

theorem Parking.not_HoleCloser_of_signedPair_pos {d : ℕ} (ω : Parking.Data d) {R r : ℝ}
    (hR : 0 < R) (φ : (Fin d → ℝ) → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (hsupp : ∀ x, 0 < φ x → (∑ i : Fin d, |x i|) ≤ r)
    (hH : ∀ y : Parking.Site d, (Parking.graphNorm y : ℝ) ≤ r * R → Parking.H ω ⌊R ^ 2⌋₊ y = 0)
    (hpair : 0 < Parking.signedPair ω R φ) :
    ¬ Parking.HoleCloser ω ⌊R ^ 2⌋₊ := by
  have hc := Real.rpow_pos_of_pos hR (-(d : ℝ) / 2)
  have hs : 0 < ∑' y : Parking.Site d,
      ((Parking.A ω ⌊R ^ 2⌋₊ y : ℝ) - (Parking.H ω ⌊R ^ 2⌋₊ y : ℝ)) *
        φ (fun i => (y i : ℝ) / R) := (mul_pos_iff_of_pos_left hc).mp hpair
  obtain ⟨y, hyA, hyφ⟩ := Parking.exists_positive_weight_of_tsum_pos
    (Parking.A ω ⌊R ^ 2⌋₊) (Parking.H ω ⌊R ^ 2⌋₊)
    (fun y => φ (fun i => (y i : ℝ) / R)) (fun _ => hφ _) hs
  have hnorm := hsupp _ hyφ
  rw [Parking.graphNorm_rescale hR y] at hnorm
  exact Parking.not_HoleCloser_of_cleared_ball ω _ _ hH
    ⟨y, (div_le_iff₀ hR).mp hnorm, hyA⟩

theorem Parking.positive_U_ball_of_barOdometer {d : ℕ} (ω : Parking.Data d) {R r : ℝ}
    (hR : 0 < R)
    (hU : ∀ x : Fin d → ℝ, (∑ i, |x i|) ≤ r → 0 < Parking.barOdometer ω R 1 x) :
    ∀ y : Parking.Site d, (Parking.graphNorm y : ℝ) ≤ r * R → 0 < Parking.U ω ⌊R ^ 2⌋₊ y := by
  intro y hy
  have hn : (∑ i : Fin d, |(y i : ℝ) / R|) ≤ r := by
    rw [Parking.graphNorm_rescale hR]
    exact (div_le_iff₀ hR).mpr hy
  have hu := Parking.U_pos_of_barOdometer_pos ω R 1 _ (hU _ hn)
  simpa only [one_mul, Parking.latticePoint_div hR.ne'] using hu

theorem Parking.activeDistance_le_of_active {d : ℕ} (ω : Parking.Data d) (t : ℕ)
    (x : Parking.Site d) (hx : 0 < Parking.A ω t x) :
    Parking.activeDistance ω t ≤ (Parking.graphNorm x : ℕ∞) := by
  exact iInf_le_of_le x (iInf_le_of_le hx le_rfl)

theorem Parking.radius_lt_holeDistance_of_cleared {d : ℕ} (ω : Parking.Data d) (t r : ℕ)
    (hh : ∀ x : Parking.Site d, Parking.graphNorm x ≤ r → Parking.H ω t x = 0) :
    (r : ℕ∞) < Parking.holeDistance ω t := by
  have hs : ((r + 1 : ℕ) : ℕ∞) ≤ Parking.holeDistance ω t := by
    apply le_iInf
    intro x
    apply le_iInf
    intro hx
    have hn : r < Parking.graphNorm x := by
      by_contra! hn
      have := hh x hn
      change 0 < Parking.H ω t x at hx
      omega
    exact_mod_cast Nat.succ_le_of_lt hn
  have hr : (r : ℕ∞) < ((r + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self r
  exact hr.trans_le hs

end
