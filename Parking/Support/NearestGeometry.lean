import Parking.Support.HoleCloserEvent
import Parking.Support.NearestHoleFilled
import Parking.Support.NoBoth
import Parking.Support.Continuum

/-!
# Pathwise geometry for the nearest-hole comparison

The pathwise nearest comparison of `parking.tex:1835-1846`.
A positive odometer excludes an unfilled hole. A positive signed pairing
against nonnegative weights finds an active site in their support.
-/

noncomputable section
open MeasureTheory LatticeProb Filter Topology

/-- If every hole within graph-distance `r` is empty but some site within `r` is active, then
`ω` is not a `HoleCloser` at `t`: the closest surviving hole from `HoleCloser_iff` would have
to be nearer than the active site, contradicting `hh`. -/
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

/-- Rescaling a lattice point `y` by `1/R` and applying `latticePoint R` recovers `y`, for
`R ≠ 0`. -/
theorem Parking.latticePoint_div {d : ℕ} {R : ℝ} (hR : R ≠ 0) (y : Parking.Site d) :
    Parking.latticePoint R (fun i => (y i : ℝ) / R) = y := by
  funext i
  simp [Parking.latticePoint, mul_div_cancel₀ _ hR]

/-- If the weighted sum `∑' (a i - h i) * w i` is positive with all weights `w i ≥ 0`, some
index has both `a i > 0` and `w i > 0`; otherwise every term would be nonpositive. -/
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

/-- Rescaling each coordinate of `y` by `1/R` divides the `graphNorm` by `R`, for `R > 0`. -/
theorem Parking.graphNorm_rescale {d : ℕ} {R : ℝ} (hR : 0 < R) (y : Parking.Site d) :
    (∑ i : Fin d, |(y i : ℝ) / R|) = (Parking.graphNorm y : ℝ) / R := by
  simp [abs_div, abs_of_pos hR, Parking.graphNorm, Nat.cast_sum, Nat.cast_natAbs,
    Int.cast_abs, Finset.sum_div]

/-- A positive continuum odometer `barOdometer ω R s x` forces the lattice odometer `U` at the
rounded point `latticePoint R x` to be positive, since `barOdometer` unfolds to a rescaling of
`U`. -/
theorem Parking.U_pos_of_barOdometer_pos {d : ℕ} (ω : Parking.Data d) (R s : ℝ)
    (x : Fin d → ℝ) (h : 0 < Parking.barOdometer ω R s x) :
    0 < Parking.U ω ⌊s * R ^ 2⌋₊ (Parking.latticePoint R x) := by
  by_contra! hz
  have he : Parking.U ω ⌊s * R ^ 2⌋₊ (Parking.latticePoint R x) = 0 := by omega
  simp [Parking.barOdometer, he] at h

/-- If every hole within radius `rR` is cleared and the signed pairing `signedPair ω R φ`
against a nonnegative `φ` is positive, some active site lies in `φ`'s support by
`exists_positive_weight_of_tsum_pos`, so `not_HoleCloser_of_cleared_ball` rules out `ω` being a
`HoleCloser` at `⌊R²⌋₊`. -/
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

/-- If the continuum odometer `barOdometer ω R 1` is positive on the ball of radius `r`, the
lattice odometer `U ω ⌊R²⌋₊` is positive at every lattice point within `rR`, via
`U_pos_of_barOdometer_pos` and `graphNorm_rescale`. -/
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

/-- An active site `x` at time `t` bounds `activeDistance ω t` above by `graphNorm x`, since the
distance is an infimum over active sites. -/
theorem Parking.activeDistance_le_of_active {d : ℕ} (ω : Parking.Data d) (t : ℕ)
    (x : Parking.Site d) (hx : 0 < Parking.A ω t x) :
    Parking.activeDistance ω t ≤ (Parking.graphNorm x : ℕ∞) := by
  exact iInf_le_of_le x (iInf_le_of_le hx le_rfl)

/-- If every hole within graph-distance `r` is cleared, the nearest surviving hole is strictly
farther than `r`, i.e. `(r : ℕ∞) < holeDistance ω t`. -/
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
