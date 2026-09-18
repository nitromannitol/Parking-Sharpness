/-
The remaining-horizon reward field of the directed scaling limit
(`parking.tex:3192-3203`).

The Dynkin identity of `Parking.uOriented_eq_potential_add_stoppingSup` writes
the odometer of the horizon-`n` problem as the potential `Φ_n(0)` plus the
value of the optimal-stopping problem whose reward at the lattice point
`(k, z)` is `-Φ_{n-k}(z)`.  Read at the rescaled space-time point `(s,y)`
through the field site of `Parking.orientedFieldSite`, that reward is

  `G_n(s,y) = -n^{-1/4} Φ_{n-⌊ns⌋}(site n s y)`,

the *remaining-horizon* reward field.  This module builds that field as a
function of the scenery: its measurability, its values on the lattice of
rescaled grid points, and the `p`-th moment bound of its increments from the
scenery moment bound of `Parking.exists_oriented_potential_scenery_bound`.
-/
import Parking.Support.TightMoment

open MeasureTheory LatticeProb

noncomputable section
namespace Parking

/-- The remaining-horizon reward field at scale `n`: minus the rescaled
potential of the remaining horizon `n - ⌊ns⌋`, read at the field site of
`(s,y)`. -/
def orientedRewardField (n : ℕ) (s y : ℝ) (η : Site 2 → ℝ) : ℝ :=
  -(n : ℝ) ^ (-(1 : ℝ) / 4) *
    orientedPotential η (n - ⌊(n : ℝ) * s⌋₊) (orientedFieldSite n s y)

/-- **The reward field is measurable in the scenery.** -/
theorem measurable_orientedRewardField (n : ℕ) (s y : ℝ) :
    Measurable fun η : Site 2 → ℝ => orientedRewardField n s y η :=
  measurable_const.mul
    (measurable_orientedPotential (n - ⌊(n : ℝ) * s⌋₊) (orientedFieldSite n s y))

/-- **The `p`-th power of the absolute increment of the reward field** is the
prefactor `n^{-p/4}` times the `p`-th power of the absolute potential increment
over the remaining horizons. -/
theorem orientedRewardField_abs_sub_rpow (n : ℕ) (s y s' y' : ℝ) (p : ℝ)
    (η : Site 2 → ℝ) :
    |orientedRewardField n s y η - orientedRewardField n s' y' η| ^ p =
      ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ p *
        |orientedPotential η (n - ⌊(n : ℝ) * s⌋₊) (orientedFieldSite n s y) -
          orientedPotential η (n - ⌊(n : ℝ) * s'⌋₊) (orientedFieldSite n s' y')| ^ p := by
  have hc : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) := by positivity
  have hdiff : orientedRewardField n s y η - orientedRewardField n s' y' η =
      (n : ℝ) ^ (-(1 : ℝ) / 4) *
        (orientedPotential η (n - ⌊(n : ℝ) * s'⌋₊) (orientedFieldSite n s' y') -
          orientedPotential η (n - ⌊(n : ℝ) * s⌋₊) (orientedFieldSite n s y)) := by
    simp only [orientedRewardField]
    ring
  rw [hdiff, abs_mul, abs_of_nonneg hc, abs_sub_comm, Real.mul_rpow hc (abs_nonneg _)]

/-- **The prefactor of the `p`-th moment of the reward field increment.** -/
theorem orientedRewardField_integral_rpow_eq (n : ℕ) (s y s' y' : ℝ) (p : ℝ)
    (hp : 0 < p) (ν : Measure ℤ) :
    (∫ η : Site 2 → ℝ,
        |orientedRewardField n s y η - orientedRewardField n s' y' η| ^ p
      ∂(iidLaw 2 (realLaw ν))) ^ (2 / p) =
      (n : ℝ) ^ (-(1 : ℝ) / 2) *
        (∫ η : Site 2 → ℝ,
          |orientedPotential η (n - ⌊(n : ℝ) * s⌋₊) (orientedFieldSite n s y) -
            orientedPotential η (n - ⌊(n : ℝ) * s'⌋₊) (orientedFieldSite n s' y')| ^ p
        ∂(iidLaw 2 (realLaw ν))) ^ (2 / p) := by
  have hpt : ∀ η : Site 2 → ℝ,
      |orientedRewardField n s y η - orientedRewardField n s' y' η| ^ p
      = ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ p *
        |orientedPotential η (n - ⌊(n : ℝ) * s⌋₊) (orientedFieldSite n s y) -
          orientedPotential η (n - ⌊(n : ℝ) * s'⌋₊) (orientedFieldSite n s' y')| ^ p :=
    fun η => orientedRewardField_abs_sub_rpow n s y s' y' p η
  simp only [hpt]
  rw [integral_const_mul]
  rw [Real.mul_rpow (Real.rpow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) _)
    (integral_nonneg (fun η => Real.rpow_nonneg (abs_nonneg _) p))]
  congr 1
  rw [← Real.rpow_mul (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  rw [← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1
  have h2 : p * (2 / p) = 2 := by
    rw [mul_comm p (2 / p), div_mul_cancel₀ 2 (ne_of_gt hp)]
  rw [h2]
  norm_num

/-- **The increment moment of the reward field**: when the two space-time
points differ by `h` layers and layer coordinate `D`, the `p`-th moment of the
increment is bounded by the crossed scenery estimate. -/
theorem exists_orientedRewardField_moment_bound (ν : Measure ℤ) (hν : CriticalLaw ν)
    (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (s y s' y' : ℝ) (h : ℕ) (D : ℤ),
      ⌊(n : ℝ) * s'⌋₊ + h = ⌊(n : ℝ) * s⌋₊ →
      ⌊(n : ℝ) * s⌋₊ ≤ n →
      orientedFieldSite n s y = orientedFieldSite n s' y' + orientedLayerPoint h D →
      Integrable (fun η : Site 2 → ℝ => |orientedRewardField n s y η -
          orientedRewardField n s' y' η| ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedRewardField n s y η -
          orientedRewardField n s' y' η| ^ p ∂(iidLaw 2 (realLaw ν))) ^ (2 / p) ≤
        C * ((n : ℝ) ^ (-(1 : ℝ) / 2) * (Real.sqrt h + |(D : ℝ) - (h : ℝ) / 2|)) := by
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  have hp0 : (0 : ℝ) ≤ p := le_trans (by norm_num) hp
  have hpp : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp
  obtain ⟨C, hC, hb⟩ := exists_oriented_potential_scenery_bound (realLaw ν) p hp
    (integrable_rpow_realLaw ν hν p hp0) (realLaw_mean ν hν)
  refine ⟨C, hC, fun n s y s' y' h D hN hn hsite => ?_⟩
  have hle : ⌊(n : ℝ) * s'⌋₊ ≤ ⌊(n : ℝ) * s⌋₊ := hN ▸ Nat.le_add_right _ _
  have hhor : n - ⌊(n : ℝ) * s⌋₊ + h = n - ⌊(n : ℝ) * s'⌋₊ := by omega
  have hkey := hb (n - ⌊(n : ℝ) * s⌋₊) h D (orientedFieldSite n s' y')
  rw [hhor, ← hsite] at hkey
  have hkey2 : Integrable (fun η : Site 2 → ℝ =>
        |orientedPotential η (n - ⌊(n : ℝ) * s⌋₊) (orientedFieldSite n s y) -
          orientedPotential η (n - ⌊(n : ℝ) * s'⌋₊) (orientedFieldSite n s' y')| ^ p)
        (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ,
          |orientedPotential η (n - ⌊(n : ℝ) * s⌋₊) (orientedFieldSite n s y) -
            orientedPotential η (n - ⌊(n : ℝ) * s'⌋₊) (orientedFieldSite n s' y')| ^ p
        ∂(iidLaw 2 (realLaw ν))) ^ (2 / p) ≤
        C * (Real.sqrt h + |(D : ℝ) - (h : ℝ) / 2|) := by
    have hcongr : (fun η : Site 2 → ℝ =>
          |orientedPotential η (n - ⌊(n : ℝ) * s⌋₊) (orientedFieldSite n s y) -
            orientedPotential η (n - ⌊(n : ℝ) * s'⌋₊) (orientedFieldSite n s' y')| ^ p)
        = (fun η : Site 2 → ℝ =>
          |orientedPotential η (n - ⌊(n : ℝ) * s'⌋₊) (orientedFieldSite n s' y') -
            orientedPotential η (n - ⌊(n : ℝ) * s⌋₊) (orientedFieldSite n s y)| ^ p) := by
      funext η
      exact congr_arg (· ^ p) (abs_sub_comm _ _)
    refine ⟨hcongr ▸ hkey.1, ?_⟩
    rw [hcongr]
    exact hkey.2
  constructor
  · have h1 : Integrable (fun η : Site 2 → ℝ =>
        ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ p *
          |orientedPotential η (n - ⌊(n : ℝ) * s⌋₊) (orientedFieldSite n s y) -
            orientedPotential η (n - ⌊(n : ℝ) * s'⌋₊) (orientedFieldSite n s' y')| ^ p)
        (iidLaw 2 (realLaw ν)) := hkey2.1.const_mul _
    refine h1.congr ?_
    filter_upwards with η
    rw [orientedRewardField_abs_sub_rpow n s y s' y' p]
  · rw [orientedRewardField_integral_rpow_eq n s y s' y' p hpp ν]
    calc (n : ℝ) ^ (-(1 : ℝ) / 2) *
            (∫ η : Site 2 → ℝ,
              |orientedPotential η (n - ⌊(n : ℝ) * s⌋₊) (orientedFieldSite n s y) -
                orientedPotential η (n - ⌊(n : ℝ) * s'⌋₊) (orientedFieldSite n s' y')| ^ p
              ∂(iidLaw 2 (realLaw ν))) ^ (2 / p)
        ≤ (n : ℝ) ^ (-(1 : ℝ) / 2) * (C * (Real.sqrt h + |(D : ℝ) - (h : ℝ) / 2|)) :=
          mul_le_mul_of_nonneg_left hkey2.2 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = C * ((n : ℝ) ^ (-(1 : ℝ) / 2) * (Real.sqrt h + |(D : ℝ) - (h : ℝ) / 2|)) := by ring

/-- **The single-point moment of the reward field**: the `p`-th moment of the
field at one point is bounded by the square root of the remaining horizon. -/
theorem exists_orientedRewardField_single_moment (ν : Measure ℤ) (hν : CriticalLaw ν)
    (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (s y : ℝ), ⌊(n : ℝ) * s⌋₊ ≤ n →
      Integrable (fun η : Site 2 → ℝ => |orientedRewardField n s y η| ^ p)
        (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedRewardField n s y η| ^ p ∂(iidLaw 2 (realLaw ν))) ^ (2 / p) ≤
        C * ((n : ℝ) ^ (-(1 : ℝ) / 2) * (Real.sqrt (n - ⌊(n : ℝ) * s⌋₊) + 1 / 2)) := by
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  have hp0 : (0 : ℝ) ≤ p := le_trans (by norm_num) hp
  have hpp : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp
  obtain ⟨C, hC, hb⟩ := exists_oriented_potential_scenery_bound (realLaw ν) p hp
    (integrable_rpow_realLaw ν hν p hp0) (realLaw_mean ν hν)
  refine ⟨C, hC, fun n s y hn => ?_⟩
  set h : ℕ := n - ⌊(n : ℝ) * s⌋₊ with hh
  set D : ℤ := round ((h : ℝ) / 2) with hD
  have h0h : (0 : ℕ) + h = h := Nat.zero_add h
  have hpt : ∀ η : Site 2 → ℝ, |orientedRewardField n s y η| ^ p =
      ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ p * |orientedPotential η h (orientedFieldSite n s y)| ^ p := by
    intro η
    have hc : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) := by positivity
    have h1 : orientedRewardField n s y η =
        -(n : ℝ) ^ (-(1 : ℝ) / 4) * orientedPotential η h (orientedFieldSite n s y) := rfl
    rw [h1, abs_mul, abs_neg, abs_of_nonneg hc, Real.mul_rpow hc (abs_nonneg _)]
  have hkey := hb 0 h D (orientedFieldSite n s y)
  have hkey2 : Integrable (fun η : Site 2 → ℝ =>
        |orientedPotential η h (orientedFieldSite n s y)| ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedPotential η h (orientedFieldSite n s y)| ^ p
        ∂(iidLaw 2 (realLaw ν))) ^ (2 / p) ≤
        C * (Real.sqrt h + |(D : ℝ) - (h : ℝ) / 2|) := by
    have hcongr : (fun η : Site 2 → ℝ =>
          |orientedPotential η (0 + h) (orientedFieldSite n s y) -
            orientedPotential η 0 (orientedFieldSite n s y + orientedLayerPoint h D)| ^ p)
        = (fun η : Site 2 → ℝ =>
          |orientedPotential η h (orientedFieldSite n s y)| ^ p) := by
      funext η
      rw [zero_add, orientedPotential_zero, sub_zero]
    refine ⟨hcongr ▸ hkey.1, ?_⟩
    rw [← hcongr]
    exact hkey.2
  have hDbound : |(D : ℝ) - (h : ℝ) / 2| ≤ 1 / 2 := by
    rw [hD, abs_sub_comm]
    exact abs_sub_round ((h : ℝ) / 2)
  constructor
  · have h1 : Integrable (fun η : Site 2 → ℝ =>
        ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ p *
          |orientedPotential η h (orientedFieldSite n s y)| ^ p)
        (iidLaw 2 (realLaw ν)) := hkey2.1.const_mul _
    exact h1.congr (Filter.Eventually.of_forall fun η => (hpt η).symm)
  · have hpre : (∫ η : Site 2 → ℝ, |orientedRewardField n s y η| ^ p
        ∂(iidLaw 2 (realLaw ν))) ^ (2 / p) =
        (n : ℝ) ^ (-(1 : ℝ) / 2) *
          (∫ η : Site 2 → ℝ, |orientedPotential η h (orientedFieldSite n s y)| ^ p
            ∂(iidLaw 2 (realLaw ν))) ^ (2 / p) := by
      simp only [hpt]
      rw [integral_const_mul]
      rw [Real.mul_rpow (Real.rpow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) _)
        (integral_nonneg (fun η => Real.rpow_nonneg (abs_nonneg _) p))]
      congr 1
      rw [← Real.rpow_mul (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
      rw [← Real.rpow_mul (Nat.cast_nonneg n)]
      congr 1
      have h2 : p * (2 / p) = 2 := by
        rw [mul_comm p (2 / p), div_mul_cancel₀ 2 (ne_of_gt hpp)]
      rw [h2]
      norm_num
    rw [hpre]
    calc (n : ℝ) ^ (-(1 : ℝ) / 2) *
          (∫ η : Site 2 → ℝ, |orientedPotential η h (orientedFieldSite n s y)| ^ p
            ∂(iidLaw 2 (realLaw ν))) ^ (2 / p)
        ≤ (n : ℝ) ^ (-(1 : ℝ) / 2) * (C * (Real.sqrt h + |(D : ℝ) - (h : ℝ) / 2|)) :=
          mul_le_mul_of_nonneg_left hkey2.2 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ ≤ (n : ℝ) ^ (-(1 : ℝ) / 2) * (C * (Real.sqrt h + 1 / 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          refine mul_le_mul_of_nonneg_left ?_ hC.le
          simp only [add_le_add_iff_left]
          exact hDbound
      _ = C * ((n : ℝ) ^ (-(1 : ℝ) / 2) * (Real.sqrt (n - ⌊(n : ℝ) * s⌋₊) + 1 / 2)) := by
          rw [show (h : ℝ) = (n : ℝ) - (⌊(n : ℝ) * s⌋₊ : ℝ) by
            rw [hh]; exact Nat.cast_sub hn]
          ring

/-- **The grid value**: at the rescaled grid point `(k/n, (j - k/2)/√n)` the
reward field is minus the rescaled potential of the remaining horizon `n - k`
at the layer point `(k, j)`. -/
theorem orientedRewardField_grid (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (j : ℤ) (η : Site 2 → ℝ) :
    orientedRewardField n ((k : ℝ) / n) (((j : ℝ) - (k : ℝ) / 2) / Real.sqrt n) η =
      -(n : ℝ) ^ (-(1 : ℝ) / 4) * orientedPotential η (n - k) (orientedLayerPoint k j) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsqrt : Real.sqrt n ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (by omega))
  have h1 : (n : ℝ) * ((k : ℝ) / n) = (k : ℝ) := mul_div_cancel₀ (k : ℝ) hn0
  have h2 : Real.sqrt n * (((j : ℝ) - (k : ℝ) / 2) / Real.sqrt n) = (j : ℝ) - (k : ℝ) / 2 :=
    mul_div_cancel₀ ((j : ℝ) - (k : ℝ) / 2) hsqrt
  simp only [orientedRewardField, orientedFieldSite, h1, Nat.floor_natCast, h2]
  rw [show (k : ℝ) / 2 + ((j : ℝ) - (k : ℝ) / 2) = (j : ℝ) by ring, round_intCast]

/-- **The value at the origin**: the reward field at `(0,0)` is minus the
rescaled potential of the full horizon. -/
theorem orientedRewardField_zero_zero (n : ℕ) (η : Site 2 → ℝ) :
    orientedRewardField n 0 0 η =
      -(n : ℝ) ^ (-(1 : ℝ) / 4) * orientedPotential η n 0 := by
  have hlp : orientedLayerPoint 0 0 = (0 : Site 2) := by
    funext i
    fin_cases i <;> rfl
  simp only [orientedRewardField, orientedFieldSite, mul_zero, Nat.floor_zero, Nat.cast_zero,
    zero_div, zero_add, tsub_zero, round_zero, hlp]

end Parking
end
