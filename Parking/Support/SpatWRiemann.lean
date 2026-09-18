/- Riemann discretization controlled by local rescaled odometer mass. -/
import Parking.Support.SpatWLocalMass
import Parking.Support.SpatialVanishingDistance
import Parking.Support.RiemannLattice

open MeasureTheory LatticeProb Filter Topology

noncomputable section
namespace Parking

variable {d : ℕ}

theorem barOdometer_mul_eq_sum_indicator (w : Data d) {R B : ℝ} (hR : 0 < R)
    {g : (Fin d → ℝ) → ℝ} (hbound : ∀ x, g x ≠ 0 → ‖x‖ ≤ B) (x : Fin d → ℝ) :
    barOdometer w R 1 x * g x = ∑ y ∈ boxFinset (0 : Site d) (⌈B * R⌉₊ + 1),
      (R ^ ((d : ℝ) / 2 - 2) * (U w ⌊R ^ 2⌋₊ y : ℝ)) *
        (latticeCube d y R).indicator g x := by
  classical
  have hmem : ∀ y : Site d, x ∈ latticeCube d y R ↔ y = latticePoint R x := by
    intro y
    rw [mem_latticeCube_iff hR]
    constructor
    · intro hy
      funext i
      exact (hy i).symm
    · intro hy
      subst y
      exact fun _ => rfl
  have hi : ∀ y : Site d, (latticeCube d y R).indicator g x =
      if y = latticePoint R x then g x else 0 := by
    intro y
    simp only [Set.indicator_apply, hmem]
  simp_rw [hi, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  by_cases hx : latticePoint R x ∈ boxFinset (0 : Site d) (⌈B * R⌉₊ + 1)
  · rw [if_pos hx]
    simp only [barOdometer, one_mul]
  · rw [if_neg hx]
    have hg : g x = 0 := by
      by_contra hne
      exact hx (latticePoint_mem_boxFinset hR.le fun i =>
        (norm_le_pi_norm x i).trans (hbound x hne))
    simp [hg]

theorem integral_barOdometer_mul_eq_sum (w : Data d) {R B : ℝ} (hR : 0 < R)
    {g : (Fin d → ℝ) → ℝ} (hg : Integrable g)
    (hbound : ∀ x, g x ≠ 0 → ‖x‖ ≤ B) :
    ∫ x, barOdometer w R 1 x * g x = ∑ y ∈ boxFinset (0 : Site d) (⌈B * R⌉₊ + 1),
      (R ^ ((d : ℝ) / 2 - 2) * (U w ⌊R ^ 2⌋₊ y : ℝ)) * ∫ x in latticeCube d y R, g x := by
  have hpoint := funext (barOdometer_mul_eq_sum_indicator w hR hbound)
  rw [hpoint, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro y _
    rw [integral_const_mul, integral_indicator (latticeCube_measurableSet y R)]
  · intro y _
    exact (hg.indicator (latticeCube_measurableSet y R)).const_mul _

theorem abs_barOdometer_riemann_error_le (w : Data d) {R B ε : ℝ} (hR : 0 < R)
    {g : (Fin d → ℝ) → ℝ} (hg : Integrable g)
    (hbound : ∀ x, g x ≠ 0 → ‖x‖ ≤ B)
    (hmod : ∀ x z, dist x z ≤ 1 / R → |g x - g z| ≤ ε) :
    |R ^ (-(d : ℝ) / 2 - 2) *
        ∑ y ∈ boxFinset (0 : Site d) (⌈B * R⌉₊ + 1),
          (U w ⌊R ^ 2⌋₊ y : ℝ) * g (fun i => (y i : ℝ) / R)
        - ∫ x, barOdometer w R 1 x * g x| ≤ ε * spatialLocalMass w R B := by
  classical
  let S := boxFinset (0 : Site d) (⌈B * R⌉₊ + 1)
  let A := R ^ ((d : ℝ) / 2 - 2)
  let V : ℝ := (1 / R) ^ d
  have hA : 0 ≤ A := Real.rpow_nonneg hR.le _
  have hvol : ∀ y, volume.real (latticeCube d y R) = V := by
    intro y
    rw [measureReal_def, volume_latticeCube y hR, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity)]
  have hscale : A * V = R ^ (-(d : ℝ) / 2 - 2) := by
    dsimp [A, V]
    rw [one_div, inv_pow, ← Real.rpow_natCast R d, ← Real.rpow_neg hR.le, ← Real.rpow_add hR]
    congr 1
    ring
  let e : Site d → ℝ := fun y => g (fun i => (y i : ℝ) / R) * V - ∫ x in latticeCube d y R, g x
  have he : ∀ y, |e y| ≤ ε * V := by
    intro y
    have hfinite : volume (latticeCube d y R) < ⊤ := by
      rw [volume_latticeCube y hR]
      exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
    have heq : e y = ∫ x in latticeCube d y R, (g (fun i => (y i : ℝ) / R) - g x) := by
      rw [integral_sub (integrableOn_const (C := g (fun i => (y i : ℝ) / R)) hfinite.ne) hg.integrableOn, setIntegral_const]
      dsimp [e]
      rw [hvol y, mul_comm V]
    rw [heq]
    have hn := norm_setIntegral_le_of_norm_le_const hfinite (f := fun x =>
      g (fun i => (y i : ℝ) / R) - g x) (C := ε) (fun x hx => ?_)
    · simpa [Real.norm_eq_abs, hvol y, mul_comm] using hn
    have hm := (mem_latticeCube_iff hR x).mp hx
    have hd : dist (fun i => (y i : ℝ) / R) x ≤ 1 / R := by
      apply (dist_pi_le_iff (by positivity)).2
      intro i
      rw [Real.dist_eq, ← hm i]
      exact abs_floor_mul_div_sub_le hR (x i)
    exact hmod _ _ hd
  have heq : R ^ (-(d : ℝ) / 2 - 2) *
      ∑ y ∈ S, (U w ⌊R ^ 2⌋₊ y : ℝ) * g (fun i => (y i : ℝ) / R)
      - ∫ x, barOdometer w R 1 x * g x =
      ∑ y ∈ S, (A * (U w ⌊R ^ 2⌋₊ y : ℝ)) * e y := by
    rw [integral_barOdometer_mul_eq_sum w hR hg hbound, ← hscale, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    dsimp [e, A]
    ring
  rw [heq]
  calc |∑ y ∈ S, (A * (U w ⌊R ^ 2⌋₊ y : ℝ)) * e y|
      ≤ ∑ y ∈ S, |(A * (U w ⌊R ^ 2⌋₊ y : ℝ)) * e y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ S, (A * (U w ⌊R ^ 2⌋₊ y : ℝ)) * (ε * V) := by
      apply Finset.sum_le_sum
      intro y _
      rw [abs_mul, abs_of_nonneg (mul_nonneg hA (Nat.cast_nonneg _))]
      exact mul_le_mul_of_nonneg_left (he y) (mul_nonneg hA (Nat.cast_nonneg _))
    _ = ε * spatialLocalMass w R B := by
      simp only [spatialLocalMass, ← hscale]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring

end Parking
end
