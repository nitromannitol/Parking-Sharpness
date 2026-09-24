/- Taylor control of the signed-density middle term by the local odometer mass. -/
import Parking.Support.SpatWTaylor
import Parking.Support.SpatWSignedDecomp

open MeasureTheory LatticeProb Filter Topology

noncomputable section
namespace Parking

/-- The discrete operator in the signed-density decomposition can be replaced by the
continuum operator, with an error bounded by the cubic Taylor remainder times local mass. -/
theorem exists_signedMiddle_taylor_bound {d : ℕ} (hd : 1 ≤ d)
    {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, 0 < B →
      (∀ x : Fin d → ℝ, φ x ≠ 0 → ‖x‖ ≤ B) → ∀ R : ℝ, 1 ≤ R → ∀ w : Data d,
      |signedMiddle w R φ - R ^ (-(d : ℝ) / 2) *
        ∑ y ∈ boxFinset (0 : Site d) (⌈B * R⌉₊ + 1),
          (U w ⌊R ^ 2⌋₊ y : ℝ) * (contOp d φ (fun i => (y i : ℝ) / R) / R ^ 2)|
        ≤ R ^ (-(d : ℝ) / 2) * (C / R ^ 3) *
          ∑ y ∈ boxFinset (0 : Site d) (⌈B * R⌉₊ + 1), (U w ⌊R ^ 2⌋₊ y : ℝ) := by
  obtain ⟨C, hC, hTaylor⟩ := exists_walkOp_taylor_bound hd hφ
  refine ⟨C, hC, fun B hB hbound R hR w => ?_⟩
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let S := boxFinset (0 : Site d) (⌈B * R⌉₊ + 1)
  let a : Site d → ℝ := fun y => U w ⌊R ^ 2⌋₊ y
  let e : Site d → ℝ := fun y =>
    walkOp (fun z => φ (fun i => (z i : ℝ) / R)) y - φ (fun i => (y i : ℝ) / R)
      - contOp d φ (fun i => (y i : ℝ) / R) / R ^ 2
  have he : ∀ y, |e y| ≤ C / R ^ 3 := hTaylor R hRpos
  have ha : ∀ y, 0 ≤ a y := fun y => Nat.cast_nonneg _
  have hsum : |∑ y ∈ S, a y * e y| ≤ (C / R ^ 3) * ∑ y ∈ S, a y := by
    calc |∑ y ∈ S, a y * e y| ≤ ∑ y ∈ S, |a y * e y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y ∈ S, a y * (C / R ^ 3) := Finset.sum_le_sum fun y _ => by
        rw [abs_mul, abs_of_nonneg (ha y)]
        exact mul_le_mul_of_nonneg_left (he y) (ha y)
      _ = (C / R ^ 3) * ∑ y ∈ S, a y := by rw [← Finset.sum_mul, mul_comm]
  have hq : 0 ≤ R ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hRpos.le _
  rw [signedMiddle_eq_sceneryBox_sum hB hbound hR w, ← mul_sub, ← Finset.sum_sub_distrib]
  have heq : (∑ y ∈ S,
      ((U w ⌊R ^ 2⌋₊ y : ℝ) * (walkOp (fun z => φ (fun i => (z i : ℝ) / R)) y
        - φ (fun i => (y i : ℝ) / R)) -
      (U w ⌊R ^ 2⌋₊ y : ℝ) * (contOp d φ (fun i => (y i : ℝ) / R) / R ^ 2))) =
      ∑ y ∈ S, a y * e y := by
    apply Finset.sum_congr rfl
    intro y _
    dsimp [a, e]
    ring
  change |R ^ (-(d : ℝ) / 2) * _| ≤ _
  rw [show boxFinset (0 : Site d) (⌈B * R⌉₊ + 1) = S from rfl, heq,
    abs_mul, abs_of_nonneg hq]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum hq

end Parking
end
