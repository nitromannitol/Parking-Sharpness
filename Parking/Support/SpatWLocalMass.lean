/- First-moment control of the rescaled odometer mass in a fixed spatial box. -/
import Parking.Support.SpatWMartingaleVariance

open MeasureTheory LatticeProb Filter Topology

noncomputable section
namespace Parking

/-- The rescaled particle odometer mass in the lattice box covering a fixed continuum box. -/
def spatialLocalMass {d : ℕ} (w : Data d) (R B : ℝ) : ℝ :=
  R ^ (-(d : ℝ) / 2 - 2) *
    ∑ y ∈ boxFinset (0 : Site d) (⌈B * R⌉₊ + 1), (U w ⌊R ^ 2⌋₊ y : ℝ)

theorem spatialLocalMass_nonneg {d : ℕ} (w : Data d) {R : ℝ} (hR : 0 ≤ R) (B : ℝ) :
    0 ≤ spatialLocalMass w R B := by
  unfold spatialLocalMass
  positivity

theorem integrable_spatialLocalMass {d : ℕ} (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (R B : ℝ) : Integrable (fun w => spatialLocalMass w R B) (law d ν) := by
  haveI := hν.prob
  exact (integrable_finsetSum _ fun y _ =>
    integrable_U_law hd ν hν.integrable_abs ⌊R ^ 2⌋₊ y).const_mul _

/-- The growth theorem gives a uniform first moment for local rescaled odometer mass. -/
theorem exists_integral_spatialLocalMass_le {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : External.SandpileGrowth) (hBernstein : External.Bernstein)
    (hConcentration : External.UConcentration) (hGreenNorms : External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 2 ≤ R →
      ∫ w, spatialLocalMass w R B ∂law d ν ≤ C := by
  haveI := hν.prob
  obtain ⟨c, C, hc, hcC, hmean, _⟩ :=
    (Frozen.growth hGrowth hBernstein hConcentration hGreenNorms d hd ν hν).1 hd3
  have hC : 0 ≤ C := hc.le.trans hcC
  refine ⟨(2 * B + 5) ^ d * C, by positivity, fun R hR => ?_⟩
  have hRpos : 0 < R := by linarith
  have ht2 : 2 ≤ ⌊R ^ 2⌋₊ := (Nat.le_floor_iff (by positivity)).2 (by norm_num; nlinarith)
  have hI : ∀ y, Integrable (fun w : Data d => (U w ⌊R ^ 2⌋₊ y : ℝ)) (law d ν) :=
    fun y => integrable_U_law hd ν hν.integrable_abs _ y
  have heq : (∫ w, spatialLocalMass w R B ∂law d ν) =
      R ^ (-(d : ℝ) / 2 - 2) *
        ((boxFinset (0 : Site d) (⌈B * R⌉₊ + 1)).card : ℝ) * meanU (law d ν) ⌊R ^ 2⌋₊ := by
    unfold spatialLocalMass
    rw [integral_const_mul, integral_finsetSum _ (fun y _ => hI y)]
    simp_rw [meanU_shift_invariant hd ν]
    rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hpow : (⌊R ^ 2⌋₊ : ℝ) ^ ((4 - (d : ℝ)) / 4) ≤ R ^ ((4 - (d : ℝ)) / 2) := by
    have hexp : 0 ≤ (4 - (d : ℝ)) / 4 := by
      have hd' : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
      linarith
    calc (⌊R ^ 2⌋₊ : ℝ) ^ ((4 - (d : ℝ)) / 4)
        ≤ (R ^ 2) ^ ((4 - (d : ℝ)) / 4) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by positivity)) hexp
      _ = R ^ ((4 - (d : ℝ)) / 2) := by
        rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hRpos.le]
        congr 1
        push_cast
        ring
  have hm := ((hmean ⌊R ^ 2⌋₊ ht2).2).trans (mul_le_mul_of_nonneg_left hpow hC)
  have hcard := card_sceneryBox_le (d := d) hB (show 1 ≤ R by linarith)
  rw [heq]
  calc R ^ (-(d : ℝ) / 2 - 2) *
        ((boxFinset (0 : Site d) (⌈B * R⌉₊ + 1)).card : ℝ) * meanU (law d ν) ⌊R ^ 2⌋₊
      ≤ R ^ (-(d : ℝ) / 2 - 2) * ((2 * B + 5) ^ d * R ^ d) *
          (C * R ^ ((4 - (d : ℝ)) / 2)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hcard (Real.rpow_nonneg hRpos.le _)
        · exact hm
        · exact integral_nonneg fun w => Nat.cast_nonneg _
        · positivity
    _ = (2 * B + 5) ^ d * C := by
      rw [← Real.rpow_natCast R d]
      calc R ^ (-(d : ℝ) / 2 - 2) * ((2 * B + 5) ^ d * R ^ (d : ℝ)) *
            (C * R ^ ((4 - (d : ℝ)) / 2)) =
          ((2 * B + 5) ^ d * C) *
            (R ^ (-(d : ℝ) / 2 - 2) * R ^ (d : ℝ) * R ^ ((4 - (d : ℝ)) / 2)) := by ring
        _ = (2 * B + 5) ^ d * C := by
          rw [← Real.rpow_add hRpos, ← Real.rpow_add hRpos]
          ring_nf
          simp

end Parking
end
