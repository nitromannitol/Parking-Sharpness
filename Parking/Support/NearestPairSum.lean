import Parking.Support.ThreeShellSum
import Parking.Support.TwoHoleShellBounds
import Parking.Support.HoleBounds

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The close, middle and far two-hole estimates give a finite isolation bound. -/
theorem nearest_pair_sum_bound (hd : 5 ≤ d) {p C : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4)
    (hC : 0 < C) (t R L M : ℕ)
    (hTwo : ∀ z : Site d, z ≠ 0 →
      ((law d (threePointLaw p)) {ω | H ω t 0 = 1 ∧ H ω t z = 1}).toReal ≤
        C * holeProb d (threePointLaw p) t ^ 2 * Real.exp (C * Real.log (1 / holeProb d (threePointLaw p) t) *
          (1 + (graphNorm z : ℝ)) ^ (4 - (d : ℝ))))
    (hL : C * (1 + (L : ℝ)) ^ (4 - (d : ℝ)) ≤ 1 / 4)
    (hM : C * Real.log (1 / holeProb d (threePointLaw p) t) * (1 + (M : ℝ)) ^ (4 - (d : ℝ)) ≤ 1) :
    (∑ z ∈ (boxFinset (0 : Site d) (4 * d * R)).erase 0,
      ((law d (threePointLaw p)) {ω | H ω t 0 = 1 ∧ H ω t z = 1}).toReal) ≤
        ((2 * L + 1 : ℕ) : ℝ) ^ d * (2 * p * holeProb d (threePointLaw p) t) +
        ((2 * M + 1 : ℕ) : ℝ) ^ d * (C * holeProb d (threePointLaw p) t ^ (7 / 4 : ℝ)) +
        ((8 * d * R + 1 : ℕ) : ℝ) ^ d * (C * Real.exp 1 * holeProb d (threePointLaw p) t ^ 2) := by
  have hd1 : 1 ≤ d := by omega
  let h := holeProb d (threePointLaw p) t
  let S := (boxFinset (0 : Site d) (4 * d * R)).erase 0
  let f := fun z : Site d => ((law d (threePointLaw p)) {ω | H ω t 0 = 1 ∧ H ω t z = 1}).toReal
  have hh : 0 < h := holeProb_pos hd1 hp hp4 t
  have hh1 : h ≤ 1 := (holeProb_le_p hd1 hp hp4 t).trans (by linarith)
  have hlog : 0 ≤ Real.log (1 / h) := Real.log_nonneg (by apply (le_div_iff₀ hh).mpr; simpa using hh1)
  have hsum := sum_three_shell_le S f L M (2 * p * h) (C * h ^ (7 / 4 : ℝ)) (C * Real.exp 1 * h ^ 2)
    (by positivity) (by positivity) (by positivity)
    (fun z hz _ => close_pair hd1 hp hp4 t 0 z (Ne.symm (Finset.mem_erase.mp hz).1))
    (fun z hz hzL _ => (hTwo z (Finset.mem_erase.mp hz).1).trans
      (twoHole_middle_bound hC.le hh hh1
        ((mul_le_mul_of_nonneg_left (twoHole_coefficient_antitone hd hzL) hC.le).trans hL)))
    (fun z hz _ hzM => ?_)
  · have hcard : (S.card : ℝ) ≤ ((8 * d * R + 1 : ℕ) : ℝ) ^ d := by
      have hc : S.card ≤ (boxFinset (0 : Site d) (4 * d * R)).card :=
        Finset.card_le_card (Finset.erase_subset _ _)
      rw [card_boxFinset] at hc
      have he : 2 * (4 * d * R) + 1 = 8 * d * R + 1 := by ring
      rw [he] at hc
      exact_mod_cast hc
    exact hsum.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard (by positivity)))
  · have hq := mul_le_mul_of_nonneg_left (twoHole_coefficient_antitone hd hzM) (mul_nonneg hC.le hlog)
    have he : C * Real.log (1 / h) * (1 + (graphNorm z : ℝ)) ^ (4 - (d : ℝ)) ≤ 1 := hq.trans hM
    calc f z
      ≤ C * h ^ 2 * Real.exp (C * Real.log (1 / h) * (1 + (graphNorm z : ℝ)) ^ (4 - (d : ℝ))) := hTwo z (Finset.mem_erase.mp hz).1
      _ ≤ C * h ^ 2 * Real.exp 1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
      _ = C * Real.exp 1 * h ^ 2 := by ring

end Parking
