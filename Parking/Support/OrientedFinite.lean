/- Finite support and measurable linear potentials for the oriented kernel. -/
import Parking.Support.OrientedPotential

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem orientedGreen_zero_outside {n : ℕ} {z : Site d} (hz : z ∉ boxFinset 0 n) :
    orientedGreen d n z = 0 := by
  apply sum_eq_zero
  intro l hl
  apply orientedLayer_eq_zero_of_notMem
  exact fun h => hz (boxFinset_mono (Nat.le_of_lt (mem_range.mp hl)) h)

theorem orientedGreen_sub_zero_outside {n : ℕ} {x z : Site d} (hz : z ∉ boxFinset x n) :
    orientedGreen d n (z - x) = 0 := by
  apply orientedGreen_zero_outside
  intro h
  apply hz
  simpa only [mem_boxFinset_iff, Pi.sub_apply, Pi.zero_apply, sub_zero] using h

theorem summable_orientedGreen_weight (n : ℕ) (x : Site d) (f : Site d → ℝ) :
    Summable fun z : Site d => orientedGreen d n (z - x) * f z := by
  refine summable_of_ne_finset_zero (s := boxFinset x n) fun z hz => ?_
  rw [orientedGreen_sub_zero_outside hz, zero_mul]

theorem orientedPotential_eq_green_sub (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    orientedPotential η n x = ∑' z : Site d, orientedGreen d n (z - x) * η z := by
  rw [orientedPotential_eq_green]
  have h := (Equiv.addRight x).tsum_eq (fun z : Site d => orientedGreen d n (z - x) * η z)
  simp only [Equiv.coe_addRight, add_sub_cancel_right] at h
  refine (tsum_congr fun z => ?_).trans h
  rw [add_comm x z]

theorem orientedPotential_eq_box (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    orientedPotential η n x = ∑ z ∈ boxFinset x n, orientedGreen d n (z - x) * η z := by
  rw [orientedPotential_eq_green_sub]
  exact tsum_eq_sum fun z hz => by rw [orientedGreen_sub_zero_outside hz, zero_mul]

theorem measurable_orientedPotential (n : ℕ) (x : Site d) :
    Measurable fun η : Site d → ℝ => orientedPotential η n x := by
  simp only [orientedPotential_eq_box]
  fun_prop

theorem measurable_uOriented (n : ℕ) (x : Site d) :
    Measurable fun η : Site d → ℝ => uOriented η n x := by
  induction n generalizing x with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [uOriented, orientedOp]
    exact measurable_const.max ((measurable_pi_apply x).add
      ((Finset.measurable_sum _ (fun i _ => ih (x - unit i))).div_const (d : ℝ)))

theorem orientedPotential_sub (η : Site d → ℝ) (n m : ℕ) (x y : Site d) :
    orientedPotential η n x - orientedPotential η m y =
      ∑' z : Site d, (orientedGreen d n (z - x) - orientedGreen d m (z - y)) * η z := by
  rw [orientedPotential_eq_green_sub, orientedPotential_eq_green_sub,
    ← (summable_orientedGreen_weight n x η).tsum_sub (summable_orientedGreen_weight m y η)]
  apply tsum_congr
  intro z
  ring

end Parking
