import Parking.Support.OrientedPotential

/-!
# Finite support and measurability for the oriented kernel

Finite support and measurable linear potentials for the oriented kernel.
-/

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

/-- `orientedGreen d n` vanishes outside the box of radius `n` around the origin, since
each layer `orientedLayer d l` in the defining sum, for `l < n`, is supported inside that
box. -/
theorem orientedGreen_zero_outside {n : ℕ} {z : Site d} (hz : z ∉ boxFinset 0 n) :
    orientedGreen d n z = 0 := by
  apply sum_eq_zero
  intro l hl
  apply orientedLayer_eq_zero_of_notMem
  exact fun h => hz (boxFinset_mono (Nat.le_of_lt (mem_range.mp hl)) h)

/-- The shifted Green kernel `orientedGreen d n (z - x)` vanishes when `z` lies outside
the box of radius `n` around `x`, by translating `orientedGreen_zero_outside`. -/
theorem orientedGreen_sub_zero_outside {n : ℕ} {x z : Site d} (hz : z ∉ boxFinset x n) :
    orientedGreen d n (z - x) = 0 := by
  apply orientedGreen_zero_outside
  intro h
  apply hz
  simpa only [mem_boxFinset_iff, Pi.sub_apply, Pi.zero_apply, sub_zero] using h

/-- The kernel-weighted sum `∑ z, orientedGreen d n (z - x) * f z` is summable, since the
summand vanishes outside the finite box `boxFinset x n`
(`orientedGreen_sub_zero_outside`). -/
theorem summable_orientedGreen_weight (n : ℕ) (x : Site d) (f : Site d → ℝ) :
    Summable fun z : Site d => orientedGreen d n (z - x) * f z := by
  refine summable_of_ne_finset_zero (s := boxFinset x n) fun z hz => ?_
  rw [orientedGreen_sub_zero_outside hz, zero_mul]

/-- The potential `orientedPotential η n x` equals `∑' z, orientedGreen d n (z - x) * η z`,
obtained from `orientedPotential_eq_green` by re-indexing the sum along the translation
`z ↦ z + x`. -/
theorem orientedPotential_eq_green_sub (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    orientedPotential η n x = ∑' z : Site d, orientedGreen d n (z - x) * η z := by
  rw [orientedPotential_eq_green]
  have h := (Equiv.addRight x).tsum_eq (fun z : Site d => orientedGreen d n (z - x) * η z)
  simp only [Equiv.coe_addRight, add_sub_cancel_right] at h
  refine (tsum_congr fun z => ?_).trans h
  rw [add_comm x z]

/-- The potential is a finite sum over the box `boxFinset x n`, since the tail of the
`tsum` from `orientedPotential_eq_green_sub` vanishes there by
`orientedGreen_sub_zero_outside`. -/
theorem orientedPotential_eq_box (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    orientedPotential η n x = ∑ z ∈ boxFinset x n, orientedGreen d n (z - x) * η z := by
  rw [orientedPotential_eq_green_sub]
  exact tsum_eq_sum fun z hz => by rw [orientedGreen_sub_zero_outside hz, zero_mul]

/-- `η ↦ orientedPotential η n x` is measurable, since `orientedPotential_eq_box` writes it
as a finite sum of measurable coordinate evaluations. -/
theorem measurable_orientedPotential (n : ℕ) (x : Site d) :
    Measurable fun η : Site d → ℝ => orientedPotential η n x := by
  simp only [orientedPotential_eq_box]
  fun_prop

/-- `η ↦ uOriented η n x` is measurable, by induction on `n` using the
max-of-averaged-neighbors recursion defining `uOriented`. -/
theorem measurable_uOriented (n : ℕ) (x : Site d) :
    Measurable fun η : Site d → ℝ => uOriented η n x := by
  induction n generalizing x with
  | zero => exact measurable_const
  | succ n ih =>
    simp only [uOriented, orientedOp]
    exact measurable_const.max ((measurable_pi_apply x).add
      ((Finset.measurable_sum _ (fun i _ => ih (x - unit i))).div_const (d : ℝ)))

/-- The difference of two potentials, possibly at different horizons `n`, `m` and sites
`x`, `y`, is a single `tsum` of the difference of the two Green kernels weighted by `η`,
combining the summability of each weighted sum
(`summable_orientedGreen_weight`). -/
theorem orientedPotential_sub (η : Site d → ℝ) (n m : ℕ) (x y : Site d) :
    orientedPotential η n x - orientedPotential η m y =
      ∑' z : Site d, (orientedGreen d n (z - x) - orientedGreen d m (z - y)) * η z := by
  rw [orientedPotential_eq_green_sub, orientedPotential_eq_green_sub,
    ← (summable_orientedGreen_weight n x η).tsum_sub (summable_orientedGreen_weight m y η)]
  apply tsum_congr
  intro z
  ring

end Parking
