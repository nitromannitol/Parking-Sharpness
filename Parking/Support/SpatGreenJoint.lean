/-
**The JOINT space-time two-point comparison of the truncated Green function**, combining
`Parking.Support.SpatGreenShift`/`Parking.Support.SpatGreenShiftLowDim` (the SPACE direction,
fixed horizon, `1 ≤ d ≤ 3`) and `Parking.Support.LinTimeShift` (the TIME
direction, fixed site, general `d`, already proved) by the two-term Minkowski inequality for
finitely-supported fields (`Parking.Support.SpatGreenShift.l2Norm_add_le_of_support`/
`supAbs_add_le_of_support`), via the triangle decomposition

    green d n (x - z) - green d m (y - z)
      = [green d n (x - z) - green d n (y - z)] + [green d n (y - z) - green d m (y - z)]

(SAME horizon `n` on the space term, SAME site `y` on the time term).  The RESCALING
(turning this UNSCALED lattice bound into an `IsKolmogorovProcess` hypothesis for the
rescaled, interpolated linear field) and the Kolmogorov exponent optimization are separate
steps that build on this bound: this module supplies only the unscaled joint comparison
itself, a self-contained building block for them.

No `External` beyond what `Parking.Support.SpatGreenShiftLowDim`'s own combined wrappers
already discharge (`GreenGradient` at `d = 2, 3`, proved; nothing at `d = 1`) is used.
-/
import Parking.Support.SpatGreenShiftLowDim
import Parking.Support.LinTimeShift

noncomputable section

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### A single box containing both the space-direction and the time-direction support -/

/-- **The time-direction difference vanishes outside a box around `y` of radius `n`**: both
`green d n (y - z)` and `green d m (y - z)` vanish once `z` is more than sup-distance `n`
(hence graph-distance `n`, since `n ≥ m`) from `y`. -/
theorem green_time_diff_eq_zero_of_notMem_box {n m : ℕ} (hmn : m ≤ n) {y : Site d}
    {z : Site d} (hz : z ∉ boxFinset y n) :
    green d n (y - z) - green d m (y - z) = 0 := by
  rw [mem_boxFinset_iff'] at hz
  have hgt : n < supNorm (y - z) := not_le.mp hz
  have hgtg : n < graphNorm (y - z) := lt_of_lt_of_le hgt (supNorm_le_graphNorm (y - z))
  rw [green_eq_zero_of_le hgtg.le, green_eq_zero_of_le (le_trans hmn hgtg.le)]
  ring

/-- **The space-direction difference (SAME horizon `n`), vanishes outside a box around `x`
of radius `n + graphNorm (x - y)`.**  A specialization of
`Parking.Support.SpatGreenShift.green_diff_eq_zero_of_notMem_box` at `a = x`, `b = y`,
`c = x`. -/
theorem green_space_diff_eq_zero_of_notMem_box {n : ℕ} {x y : Site d} {z : Site d}
    (hz : z ∉ boxFinset x (n + graphNorm (x - y))) :
    green d n (x - z) - green d n (y - z) = 0 := by
  refine green_diff_eq_zero_of_notMem_box (a := x) (b := y) (c := x) ?_ ?_ hz
  · rw [sub_self, supNorm_zero']; omega
  · have := supNorm_le_graphNorm (x - y); omega

/-- **The time-direction difference also vanishes outside the SAME box around `x`**, since
`y` itself is within graph-distance `graphNorm (x - y)` of `x`. -/
theorem green_time_diff_eq_zero_of_notMem_box' {n m : ℕ} (hmn : m ≤ n) {x y : Site d}
    {z : Site d} (hz : z ∉ boxFinset x (n + graphNorm (x - y))) :
    green d n (y - z) - green d m (y - z) = 0 := by
  refine green_time_diff_eq_zero_of_notMem_box hmn (n := n) (y := y) (z := z) ?_
  rw [mem_boxFinset_iff'] at hz ⊢
  intro hcontra
  refine hz ?_
  have hsplit : x - z = (x - y) + (y - z) := by abel
  have hadd : supNorm (x - z) ≤ supNorm (x - y) + supNorm (y - z) := by
    rw [hsplit]; exact supNorm_add_le' _ _
  have hxy : supNorm (x - y) ≤ graphNorm (x - y) := supNorm_le_graphNorm (x - y)
  omega

/-! ### The joint comparison -/

/-- **The joint space-time two-point `l2Norm` comparison, UNSCALED, general `d`.** -/
theorem exists_green_joint_l2_bound (hd1 : 1 ≤ d) (hd3 : d ≤ 3) :
    ∃ K : ℝ, 0 < K ∧ ∀ n m : ℕ, 1 ≤ m → m ≤ n → ∀ x y : Site d,
      l2Norm (fun z => green d n (x - z) - green d m (y - z))
        ≤ K * spatialStepRate d n * (graphNorm (x - y) : ℝ)
          + ((n : ℝ) - m) * Real.sqrt (LatticeProb.diagConst d / Real.sqrt (2 * m) ^ d) := by
  obtain ⟨K, hK, hspace⟩ := exists_green_space_shift_l2_bound_full hd1 hd3
  refine ⟨K, hK, fun n m hm hmn x y => ?_⟩
  set R : ℕ := n + graphNorm (x - y) with hRdef
  have hS1 : ∀ z ∉ boxFinset x R, green d n (x - z) - green d n (y - z) = 0 :=
    fun z hz => green_space_diff_eq_zero_of_notMem_box hz
  have hS2 : ∀ z ∉ boxFinset x R, green d n (y - z) - green d m (y - z) = 0 :=
    fun z hz => green_time_diff_eq_zero_of_notMem_box' hmn hz
  have heq : (fun z => (green d n (x - z) - green d n (y - z))
        + (green d n (y - z) - green d m (y - z)))
      = fun z => green d n (x - z) - green d m (y - z) := by
    funext z; ring
  have hcomb : l2Norm (fun z => green d n (x - z) - green d m (y - z))
      ≤ l2Norm (fun z => green d n (x - z) - green d n (y - z))
        + l2Norm (fun z => green d n (y - z) - green d m (y - z)) := by
    calc l2Norm (fun z => green d n (x - z) - green d m (y - z))
        = l2Norm (fun z => (green d n (x - z) - green d n (y - z))
            + (green d n (y - z) - green d m (y - z))) := by rw [heq]
      _ ≤ l2Norm (fun z => green d n (x - z) - green d n (y - z))
            + l2Norm (fun z => green d n (y - z) - green d m (y - z)) :=
          l2Norm_add_le_of_support hS1 hS2
  have hspaceTerm := hspace n (hm.trans hmn) x y
  have hd' : 0 < d := hd1
  have htimeTerm := exists_green_time_shift_l2_bound hd' hm hmn y
  calc l2Norm (fun z => green d n (x - z) - green d m (y - z))
      ≤ l2Norm (fun z => green d n (x - z) - green d n (y - z))
        + l2Norm (fun z => green d n (y - z) - green d m (y - z)) := hcomb
    _ ≤ K * spatialStepRate d n * (graphNorm (x - y) : ℝ)
        + ((n : ℝ) - m) * Real.sqrt (LatticeProb.diagConst d / Real.sqrt (2 * m) ^ d) :=
        add_le_add hspaceTerm htimeTerm

/-- **The joint space-time two-point `supAbs` comparison, UNSCALED, general `d`.** -/
theorem exists_green_joint_sup_bound (hd1 : 1 ≤ d) (hd3 : d ≤ 3) :
    ∃ K : ℝ, 0 < K ∧ ∀ n m : ℕ, 1 ≤ m → m ≤ n → ∀ x y : Site d,
      supAbs (fun z => green d n (x - z) - green d m (y - z))
        ≤ K * (graphNorm (x - y) : ℝ)
          + ((n : ℝ) - m) * (LatticeProb.diagConst d / Real.sqrt m ^ d) := by
  obtain ⟨K, hK, hspace⟩ := exists_green_space_shift_sup_bound_full hd1 hd3
  refine ⟨K, hK, fun n m hm hmn x y => ?_⟩
  set R : ℕ := n + graphNorm (x - y) with hRdef
  have hS1 : ∀ z ∉ boxFinset x R, green d n (x - z) - green d n (y - z) = 0 :=
    fun z hz => green_space_diff_eq_zero_of_notMem_box hz
  have hS2 : ∀ z ∉ boxFinset x R, green d n (y - z) - green d m (y - z) = 0 :=
    fun z hz => green_time_diff_eq_zero_of_notMem_box' hmn hz
  have heq : (fun z => (green d n (x - z) - green d n (y - z))
        + (green d n (y - z) - green d m (y - z)))
      = fun z => green d n (x - z) - green d m (y - z) := by
    funext z; ring
  have hcomb : supAbs (fun z => green d n (x - z) - green d m (y - z))
      ≤ supAbs (fun z => green d n (x - z) - green d n (y - z))
        + supAbs (fun z => green d n (y - z) - green d m (y - z)) := by
    calc supAbs (fun z => green d n (x - z) - green d m (y - z))
        = supAbs (fun z => (green d n (x - z) - green d n (y - z))
            + (green d n (y - z) - green d m (y - z))) := by rw [heq]
      _ ≤ supAbs (fun z => green d n (x - z) - green d n (y - z))
            + supAbs (fun z => green d n (y - z) - green d m (y - z)) :=
          supAbs_add_le_of_support hS1 hS2
  have hspaceTerm := hspace n (hm.trans hmn) x y
  have hd' : 0 < d := hd1
  have htimeTerm := exists_green_time_shift_sup_bound hd' hm hmn y
  calc supAbs (fun z => green d n (x - z) - green d m (y - z))
      ≤ supAbs (fun z => green d n (x - z) - green d n (y - z))
        + supAbs (fun z => green d n (y - z) - green d m (y - z)) := hcomb
    _ ≤ K * (graphNorm (x - y) : ℝ)
        + ((n : ℝ) - m) * (LatticeProb.diagConst d / Real.sqrt m ^ d) :=
        add_le_add hspaceTerm htimeTerm

end Parking

end
