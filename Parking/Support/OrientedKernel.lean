import Parking.Support.Oriented
import Parking.Support.KernelBridge

/-!
# The oriented kernel as a lattice kernel

The oriented kernel, its forward layer recursion and its divisible operator.
-/

open LatticeProb.Walk (kIter kOp)

noncomputable section
namespace Parking
open LatticeProb Finset
variable {d : ℕ}

/-- The map `i ↦ unit i` sending a coordinate to the corresponding standard basis site
is injective, since two equal sites agree at every coordinate. -/
theorem unit_injective : Function.Injective (unit : Fin d → Site d) := by
  intro i j h
  by_contra hij
  have h' := congrFun h i
  simp [unit, hij] at h'

/-- `orientedKern d y x` is nonnegative, being either `0` or `(d : ℝ)⁻¹`. -/
theorem orientedKern_nonneg (d : ℕ) (y x : Site d) : 0 ≤ orientedKern d y x := by
  unfold orientedKern
  split_ifs <;> positivity

/-- `orientedKern` is translation invariant: shifting both endpoints `y` and `x` by the
same `v` leaves the transition probability unchanged. -/
theorem orientedKern_shift (v y x : Site d) :
    orientedKern d (y + v) (x + v) = orientedKern d y x := by
  have he : (∃ i : Fin d, x + v = y + v - unit i) ↔
      ∃ i : Fin d, x = y - unit i := by
    simp only [add_sub_right_comm, add_left_inj]
  simp only [orientedKern, he]

/-- Convolving `f` against `orientedKern d x ·` on the unit box around `x` reduces to the
average of `f` over the `d` predecessors `x - unit i`, since `orientedKern d x y` is
nonzero exactly at those `y`. -/
theorem sum_orientedKern_mul (f : Site d → ℝ) (x : Site d) :
    (∑ y ∈ boxFinset x 1, orientedKern d x y * f y) =
      (∑ i : Fin d, f (x - unit i)) / d := by
  classical
  let s := univ.image fun i : Fin d => x - unit i
  have hs : s ⊆ boxFinset x 1 := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := mem_image.mp hy
    exact mem_boxFinset_one_of_nbr (mem_nbrFinset_sub x i)
  have hinj : Function.Injective fun i : Fin d => x - unit i := by
    intro i j hij
    exact unit_injective (sub_right_injective hij)
  rw [← sum_subset hs (fun y _ hy => ?_)]
  · change (∑ y ∈ univ.image (fun i : Fin d => x - unit i),
        orientedKern d x y * f y) = _
    rw [sum_image (fun i _ j _ hij => hinj hij)]
    have hv : ∀ i : Fin d, orientedKern d x (x - unit i) = (d : ℝ)⁻¹ := by
      intro i
      exact if_pos ⟨i, rfl⟩
    simp only [hv, ← mul_sum, div_eq_inv_mul]
  · have hne : ¬ ∃ i : Fin d, y = x - unit i := by
      rintro ⟨i, rfl⟩
      exact hy (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
    simp [orientedKern, hne]

/-- Convolving `f` against `orientedKern d · x` on the unit box around `x` reduces to the
average of `f` over the `d` successors `x + unit i`, since `orientedKern d y x` is
nonzero exactly at those `y`. -/
theorem sum_mul_orientedKern (f : Site d → ℝ) (x : Site d) :
    (∑ y ∈ boxFinset x 1, f y * orientedKern d y x) =
      (∑ i : Fin d, f (x + unit i)) / d := by
  classical
  let s := univ.image fun i : Fin d => x + unit i
  have hs : s ⊆ boxFinset x 1 := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := mem_image.mp hy
    exact mem_boxFinset_one_of_nbr (mem_nbrFinset_add x i)
  have hinj : Function.Injective fun i : Fin d => x + unit i := by
    intro i j hij
    exact unit_injective (add_left_cancel hij)
  rw [← sum_subset hs (fun y _ hy => ?_)]
  · change (∑ y ∈ univ.image (fun i : Fin d => x + unit i),
        f y * orientedKern d y x) = _
    rw [sum_image (fun i _ j _ hij => hinj hij)]
    have hv : ∀ i : Fin d, orientedKern d (x + unit i) x = (d : ℝ)⁻¹ := by
      intro i
      exact if_pos ⟨i, by simp⟩
    simp only [hv, ← sum_mul, div_eq_mul_inv]
  · have hne : ¬ ∃ i : Fin d, x = y - unit i := by
      rintro ⟨i, hi⟩
      exact hy (mem_image.mpr ⟨i, mem_univ _, (eq_add_of_sub_eq hi.symm).symm⟩)
    simp [orientedKern, hne]

/-- `orientedKern d` is a lattice kernel of range `1`: it is nonnegative, supported on the
unit box, sums to `1` from every site (using `sum_orientedKern_mul` at `f = 1`), and is
translation invariant. -/
theorem isLatticeKernel_oriented (hd : 1 ≤ d) : IsLatticeKernel 1 (orientedKern d) := by
  refine ⟨orientedKern_nonneg d, ?_, ?_, orientedKern_shift⟩
  · intro y x h
    have hm : x ∈ boxFinset y 1 := by
      have he : ∃ i : Fin d, x = y - unit i := by
        by_contra he
        exact h (by simp [orientedKern, he])
      obtain ⟨i, rfl⟩ := he
      exact mem_boxFinset_one_of_nbr (mem_nbrFinset_sub y i)
    refine Finset.sup_le fun i _ => ?_
    have hi := abs_le.mp (mem_boxFinset_iff.mp hm i)
    change (x i - y i).natAbs ≤ 1
    omega
  · intro y
    have he := sum_orientedKern_mul (fun _ : Site d => 1) y
    simpa [ne_of_gt (show (0 : ℝ) < d by exact_mod_cast hd)] using he

/-- The kernel operator `kOp 1 (orientedKern d)` agrees with `orientedOp`, since both
average `f` over the same `d` predecessors `x - unit i`. -/
theorem kOp_oriented (f : Site d → ℝ) (x : Site d) :
    kOp 1 (orientedKern d) f x = orientedOp f x :=
  sum_orientedKern_mul f x

/-- The kernel-driven divisible solution `kSol 1 (orientedKern d) η` agrees with
`uOriented η`, by induction on `n` using `kOp_oriented` to match the two recursions. -/
theorem kSol_oriented (η : Site d → ℝ) (n : ℕ) :
    kSol 1 (orientedKern d) η n = uOriented η n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    simp only [kSol, uOriented, ih, kOp_oriented]

/-- The kernel iterate `kIter 1 (orientedKern d) n` agrees with `orientedLayer d n`, by
induction on `n` unfolding both recursions. -/
theorem kIter_oriented (n : ℕ) : kIter 1 (orientedKern d) n = orientedLayer d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    simp only [kIter, orientedLayer, ih]

/-- The kernel Green function `kGreen 1 (orientedKern d) n` agrees with `orientedGreen d
n`, since `kGreen` and `orientedGreen` sum the same layers by `kIter_oriented`. -/
theorem kGreen_oriented (n : ℕ) : kGreen 1 (orientedKern d) n = orientedGreen d n := by
  funext x
  simp only [kGreen, orientedGreen, kIter_oriented]

/-- The layer recursion `orientedLayer d (n + 1) x` is the average of `orientedLayer d n`
over the `d` successors `x + unit i`, an instance of `sum_mul_orientedKern`. -/
theorem orientedLayer_succ (n : ℕ) (x : Site d) :
    orientedLayer d (n + 1) x = (∑ i : Fin d, orientedLayer d n (x + unit i)) / d :=
  sum_mul_orientedKern (orientedLayer d n) x

end Parking
