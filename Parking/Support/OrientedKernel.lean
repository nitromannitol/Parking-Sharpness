/- The oriented kernel, its forward layer recursion and its divisible operator. -/
import Parking.Support.Oriented
import Parking.Support.KernelBridge

noncomputable section
namespace Parking
open LatticeProb Finset
variable {d : ℕ}

theorem unit_injective : Function.Injective (unit : Fin d → Site d) := by
  intro i j h
  by_contra hij
  have h' := congrFun h i
  simp [unit, hij] at h'

theorem orientedKern_nonneg (d : ℕ) (y x : Site d) : 0 ≤ orientedKern d y x := by
  unfold orientedKern
  split_ifs <;> positivity

theorem orientedKern_shift (v y x : Site d) :
    orientedKern d (y + v) (x + v) = orientedKern d y x := by
  have he : (∃ i : Fin d, x + v = y + v - unit i) ↔
      ∃ i : Fin d, x = y - unit i := by
    simp only [add_sub_right_comm, add_left_inj]
  simp only [orientedKern, he]

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

theorem kOp_oriented (f : Site d → ℝ) (x : Site d) :
    kOp 1 (orientedKern d) f x = orientedOp f x :=
  sum_orientedKern_mul f x

theorem kSol_oriented (η : Site d → ℝ) (n : ℕ) :
    kSol 1 (orientedKern d) η n = uOriented η n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    simp only [kSol, uOriented, ih, kOp_oriented]

theorem kIter_oriented (n : ℕ) : kIter 1 (orientedKern d) n = orientedLayer d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    simp only [kIter, orientedLayer, ih]

theorem kGreen_oriented (n : ℕ) : kGreen 1 (orientedKern d) n = orientedGreen d n := by
  funext x
  simp only [kGreen, orientedGreen, kIter_oriented]

theorem orientedLayer_succ (n : ℕ) (x : Site d) :
    orientedLayer d (n + 1) x = (∑ i : Fin d, orientedLayer d n (x + unit i)) / d :=
  sum_mul_orientedKern (orientedLayer d n) x

end Parking
