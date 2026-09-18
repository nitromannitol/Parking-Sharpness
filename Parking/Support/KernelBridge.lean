/-
The simple random walk read as a lattice kernel.

`lem:u-concentration` is stated in `parking.tex` for an arbitrary finite-range
translation-invariant kernel `K`, and the frozen `Parking.External.UConcentration`
transcribes it that way.  Section 7 uses it with `K = P` and `v = u`, so what
`thm:upper` needs of the transcription is the identification of the general
objects with the ones of the model: the transition kernel of the walk is a
lattice kernel of range one, its operator is the walk operator, the recursion it
drives is the divisible sandpile odometer, and its truncated Green function is
`g_n`.
-/
import Parking.Support.Kernel
import Parking.Support.Pathwise
import Parking.Support.WBound

noncomputable section

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### The kernel of the walk -/

theorem kern_nonneg (d : ℕ) (y x : Site d) : 0 ≤ kern d y x := by
  rw [kern]
  by_cases h : x ∈ nbrFinset y
  · rw [if_pos h]; positivity
  · rw [if_neg h]

theorem kern_eq_zero_of_notMem {y x : Site d} (h : x ∉ nbrFinset y) : kern d y x = 0 := by
  rw [kern, if_neg h]

theorem nbrFinset_subset_box (x : Site d) : nbrFinset x ⊆ boxFinset x 1 :=
  fun _ h => mem_boxFinset_one_of_nbr h

theorem kern_shift (v y x : Site d) : kern d (y + v) (x + v) = kern d y x := by
  classical
  rw [kern, kern]
  by_cases h : x ∈ nbrFinset y
  · rw [if_pos h, if_pos ?_]
    rw [nbrFinset_add y v]
    exact Finset.mem_image.mpr ⟨x, h, rfl⟩
  · rw [if_neg h, if_neg ?_]
    intro hc
    rw [nbrFinset_add y v, Finset.mem_image] at hc
    obtain ⟨z, hz, hzv⟩ := hc
    exact h (by rwa [add_right_cancel hzv] at hz)

theorem isLatticeKernel_kern (hd : 1 ≤ d) : IsLatticeKernel 1 (kern d) := by
  classical
  refine ⟨kern_nonneg d, ?_, ?_, ?_⟩
  · intro y x hne
    by_contra hc
    exact hne (kern_eq_zero_of_notMem (fun hmem => hc (by
      have := mem_boxFinset_one_of_nbr hmem
      rw [LatticeProb.mem_boxFinset_iff] at this
      have hsup : supNorm (x - y) ≤ 1 := by
        refine Finset.sup_le fun i _ => ?_
        have hi := abs_le.mp (this i)
        have hval : (x - y) i = x i - y i := rfl
        rw [hval]
        omega
      exact hsup)))
  · intro y
    rw [← Finset.sum_subset (nbrFinset_subset_box y)
      (fun x _ hx => kern_eq_zero_of_notMem hx)]
    exact sum_kern_eq_one hd y
  · intro v y x
    exact kern_shift v y x

/-! ### The operator, the recursion and the Green function -/

theorem kOp_kern (f : Site d → ℝ) (x : Site d) :
    kOp 1 (kern d) f x = walkOp f x := by
  classical
  have hrestrict : ∑ y ∈ boxFinset x 1, kern d x y * f y
      = ∑ y ∈ nbrFinset x, kern d x y * f y := by
    refine (Finset.sum_subset (nbrFinset_subset_box x) fun y _ hy => ?_).symm
    rw [kern_eq_zero_of_notMem hy, zero_mul]
  have hval : ∀ y ∈ nbrFinset x, kern d x y * f y = (2 * (d : ℝ))⁻¹ * f y := by
    intro y hy
    rw [kern, if_pos hy]
  rw [kOp, hrestrict, Finset.sum_congr rfl hval, ← Finset.mul_sum,
    walkOp_eq_nbrFinset, div_eq_inv_mul]

theorem kSol_kern (η : Site d → ℝ) (n : ℕ) :
    kSol 1 (kern d) η n = u η n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext x
      have hL : kSol 1 (kern d) η (n + 1) x
          = max 0 (η x + kOp 1 (kern d) (kSol 1 (kern d) η n) x) := rfl
      have hR : u η (n + 1) x = max 0 (η x + walkOp (u η n) x) := rfl
      rw [hL, hR, ih, kOp_kern]

theorem kIter_kern (j : ℕ) : kIter 1 (kern d) j = heat d j := by
  classical
  induction j with
  | zero => rfl
  | succ j ih =>
      funext x
      have hL : kIter 1 (kern d) (j + 1) x
          = ∑ y ∈ boxFinset x 1, kIter 1 (kern d) j y * kern d y x := rfl
      have hR : heat d (j + 1) x = walkOp (heat d j) x := rfl
      rw [hL, hR, ih]
      have hrestrict : ∑ y ∈ boxFinset x 1, heat d j y * kern d y x
          = ∑ y ∈ nbrFinset x, heat d j y * kern d y x := by
        refine (Finset.sum_subset (nbrFinset_subset_box x) fun y _ hy => ?_).symm
        rw [kern_eq_zero_of_notMem (fun hc => hy (nbrFinset_symm hc)), mul_zero]
      have hval : ∀ y ∈ nbrFinset x, heat d j y * kern d y x
          = (2 * (d : ℝ))⁻¹ * heat d j y := by
        intro y hy
        rw [kern, if_pos (nbrFinset_symm hy)]
        ring
      rw [hrestrict, Finset.sum_congr rfl hval, ← Finset.mul_sum,
        walkOp_eq_nbrFinset, div_eq_inv_mul]

theorem kGreen_kern (n : ℕ) : kGreen 1 (kern d) n = green d n := by
  funext z
  rw [kGreen, green]
  exact Finset.sum_congr rfl fun j _ => congrFun (kIter_kern j) z

end Parking

end
