import Parking.Support.InstructionInfluence
import Parking.Support.MeanLocality

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

/-- Changing an unused entry has no effect on the signed field after a round. -/
theorem roundSigned_update_unused (A H : Site d → ℕ) (τ : RoundSlot d → Fin d × Bool)
    (v : Site d) (j : ℕ) (hj : A v ≤ j) (b : Fin d × Bool) :
    roundSigned A H (Function.update τ (Sum.inl (v, j)) b) = roundSigned A H τ := by
  classical
  funext x
  unfold roundSigned
  apply congrArg (fun s : Finset (RoundSlot d) => (s.card : ℤ) - H x)
  ext q
  cases q with
  | inr p => simp [countArrivals]
  | inl q =>
      rcases q with ⟨u, k⟩
      rw [mem_countArrivals, mem_countArrivals]
      by_cases he : (Sum.inl (u, k) : RoundSlot d) = Sum.inl (v, j)
      · cases Sum.inl_injective he
        simp [Nat.not_lt.mpr hj]
      · rw [Function.update_of_ne he]

/-- No possible destination of a sufficiently distant entry lies in the future propagation box. -/
theorem stepVec_notMem_box_of_far (x v : Site d) (T : ℕ)
    (hv : v ∉ boxFinset x (T + 1)) (b : Fin d × Bool) :
    v + stepVec b ∉ boxFinset x T := by
  intro h
  have hn : v ∈ boxFinset (v + stepVec b) 1 :=
    nbrFinset_subset_box _ (nbrFinset_symm (mem_nbrFinset_add_stepVec v b))
  exact hv (by simpa only [Nat.add_comm 1 T] using mem_boxFinset_add h hn)

/-- A distant current instruction has constant future mean, whether it is used or unused. -/
theorem instruction_future_of_far (A H : Site d → ℕ) (τ : RoundSlot d → Fin d × Bool)
    (v : Site d) (j : ℕ) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d)
    (hv : v ∉ boxFinset x (T + 1)) (b : Fin d × Bool) :
    matchedMeanU (roundSigned A H (Function.update τ (Sum.inl (v, j)) b)) ρ T x =
      matchedMeanU (roundSigned A H τ) ρ T x := by
  by_cases hj : j < A v
  · rw [roundSigned_eq_addParticle _ _ _ _ _ hj, Function.update_self,
      roundWithout_update, matchedMeanU_addParticle_of_far _ _ _ _ _ (stepVec_notMem_box_of_far x v T hv b),
      roundSigned_eq_addParticle _ _ _ _ _ hj,
      matchedMeanU_addParticle_of_far _ _ _ _ _ (stepVec_notMem_box_of_far x v T hv _)]
  · rw [roundSigned_update_unused _ _ _ _ _ (Nat.le_of_not_gt hj)]
end Parking
