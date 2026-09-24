import Parking.Support.RevealPrefix

noncomputable section
namespace Parking

/-- Reindexing a finite sequence into equal chronological blocks. -/
theorem sum_range_blocks {α : Type*} [AddCommMonoid α] (T K : ℕ) (hK : 0 < K)
    (f : ℕ → Fin K → α) :
    (∑ n ∈ Finset.range (T * K), f (n / K) ⟨n % K, Nat.mod_lt n hK⟩) =
      ∑ s ∈ Finset.range T, ∑ j : Fin K, f s j := by
  rw [← Fin.sum_univ_eq_sum_range]
  have h := Equiv.sum_comp (finProdFinEquiv (m := T) (n := K))
    (fun n : Fin (T * K) => f (n.val / K) ⟨n.val % K, Nat.mod_lt n.val hK⟩)
  rw [← h, Fintype.sum_prod_type]
  have he (s : Fin T) (j : Fin K) :
      f ((finProdFinEquiv (s, j)).val / K)
          ⟨(finProdFinEquiv (s, j)).val % K, Nat.mod_lt _ hK⟩ = f s.val j := by
    have hpair := finProdFinEquiv.symm_apply_apply (s, j)
    rw [finProdFinEquiv_symm_apply] at hpair
    have hs := congrArg (fun p : Fin T × Fin K => p.1.val) hpair
    have hj := congrArg Prod.snd hpair
    exact congrArg₂ f hs hj
  simp_rw [he]
  exact Fin.sum_univ_eq_sum_range (fun s => ∑ j : Fin K, f s j) T

/-- Shifting a sum indexed from one to a sum indexed from zero. -/
theorem sum_Icc_one_eq_range_succ {α : Type*} [AddCommMonoid α] (f : ℕ → α) (k : ℕ) :
    ∑ n ∈ Finset.Icc 1 k, f n = ∑ n ∈ Finset.range k, f (n + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), Finset.sum_range_succ, ih]
end Parking
