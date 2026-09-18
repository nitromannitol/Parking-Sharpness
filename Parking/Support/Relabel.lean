/-
The relabeling of the particles at a site: the group law of `relabelAt` and the
transpositions that a site with `k` particles admits.

`relabelAt x₀ σ` permutes, at the site `x₀` alone, the walks and the uniform
variables attached to the labels there.  A relabeling of the PARTICLES present
uses a permutation that fixes every index at or above the count at `x₀`, so at a
site with `k` particles the admissible permutations are exactly the permutations
of `{0, …, k-1}`, and the transposition of two particles is admissible.
-/
import Parking.Support.Range

noncomputable section

namespace Parking

/-- Relabeling by the identity does nothing. -/
theorem relabelAt_refl {d : ℕ} (x₀ : Site d) (ω : PData d) :
    relabelAt x₀ (Equiv.refl ℕ) ω = ω := by
  unfold relabelAt
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;>
    · funext q
      simp only [Equiv.refl_apply, ite_self, Prod.mk.eta]

/-- Relabeling twice at the same site composes the permutations. -/
theorem relabelAt_trans {d : ℕ} (x₀ : Site d) (σ τ : Equiv.Perm ℕ) (ω : PData d) :
    relabelAt x₀ σ (relabelAt x₀ τ ω) = relabelAt x₀ (σ.trans τ) ω := by
  unfold relabelAt
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;>
    · funext q
      by_cases h : q.1.1 = x₀
      · simp [h, Equiv.trans_apply]
      · simp [h]

/-- Relabeling does not change the counts, so the labels a site carries are the
same before and after. -/
theorem relabelAt_fst {d : ℕ} (x₀ : Site d) (σ : Equiv.Perm ℕ) (ω : PData d) :
    (relabelAt x₀ σ ω).1 = ω.1 := rfl

/-- A transposition of two particles present at a site is an admissible
relabeling: it fixes every index at or above the count. -/
theorem swap_apply_of_le {n i j : ℕ} (hi : i < n) (hj : j < n) :
    ∀ k : ℕ, n ≤ k → (Equiv.swap i j) k = k := by
  intro k hk
  have hik : k ≠ i := by omega
  have hjk : k ≠ j := by omega
  exact Equiv.swap_apply_of_ne_of_ne hik hjk

/-- Relabeling by a permutation and then by its inverse returns the
configuration. -/
theorem relabelAt_symm_apply {d : ℕ} (x₀ : Site d) (σ : Equiv.Perm ℕ) (ω : PData d) :
    relabelAt x₀ σ.symm (relabelAt x₀ σ ω) = ω := by
  rw [relabelAt_trans, Equiv.symm_trans_self, relabelAt_refl]

end Parking

end
