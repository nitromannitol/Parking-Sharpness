/-
Counting the particles of a finite set of sites.

Step 2 of `lem:product` (`parking.tex:2367-2394`) sums a bound over the
particles present at a site and reads the result as `k` times the bound, `k`
being the count there.  Over finitely many sites the same sum is taken over the
canonical enumeration of the finite set of labels the sites carry, so the two
identities needed are that a sum over the enumeration is a sum over the set and
that a sum of a function of the SITE over those labels weights each site by its
count.
-/
import Parking.Support.ParticleFiltration

noncomputable section

namespace Parking

/-- A sum over the canonical enumeration of a finite set of labels is the sum
over the set. -/
theorem sum_range_equivFin {α : Type*} (s : Finset α) (h : α → ℝ) (e : ℕ → α)
    (he : ∀ (i : ℕ) (hi : i < s.card),
      e i = ((s.equivFin.symm ⟨i, hi⟩ : {x // x ∈ s}) : α)) :
    ∑ i ∈ Finset.range s.card, h (e i) = ∑ p ∈ s, h p := by
  classical
  have h1 : ∑ i ∈ Finset.range s.card, h (e i) = ∑ k : Fin s.card, h (e (k : ℕ)) :=
    (Fin.sum_univ_eq_sum_range (fun i => h (e i)) s.card).symm
  have h2 : ∀ k : Fin s.card,
      h (e (k : ℕ)) = h ((s.equivFin.symm k : {x // x ∈ s}) : α) := by
    intro k
    rw [he (k : ℕ) k.isLt]
  rw [h1, Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => h2 k),
    Equiv.sum_comp s.equivFin.symm (fun p : {x // x ∈ s} => h (p : α)),
    Finset.sum_coe_sort s h]

/-- Summing a function of the site over the particles present at the sites of
`N` weights each site by its count. -/
theorem sum_particleLabels {d : ℕ} (N : Finset (Site d)) (a : Site d → ℤ) (g : Site d → ℝ) :
    ∑ p ∈ particleLabels N a, g p.1 = ∑ x ∈ N, ((a x).toNat : ℝ) * g x := by
  classical
  have hdisj : (N : Set (Site d)).PairwiseDisjoint
      fun x => (Finset.range (a x).toNat).image fun i => ((x, i) : Label d) := by
    intro x hx y hy hxy
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image, Finset.mem_range]
    rintro p ⟨i, hi, rfl⟩ ⟨j, hj, hj2⟩
    exact hxy (congrArg Prod.fst hj2).symm
  rw [particleLabels, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.sum_image (fun i _ j _ hij => congrArg Prod.snd hij)]
  simp

end Parking

end
