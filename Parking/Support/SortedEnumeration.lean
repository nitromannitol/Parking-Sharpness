import Mathlib

/-!
# Sorted enumeration of a finite set

This file enumerates a finite set in increasing order of an integer-valued level
function, using `List.mergeSort` on the underlying list to produce a monotone bijection
from `Fin S.card` to `S`, and records that summing a function over this enumeration
recovers the sum over `S`.
-/

noncomputable section
namespace Parking
open scoped Classical

/-- A finite set `S` admits an injective enumeration `q : Fin S.card → ι` that hits every
element of `S` and is monotone with respect to an integer-valued level `h`, obtained by
merge-sorting `S.toList` on the total preorder induced by `h`. -/
theorem exists_sorted_enumeration {ι : Type*} (S : Finset ι) (h : ι → ℤ) :
    ∃ q : Fin S.card → ι, Function.Injective q ∧ (∀ x, x ∈ S ↔ ∃ j, q j = x) ∧
      Monotone (fun j => h (q j)) := by
  let r : ι → ι → Prop := fun x y => h x ≤ h y
  letI : IsTrans ι r := ⟨fun _ _ _ => le_trans⟩
  letI : Std.Total r := ⟨fun x y => le_total (h x) (h y)⟩
  letI : Std.Refl r := ⟨fun _ => le_rfl⟩
  let L := S.toList.mergeSort (fun x y => decide (r x y))
  have hp : L.Perm S.toList := List.mergeSort_perm _ _
  have hlen : L.length = S.card := hp.length_eq.trans S.length_toList
  have hnd : L.Nodup := hp.nodup_iff.mpr S.nodup_toList
  have hsorted : L.Pairwise r := List.pairwise_mergeSort' r S.toList
  let q : Fin S.card → ι := fun j => L.get (j.cast hlen.symm)
  refine ⟨q, ?_, ?_, ?_⟩
  · intro i j hij
    have he := hnd.injective_get hij
    exact Fin.ext (congrArg (fun k : Fin L.length => k.val) he)
  · intro x
    constructor
    · intro hx
      have hxL : x ∈ L := hp.mem_iff.mpr (S.mem_toList.mpr hx)
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hxL
      exact ⟨i.cast hlen, hi⟩
    · rintro ⟨j, rfl⟩
      exact S.mem_toList.mp (hp.mem_iff.mp (List.get_mem L _))
  · intro i j hij
    exact hsorted.rel_get_of_le hij

/-- Summing a function over an injective enumeration `q : Fin K → ι` that covers a finite
set `S` gives the same value as summing directly over `S`, by reindexing along the
bijection between `Fin K` and `S` that `q` and `hcov` exhibit. -/
theorem sum_enumeration {ι α : Type*} [AddCommMonoid α] {K : ℕ}
    (S : Finset ι) (q : Fin K → ι) (hq : Function.Injective q)
    (hcov : ∀ x, x ∈ S ↔ ∃ j, q j = x) (f : ι → α) :
    (∑ j : Fin K, f (q j)) = ∑ x ∈ S, f x := by
  apply Finset.sum_bij (fun j _ => q j)
  · exact fun j _ => (hcov (q j)).mpr ⟨j, rfl⟩
  · exact fun i _ j _ hij => hq hij
  · intro x hx
    obtain ⟨j, hj⟩ := (hcov x).mp hx
    exact ⟨j, Finset.mem_univ j, hj⟩
  · exact fun _ _ => rfl

end Parking
