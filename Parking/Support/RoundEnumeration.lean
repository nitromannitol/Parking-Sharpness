import Parking.Support.RoundBlock
import Parking.Support.RevealPrefix

noncomputable section
namespace Parking
open LatticeProb
variable {d : ℕ}

/-- The finite rectangle of sites and ranks queried in each round. -/
def roundEntrySet (x : Site d) (R N : ℕ) : Finset (Site d × ℕ) :=
  (boxFinset x R) ×ˢ Finset.range N

/-- A fixed enumeration of the finite rectangle of potential entries. -/
def roundEnumeration (x : Site d) (R N : ℕ) : Fin (roundEntrySet x R N).card ↪ Site d × ℕ :=
  ⟨fun i => ((roundEntrySet x R N).equivFin.symm i).val,
    fun _ _ h => (roundEntrySet x R N).equivFin.symm.injective (Subtype.ext h)⟩

theorem mem_roundEntrySet (x : Site d) (R N : ℕ) (v : Site d) (j : ℕ) :
    (v, j) ∈ roundEntrySet x R N ↔ v ∈ boxFinset x R ∧ j < N := by
  simp [roundEntrySet]

theorem roundEnumeration_mem (x : Site d) (R N : ℕ) (i : Fin (roundEntrySet x R N).card) :
    (roundEnumeration x R N i).1 ∈ boxFinset x R ∧ (roundEnumeration x R N i).2 < N := by
  have h := ((roundEntrySet x R N).equivFin.symm i).property
  exact (mem_roundEntrySet x R N _ _).mp h

theorem roundEnumeration_covers (x : Site d) (R N : ℕ) (v : Site d) (j : ℕ)
    (hv : v ∈ boxFinset x R) (hj : j < N) :
    ∃ i, roundEnumeration x R N i = (v, j) := by
  let q : roundEntrySet x R N := ⟨(v, j), (mem_roundEntrySet x R N v j).mpr ⟨hv, hj⟩⟩
  refine ⟨(roundEntrySet x R N).equivFin q, ?_⟩
  exact congrArg Subtype.val ((roundEntrySet x R N).equivFin.symm_apply_apply q)

theorem roundEntrySet_card_pos (x : Site d) (R N : ℕ) (hN : 0 < N) : 0 < (roundEntrySet x R N).card := by
  apply Finset.card_pos.mpr
  exact ⟨(x, 0), (mem_roundEntrySet x R N x 0).mpr
    ⟨mem_boxFinset_iff.mpr fun _ => by simp, hN⟩⟩
end Parking
