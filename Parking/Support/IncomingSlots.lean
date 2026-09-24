import Parking.Support.RoundArrivalMean

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- All entries which could send a particle to the specified site in one round. -/
def incomingSlots (A : Site d → ℕ) (x : Site d) : Finset (RoundSlot d) :=
  (nbrFinset x).biUnion fun y => (Finset.range (A y)).image fun j => Sum.inl (y, j)

theorem mem_incomingSlots (A : Site d → ℕ) (x y : Site d) (j : ℕ) :
    Sum.inl (y, j) ∈ incomingSlots A x ↔ y ∈ nbrFinset x ∧ j < A y := by
  classical
  simp only [incomingSlots, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range,
    Sum.inl.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨z, hz, k, hk, rfl, rfl⟩
    exact ⟨hz, hk⟩
  · rintro ⟨hy, hj⟩
    exact ⟨y, hy, j, hj, rfl, rfl⟩

/-- Summation over incoming entries first sums over the neighboring sources and their ranks. -/
theorem sum_incomingSlots (A : Site d → ℕ) (x : Site d) (f : RoundSlot d → ℝ) :
    ∑ q ∈ incomingSlots A x, f q = ∑ y ∈ nbrFinset x, ∑ j ∈ Finset.range (A y), f (Sum.inl (y, j)) := by
  classical
  unfold incomingSlots
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro y _
    exact Finset.sum_image fun i _ j _ hij => congrArg Prod.snd (Sum.inl_injective hij)
  · intro y _ z _ hyz
    apply Finset.disjoint_left.mpr
    rintro q hq hq'
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hq
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hq'
    exact hyz (congrArg Prod.fst (Sum.inl_injective (hi.trans hj.symm)))

/-- Avoidance of a target by one table entry. -/
def entryAvoids (x : Site d) (q : RoundSlot d) (b : Fin d × Bool) : ℝ :=
  match q with
  | Sum.inl (y, _) => if y + stepVec b = x then 0 else 1
  | Sum.inr _ => 1

/-- No arriving entry is the product of the individual avoidance indicators. -/
theorem noArrivals_eq_prod (A : Site d → ℕ) (x : Site d) (τ : RoundSlot d → Fin d × Bool) :
    (if (countArrivals A τ x).card = 0 then (1 : ℝ) else 0) =
      ∏ q ∈ incomingSlots A x, entryAvoids x q (τ q) := by
  classical
  by_cases hz : (countArrivals A τ x).card = 0
  · rw [if_pos hz]
    symm
    apply Finset.prod_eq_one
    intro q hq
    obtain ⟨y, _hy, hq⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    have hn : y + stepVec (τ (Sum.inl (y, j))) ≠ x := by
      intro he
      have hm := (mem_countArrivals A τ x y j).mpr ⟨Finset.mem_range.mp hj, he⟩
      rw [Finset.card_eq_zero.mp hz] at hm
      exact Finset.notMem_empty _ hm
    exact if_neg hn
  · rw [if_neg hz]
    symm
    have hne : (countArrivals A τ x).Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
    obtain ⟨q, hq⟩ := hne
    obtain ⟨y, hy, hq⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    have hji := Finset.mem_filter.mp hj
    apply Finset.prod_eq_zero ((mem_incomingSlots A x y j).mpr ⟨hy, Finset.mem_range.mp hji.1⟩)
    exact if_pos hji.2
end Parking
