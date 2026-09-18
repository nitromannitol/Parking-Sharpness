import Parking.Support.Measurability
import LatticeProb.Walk.SRW

noncomputable section
namespace Parking
open MeasureTheory
variable {d : ℕ}

/-- Strict comparison of the two distances at an arbitrary site. -/
def CloserAt (ω : Data d) (t : ℕ) (w : Site d) : Prop :=
  ∃ y : Site d, 0 < H ω t y ∧ ∀ a : Site d, 0 < A ω t a →
    graphNorm (w - y) < graphNorm (w - a)

theorem HoleCloser_iff (ω : Data d) (t : ℕ) : HoleCloser ω t ↔ CloserAt ω t 0 := by
  unfold HoleCloser holeDistance activeDistance CloserAt
  constructor
  · intro h
    obtain ⟨y, hy⟩ := iInf_lt_iff.mp h
    obtain ⟨hyH, hy⟩ := iInf_lt_iff.mp hy
    refine ⟨y, hyH, fun a ha => ?_⟩
    have hya := hy.trans_le (iInf_le_of_le a (iInf_le_of_le ha le_rfl))
    have hr : graphNorm y < graphNorm a := by exact_mod_cast hya
    simpa [graphNorm] using hr
  · rintro ⟨y, hy, hya⟩
    have hle : ((graphNorm y + 1 : ℕ) : ℕ∞) ≤
        ⨅ a ∈ {a | 0 < A ω t a}, (graphNorm a : ℕ∞) := by
      apply le_iInf
      intro a
      apply le_iInf
      intro ha
      have hr : graphNorm y < graphNorm a := by simpa [graphNorm] using hya a ha
      exact_mod_cast (Nat.succ_le_of_lt hr)
    have hm : (⨅ x ∈ {x | 0 < H ω t x}, (graphNorm x : ℕ∞)) ≤ (graphNorm y : ℕ∞) :=
      iInf_le_of_le y (iInf_le_of_le hy le_rfl)
    apply lt_of_le_of_lt hm
    apply lt_of_lt_of_le _ hle
    exact_mod_cast (Nat.lt_succ_self (graphNorm y))

theorem measurableSet_CloserAt (t : ℕ) (w : Site d) :
    MeasurableSet {ω : Data d | CloserAt ω t w} := by
  simp only [CloserAt, Set.setOf_exists, Set.setOf_and, Set.setOf_forall]
  apply MeasurableSet.iUnion
  intro y
  apply MeasurableSet.inter (measurableSet_lt measurable_const (measurable_H t y))
  apply MeasurableSet.iInter
  intro a
  by_cases h : graphNorm (w - y) < graphNorm (w - a)
  · simp only [h, implies_true, Set.setOf_true]
    exact MeasurableSet.univ
  · simp only [h, imp_false]
    exact (measurableSet_lt measurable_const (measurable_A t a)).compl

theorem measurableSet_HoleCloser (t : ℕ) :
    MeasurableSet {ω : Data d | HoleCloser ω t} := by
  simp only [HoleCloser_iff]
  exact measurableSet_CloserAt t 0

end Parking
