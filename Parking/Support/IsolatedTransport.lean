import Parking.Support.IsolatedMeasurable
import Parking.Support.IsolatedShift

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
open scoped Classical
variable {d : ℕ}

/-- Unit mass from an isolated hole to a nearby active site. -/
def isolatedActiveMass (ω : Data d) (t K : ℕ) (y a : Site d) : ℕ := by
  classical
  exact if IsolatedHole ω t (2 * K) y ∧ a ∈ activeSites ω t K y then 1 else 0

theorem isolatedActiveMass_eq (ω : Data d) (t K : ℕ) (y a : Site d) :
    isolatedActiveMass ω t K y a =
      if IsolatedHole ω t (2 * K) y ∧ a ∈ activeSites ω t K y then 1 else 0 := by
  classical
  rfl

theorem isolatedActiveMass_le_one (ω : Data d) (t K : ℕ) (y a : Site d) :
    isolatedActiveMass ω t K y a ≤ 1 := by
  classical
  rw [isolatedActiveMass_eq]
  split_ifs <;> omega

theorem isolatedActiveMass_shift (v : Site d) (ω : Data d) (t K : ℕ) (y a : Site d) :
    isolatedActiveMass (shiftData v ω) t K y a = isolatedActiveMass ω t K (y + v) (a + v) := by
  classical
  simp only [isolatedActiveMass_eq, IsolatedHole_shift, mem_activeSites_shift]

theorem measurable_isolatedActiveMass (t K : ℕ) (y a : Site d) :
    Measurable (fun ω : Data d => isolatedActiveMass ω t K y a) := by
  classical
  simp only [isolatedActiveMass_eq]
  refine Measurable.ite ((measurableSet_IsolatedHole t (2 * K) y).inter ?_) measurable_const measurable_const
  change MeasurableSet {ω : Data d | a ∈ activeSites ω t K y}
  simp_rw [mem_activeSites]
  simp only [Set.setOf_and]
  exact (MeasurableSet.const _).inter (measurableSet_lt measurable_const (measurable_A t a))

theorem isolatedActiveMass_out (ω : Data d) (t K : ℕ) :
    (∑ a ∈ boxFinset 0 K, isolatedActiveMass ω t K 0 a) =
      if IsolatedHole ω t (2 * K) 0 then (activeSites ω t K 0).card else 0 := by
  classical
  by_cases h : IsolatedHole ω t (2 * K) 0
  · simp only [h, if_true, isolatedActiveMass_eq, true_and]
    rw [activeSites, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Finset.mem_filter, ha, true_and]
  · simp only [isolatedActiveMass_eq, h, false_and, if_false, Finset.sum_const_zero]

theorem isolatedActiveMass_in (ω : Data d) (t K : ℕ) :
    (∑ y ∈ boxFinset 0 K, isolatedActiveMass ω t K y 0) ≤ A ω t 0 := by
  classical
  by_cases hA : 0 < A ω t 0
  · have hc : ((boxFinset (0 : Site d) K).filter fun y =>
        IsolatedHole ω t (2 * K) y ∧ 0 ∈ activeSites ω t K y).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro y hy z hz
      rcases (Finset.mem_filter.mp hy).2 with ⟨hyI, hyA⟩
      rcases (Finset.mem_filter.mp hz).2 with ⟨hzI, hzA⟩
      exact isolatedHole_unique hyI hzI (mem_activeSites.mp hyA).1 (mem_activeSites.mp hzA).1
    rw [Finset.card_filter] at hc
    have h1 : 1 ≤ A ω t 0 := hA
    simpa only [isolatedActiveMass_eq] using hc.trans h1
  · have he : ∀ y, isolatedActiveMass ω t K y 0 = 0 := by
      intro y
      simp only [isolatedActiveMass_eq, mem_activeSites, hA, and_false, if_false]
    simp only [he, Finset.sum_const_zero]
    exact Nat.zero_le _

end Parking
