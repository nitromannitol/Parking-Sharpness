import Parking.Support.IsolatedHoles

/-!
# Measurability of the isolated-hole predicates

`measurable_activeSites_card`, `measurableSet_IsolatedHole`, `measurableSet_GoodHole`
and `measurableSet_mem_safeSites` show that the predicates of
`Parking.Support.IsolatedHoles` are all measurable, by expressing each as a finite or
countable Boolean combination of the measurable coordinate maps `A` and `H`.
-/

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The cardinality of `activeSites` is measurable, computed as a sum of measurable
0/1 indicators over `boxFinset y K`. -/
theorem measurable_activeSites_card (t K : ℕ) (y : Site d) :
    Measurable (fun ω : Data d => (activeSites ω t K y).card) := by
  classical
  simp only [activeSites, Finset.card_filter]
  apply Finset.measurable_sum
  intro a _
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_A t a))
    measurable_const measurable_const

/-- The event `IsolatedHole ω t K y` is measurable, as the intersection of the
measurable event `H · t y = 1` with a countable intersection over `z` of the
measurable complementary events at the other sites. -/
theorem measurableSet_IsolatedHole (t K : ℕ) (y : Site d) :
    MeasurableSet {ω : Data d | IsolatedHole ω t K y} := by
  simp only [IsolatedHole, Set.setOf_and, Set.setOf_forall]
  apply MeasurableSet.inter ((measurable_H t y) (measurableSet_singleton 1))
  apply MeasurableSet.iInter
  intro z
  apply MeasurableSet.iInter
  intro _
  apply MeasurableSet.iInter
  intro _
  exact ((measurable_H t z) (measurableSet_singleton 1)).compl

/-- `GoodHole` is measurable, combining `measurableSet_IsolatedHole` with the
measurable-cardinality bound from `measurable_activeSites_card`. -/
theorem measurableSet_GoodHole (t R : ℕ) (y : Site d) :
    MeasurableSet {ω : Data d | GoodHole ω t R y} :=
  (measurableSet_IsolatedHole t (4 * d * R) y).inter
    (measurableSet_le (measurable_activeSites_card t (2 * d * R) y) measurable_const)

/-- Membership in `safeSites` is measurable, as a finite intersection over the
active-site condition and the pointwise `Opposite` predicate. -/
theorem measurableSet_mem_safeSites (t R : ℕ) (y w : Site d) :
    MeasurableSet {ω : Data d | w ∈ safeSites ω t R y} := by
  simp only [mem_safeSites, Set.setOf_and, Set.setOf_forall]
  apply MeasurableSet.inter (MeasurableSet.const _)
  apply MeasurableSet.iInter
  intro a
  simp only [mem_activeSites]
  by_cases hO : Opposite y a w
  · simp only [hO, implies_true, Set.setOf_true]
    exact MeasurableSet.univ
  · simp only [hO, imp_false, not_and]
    by_cases hB : a ∈ boxFinset y (2 * d * R)
    · simp only [hB, true_implies]
      exact (measurableSet_lt measurable_const (measurable_A t a)).compl
    · simp only [hB, false_implies, Set.setOf_true]
      exact MeasurableSet.univ

end Parking
