/-
The measurable positive event used at `parking.tex:1818-1833`.
Its complement bounds the probability that a hole is closer than an active
particle. The test function needs only nonnegative values and bounded support
for this implication.
-/
import Parking.Support.NearestGeometry

noncomputable section
open MeasureTheory LatticeProb Filter Topology

theorem Parking.measurableSet_positive_U_ball {d : ℕ} (t : ℕ) (r : ℝ) :
    MeasurableSet {ω : Parking.Data d | ∀ y : Parking.Site d,
      (Parking.graphNorm y : ℝ) ≤ r → 0 < Parking.U ω t y} := by
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun y => MeasurableSet.iInter fun _ =>
    measurableSet_lt measurable_const (Parking.measurable_U t y)

theorem Parking.measureReal_le_one_sub_of_disjoint {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E G : Set Ω) (hG : MeasurableSet G)
    (hEG : Disjoint E G) : (μ E).toReal ≤ 1 - (μ G).toReal := by
  have hs : E ⊆ Gᶜ := fun _ he hg => Set.disjoint_left.mp hEG he hg
  have hm := measureReal_mono (μ := μ) hs
  rw [probReal_compl_eq_one_sub hG] at hm
  exact hm

theorem Parking.measurable_signedPair {d : ℕ} (R : ℝ) (φ : (Fin d → ℝ) → ℝ) :
    Measurable (fun ω : Parking.Data d => Parking.signedPair ω R φ) := by
  unfold Parking.signedPair
  apply Measurable.const_mul
  apply Measurable.tsum
  intro y
  exact ((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (Parking.measurable_A _ y)).sub
      ((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (Parking.measurable_H _ y)) |>.mul_const _

theorem Parking.measurableSet_active_ball {d : ℕ} (t : ℕ) (r : ℝ) :
    MeasurableSet {ω : Parking.Data d | ∃ y : Parking.Site d,
      (Parking.graphNorm y : ℝ) ≤ r ∧ 0 < Parking.A ω t y} := by
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro y
  by_cases hy : (Parking.graphNorm y : ℝ) ≤ r
  · simpa only [hy, true_and] using measurableSet_lt measurable_const (Parking.measurable_A t y)
  · simp only [hy, false_and, Set.setOf_false]
    exact MeasurableSet.empty

theorem Parking.measureReal_le_two_errors {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E B C : Set Ω) (h : E ⊆ B ∪ C) :
    (μ E).toReal ≤ (μ B).toReal + (μ C).toReal := by
  exact (measureReal_mono (μ := μ) h).trans (measureReal_union_le B C)

def Parking.PositiveTestEvent {d : ℕ} (R r : ℝ) (φ : (Fin d → ℝ) → ℝ) : Set (Parking.Data d) :=
  {ω | (∀ y : Parking.Site d, (Parking.graphNorm y : ℝ) ≤ r * R → 0 < Parking.U ω ⌊R ^ 2⌋₊ y) ∧
    0 < Parking.signedPair ω R φ}

theorem Parking.measurableSet_PositiveTestEvent {d : ℕ} (R r : ℝ)
    (φ : (Fin d → ℝ) → ℝ) : MeasurableSet (Parking.PositiveTestEvent R r φ) := by
  exact (Parking.measurableSet_positive_U_ball ⌊R ^ 2⌋₊ (r * R)).inter
    (measurableSet_lt measurable_const (Parking.measurable_signedPair R φ))

theorem Parking.not_HoleCloser_of_PositiveTestEvent {d : ℕ} (ω : Parking.Data d) {R r : ℝ}
    (hR : 0 < R) (φ : (Fin d → ℝ) → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (hsupp : ∀ x, 0 < φ x → (∑ i : Fin d, |x i|) ≤ r)
    (hω : ω ∈ Parking.PositiveTestEvent R r φ) : ¬ Parking.HoleCloser ω ⌊R ^ 2⌋₊ := by
  exact Parking.not_HoleCloser_of_signedPair_pos ω hR φ hφ hsupp
    (fun y hy => Parking.H_eq_zero_of_U_pos ω _ y (hω.1 y hy)) hω.2

theorem Parking.nearest_probability_le_complement {d : ℕ} (μ : Measure (Parking.Data d))
    [IsProbabilityMeasure μ] {R r : ℝ} (hR : 0 < R) (φ : (Fin d → ℝ) → ℝ)
    (hφ : ∀ x, 0 ≤ φ x) (hsupp : ∀ x, 0 < φ x → (∑ i : Fin d, |x i|) ≤ r) :
    (μ {ω | Parking.HoleCloser ω ⌊R ^ 2⌋₊}).toReal ≤
      1 - (μ (Parking.PositiveTestEvent R r φ)).toReal := by
  apply Parking.measureReal_le_one_sub_of_disjoint μ _ _
    (Parking.measurableSet_PositiveTestEvent R r φ)
  exact Set.disjoint_left.mpr fun ω hω hg =>
    Parking.not_HoleCloser_of_PositiveTestEvent ω hR φ hφ hsupp hg hω

end
