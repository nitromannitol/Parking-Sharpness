import Parking.Support.IsolatedMeasurable
import Parking.Support.IndicatorIntegral

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
open scoped Classical
variable {d : ℕ}

theorem measure_hole_le_isolated_add_pairs (μ : Measure (Data d)) [IsFiniteMeasure μ] (t K : ℕ) :
    (μ {ω | H ω t 0 = 1}).toReal ≤ (μ {ω | IsolatedHole ω t K 0}).toReal +
      ∑ z ∈ (boxFinset (0 : Site d) K).erase 0, (μ {ω | H ω t 0 = 1 ∧ H ω t z = 1}).toReal := by
  let S := (boxFinset (0 : Site d) K).erase 0
  let I := fun ω : Data d => if H ω t 0 = 1 then (1 : ℝ) else 0
  let J := fun ω : Data d => if IsolatedHole ω t K 0 then (1 : ℝ) else 0
  let F := fun (ω : Data d) (z : Site d) => if H ω t 0 = 1 ∧ H ω t z = 1 then (1 : ℝ) else 0
  have hmI : MeasurableSet {ω : Data d | H ω t 0 = 1} := (measurable_H t 0) (measurableSet_singleton 1)
  have hmJ := measurableSet_IsolatedHole (d := d) t K 0
  have hmF (z : Site d) : MeasurableSet {ω : Data d | H ω t 0 = 1 ∧ H ω t z = 1} :=
    hmI.inter ((measurable_H t z) (measurableSet_singleton 1))
  have hiI : Integrable I μ := integrable_ite_one_zero μ _ hmI
  have hiJ : Integrable J μ := integrable_ite_one_zero μ _ hmJ
  have hiF (z : Site d) : Integrable (fun ω => F ω z) μ := integrable_ite_one_zero μ _ (hmF z)
  have hp : ∀ ω, I ω ≤ J ω + ∑ z ∈ S, F ω z := by
    intro ω
    have hn : 0 ≤ ∑ z ∈ S, F ω z := by
      apply Finset.sum_nonneg
      intro z _
      dsimp only [F]
      split_ifs <;> norm_num
    by_cases hH : H ω t 0 = 1
    · by_cases hJ : IsolatedHole ω t K 0
      · simp only [I, J, hH, hJ, if_true]
        linarith
      · have he : ∃ z ∈ boxFinset (0 : Site d) K, z ≠ 0 ∧ H ω t z = 1 := by
          have hnot : ¬ ∀ z ∈ boxFinset (0 : Site d) K, z ≠ 0 → H ω t z ≠ 1 := by
            intro hc
            exact hJ ⟨hH, hc⟩
          push Not at hnot
          exact hnot
        obtain ⟨z, hzB, hz0, hzH⟩ := he
        have hzS : z ∈ S := Finset.mem_erase.mpr ⟨hz0, hzB⟩
        have hs : F ω z ≤ ∑ a ∈ S, F ω a := Finset.single_le_sum
          (fun a _ => by dsimp only [F]; split_ifs <;> norm_num) hzS
        have hzF : F ω z = 1 := by simp only [F, hH, hzH, and_self, if_true]
        rw [hzF] at hs
        simpa only [I, J, hH, hJ, if_true, if_false, zero_add] using hs
    · have hJn : 0 ≤ J ω := by dsimp only [J]; split_ifs <;> norm_num
      simp only [I, hH, if_false]
      exact add_nonneg hJn hn
  have h := integral_mono hiI (hiJ.add (integrable_finsetSum S (fun z _ => hiF z))) hp
  change (∫ ω, I ω ∂μ) ≤ ∫ ω, J ω + ∑ z ∈ S, F ω z ∂μ at h
  rw [integral_add hiJ (integrable_finsetSum S (fun z _ => hiF z)), integral_finsetSum S (fun z _ => hiF z)] at h
  have hI : (∫ ω, I ω ∂μ) = (μ {ω | H ω t 0 = 1}).toReal := integral_ite_one_zero μ _ hmI
  have hJ : (∫ ω, J ω ∂μ) = (μ {ω | IsolatedHole ω t K 0}).toReal := integral_ite_one_zero μ _ hmJ
  have hF (z : Site d) : (∫ ω, F ω z ∂μ) = (μ {ω | H ω t 0 = 1 ∧ H ω t z = 1}).toReal := integral_ite_one_zero μ _ (hmF z)
  simpa only [hI, hJ, hF] using h

end Parking
