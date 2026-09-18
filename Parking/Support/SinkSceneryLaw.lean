import Parking.Support.PinnedSceneryFinite
import Parking.Support.SinkField
import LatticeProb.Prob.FiniteMarginal

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory LatticeProb
open scoped NNReal
variable {d : ℕ}

/-- Fixing a permanent sink preserves the uniform Gaussian bound for the conditional mean. -/
theorem exists_sparseSinkMeanU_subgaussian (hd : 5 ≤ d) :
    ∃ V : ℝ≥0, 0 < V ∧ ∀ (ν : Measure ℤ) [IsProbabilityMeasure ν] (T : ℕ) (v x : Site d),
      HasSubgaussianMGF (fun η : Site d → ℤ => matchedMeanU (sparseSinkField T v η) 0 T x -
        ∫ ζ, matchedMeanU (sparseSinkField T v ζ) 0 T x ∂(iidLaw d ν)) V (iidLaw d ν) := by
  classical
  obtain ⟨V, hV, hsg⟩ := exists_pinnedSparseBoxField_subgaussian hd
  refine ⟨V, hV, fun ν hν T v x => ?_⟩
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  let S := boxFinset x T
  let a : ℤ := -((T * (2 * T + 1) ^ d + 1 : ℕ) : ℤ)
  have ha : a ≤ 0 := by dsimp only [a]; omega
  let f : (S → ℤ) → ℝ := fun ξ => matchedMeanU (pinnedSparseBoxField S v a ξ) 0 T x
  have hf : Measurable f := measurable_from_countable' _
  have hR : Measurable (S.restrict : (Site d → ℤ) → S → ℤ) :=
    measurable_pi_lambda _ fun y => measurable_pi_apply y.val
  have hmap := iidLaw_map_restrict d ν S
  have he (η : Site d → ℤ) : f (S.restrict η) = matchedMeanU (sparseSinkField T v η) 0 T x := by
    apply matchedMeanU_agree_box
    intro y hy
    have hyS : y ∈ S := hy
    by_cases hyv : y = v
    · subst y
      simp only [pinnedSparseBoxField, sparseSinkField, horizonSink, Function.update_self]
      rfl
    · simp only [pinnedSparseBoxField, sparseSinkField, horizonSink, Function.update_of_ne hyv,
        sparseBoxField, dif_pos hyS, Finset.restrict, clippedField]
  have hm : (∫ ξ, f ξ ∂(Measure.pi (fun _ : S => ν))) =
      ∫ η, matchedMeanU (sparseSinkField T v η) 0 T x ∂(iidLaw d ν) := by
    rw [← hmap, integral_map hR.aemeasurable hf.aestronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ he)
  have hg : HasSubgaussianMGF (fun ξ : S → ℤ => f ξ - ∫ ζ, f ζ ∂(Measure.pi (fun _ : S => ν))) V
      ((iidLaw d ν).map S.restrict) := by
    rw [hmap]
    exact hsg ν S v a ha 0 T x
  apply (HasSubgaussianMGF.of_map hR.aemeasurable hg).congr
  exact ae_of_all _ fun η => by dsimp only [Function.comp_def]; rw [he η, hm]

/-- The sink scenery contribution has a square-root moment bound, uniformly in its capacity and location. -/
theorem exists_sparseSink_scenery_moment (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : Measure ℤ) [IsProbabilityMeasure ν] (T : ℕ) (v x : Site d) (r : ℝ), 2 ≤ r →
      rNorm (iidLaw d ν) r (fun η => matchedMeanU (sparseSinkField T v η) 0 T x -
        ∫ ζ, matchedMeanU (sparseSinkField T v ζ) 0 T x ∂(iidLaw d ν)) ≤ C * Real.sqrt r := by
  obtain ⟨V, _hV, hsg⟩ := exists_sparseSinkMeanU_subgaussian hd
  refine ⟨2 * Real.exp ((V : ℝ) / 2), by positivity, fun ν hν T v x r hr => ?_⟩
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  exact (subgaussian_rNorm_le _ _
    (((measurable_matchedMeanU (by omega) 0 T x).comp (measurable_sparseSinkField T v)).sub_const _)
    V (hsg ν T v x) r hr).2
end Parking
