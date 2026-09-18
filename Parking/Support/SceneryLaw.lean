import Parking.Support.SceneryFinite
import Parking.Support.SparseLaw
import LatticeProb.Prob.FiniteMarginal

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory LatticeProb
open scoped NNReal
variable {d : ℕ}

/-- Clipping has no effect under the three-point law. -/
theorem ae_clipSparse_threePointLaw (p : ℝ) : ∀ᵐ k ∂(threePointLaw p), clipSparse k = k := by
  rw [ae_iff_of_countable]
  intro k hk
  by_cases h1 : k = 1
  · subst k; exact clipSparse_eq (by norm_num)
  by_cases hm : k = -1
  · subst k; exact clipSparse_eq (by norm_num)
  by_cases h0 : k = 0
  · subst k; exact clipSparse_eq (by norm_num)
  have hz : threePointLaw p {k} = 0 := by simp [threePointLaw, Ne.symm h1, Ne.symm hm, Ne.symm h0]
  exact False.elim (hk hz)

/-- The finite-box Gaussian bound transfers to the conditional mean in the infinite field. -/
theorem exists_matchedMeanU_subgaussian (hd : 5 ≤ d) :
    ∃ V : ℝ≥0, 0 < V ∧ ∀ (ν : Measure ℤ) [IsProbabilityMeasure ν],
      (∀ᵐ k ∂ν, clipSparse k = k) → ∀ (T : ℕ) (x : Site d),
      HasSubgaussianMGF (fun η : Site d → ℤ => matchedMeanU η 0 T x -
        ∫ ζ, matchedMeanU ζ 0 T x ∂(iidLaw d ν)) V (iidLaw d ν) := by
  classical
  obtain ⟨V, hV, hsg⟩ := exists_sparseBoxField_subgaussian hd
  refine ⟨V, hV, fun ν hν hclip T x => ?_⟩
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  let S := boxFinset x T
  let f : (S → ℤ) → ℝ := fun ξ => matchedMeanU (sparseBoxField S ξ) 0 T x
  have hf : Measurable f := measurable_from_countable' _
  have hR : Measurable (S.restrict : (Site d → ℤ) → S → ℤ) :=
    measurable_pi_lambda _ fun y => measurable_pi_apply y.val
  have hmap := iidLaw_map_restrict d ν S
  have ha : ∀ᵐ η ∂(iidLaw d ν), ∀ y, clipSparse (η y) = η y := by
    apply ae_all_iff.mpr
    intro y
    exact (measurePreserving_eval_infinitePi (fun _ : Site d => ν) y).quasiMeasurePreserving.ae hclip
  have he : ∀ᵐ η ∂(iidLaw d ν), f (S.restrict η) = matchedMeanU η 0 T x := by
    filter_upwards [ha] with η hη
    apply matchedMeanU_agree_box
    intro y hy
    have hyS : y ∈ S := hy
    change sparseBoxField S (S.restrict η) y = η y
    rw [sparseBoxField, dif_pos hyS]
    exact hη y
  have hm : ∫ ξ, f ξ ∂(Measure.pi (fun _ : S => ν)) =
      ∫ η, matchedMeanU η 0 T x ∂(iidLaw d ν) := by
    rw [← hmap, integral_map hR.aemeasurable hf.aestronglyMeasurable]
    exact integral_congr_ae he
  have hg : HasSubgaussianMGF (fun ξ : S → ℤ => f ξ - ∫ ζ, f ζ ∂(Measure.pi (fun _ : S => ν))) V
      ((iidLaw d ν).map S.restrict) := by
    rw [hmap]
    exact hsg ν S 0 T x
  apply (HasSubgaussianMGF.of_map hR.aemeasurable hg).congr
  filter_upwards [he] with η hη
  dsimp only [Function.comp_def]
  rw [hη, hm]

/-- The scenery contribution has the paper's square-root moment bound, uniformly in the sparse law. -/
theorem exists_sparse_scenery_moment (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 0 < p → p ≤ 1 / 4 → ∀ (T : ℕ) (x : Site d) (r : ℝ), 2 ≤ r →
      Integrable (fun η : Site d → ℤ => |matchedMeanU η 0 T x -
        ∫ ζ, matchedMeanU ζ 0 T x ∂(iidLaw d (threePointLaw p))| ^ r) (iidLaw d (threePointLaw p)) ∧
      rNorm (iidLaw d (threePointLaw p)) r (fun η => matchedMeanU η 0 T x -
        ∫ ζ, matchedMeanU ζ 0 T x ∂(iidLaw d (threePointLaw p))) ≤ C * Real.sqrt r := by
  obtain ⟨V, _hV, hsg⟩ := exists_matchedMeanU_subgaussian hd
  refine ⟨2 * Real.exp ((V : ℝ) / 2), by positivity, fun p hp hp4 T x r hr => ?_⟩
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  exact subgaussian_rNorm_le _ _ ((measurable_matchedMeanU (by omega) 0 T x).sub_const _)
    V (hsg (threePointLaw p) (ae_clipSparse_threePointLaw p) T x) r hr
end Parking
