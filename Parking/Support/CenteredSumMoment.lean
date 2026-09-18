/- Centered finite sums under independent coordinate laws. -/
import Parking.Support.LinearSceneryMoment
import LatticeProb.Prob.MapPi

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset

/-- A common centered coordinate law gives square-root moments for sums over
arbitrary finite subsets of an independent family. -/
theorem exists_centered_sum_moment {ι α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (p : ℝ) (hp : 2 ≤ p) (hmom : Integrable (fun x => |f x| ^ p) μ)
    (hmean : ∫ x, f x ∂μ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : Finset ι,
      Integrable (fun ω : ι → α => |∑ i ∈ S, f (ω i)| ^ p) (Measure.infinitePi fun _ : ι => μ) ∧
      (∫ ω : ι → α, |∑ i ∈ S, f (ω i)| ^ p ∂(Measure.infinitePi fun _ : ι => μ)) ^ (2 / p) ≤
        C * (S.card : ℝ) := by
  let ν := μ.map f
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hνmom : Integrable (fun z : ℝ => |z| ^ p) ν :=
    (integrable_map_measure (measurable_abs.pow_const p).aestronglyMeasurable hf.aemeasurable).mpr hmom
  have hνmean : (∫ z : ℝ, z ∂ν) = 0 := by
    exact (integral_map (μ := μ) (φ := f) (f := fun z : ℝ => z)
      hf.aemeasurable measurable_id.aestronglyMeasurable).trans hmean
  obtain ⟨C, hC, hb⟩ := exists_linear_moment_infinitePi (ι := ι) ν p hp hνmom hνmean
  refine ⟨C, hC, fun S => ?_⟩
  let mapField : (ι → α) → ι → ℝ := fun ω i => f (ω i)
  have hmap : MeasurePreserving mapField (Measure.infinitePi fun _ : ι => μ)
      (Measure.infinitePi fun _ : ι => ν) :=
    ⟨measurable_pi_lambda _ (fun i => hf.comp (measurable_pi_apply i)),
      LatticeProb.infinitePi_map_pi μ hf⟩
  obtain ⟨hI, hB⟩ := hb S (fun _ => 1)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hI hB
  let F : (ι → ℝ) → ℝ := fun ξ => |∑ i ∈ S, ξ i| ^ p
  have hF : Measurable F := by dsimp only [F]; fun_prop
  have hi := integrable_comp_mp hmap F hF.aestronglyMeasurable hI
  have he := integral_comp_mp hmap F hF.aestronglyMeasurable
  change (∫ ξ, F ξ ∂(Measure.infinitePi fun _ : ι => ν)) ^ (2 / p) ≤ C * (S.card : ℝ) at hB
  rw [he] at hB
  exact ⟨hi, hB⟩

end Parking
