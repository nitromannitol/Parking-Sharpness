/- Finite coefficient moments under an infinite independent field. -/
import Parking.Support.LinearMoment

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset

/-- The square-function estimate on any finite set of an independent field. -/
theorem exists_linear_moment_infinitePi {ι : Type*} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 2 ≤ p) (hmom : Integrable (fun z : ℝ => |z| ^ p) μ)
    (hmean : ∫ z : ℝ, z ∂μ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ι) (a : ι → ℝ),
      Integrable (fun ξ : ι → ℝ => |∑ i ∈ S, a i * ξ i| ^ p) (Measure.infinitePi fun _ : ι => μ) ∧
      (∫ ξ : ι → ℝ, |∑ i ∈ S, a i * ξ i| ^ p ∂(Measure.infinitePi fun _ : ι => μ)) ^ (2 / p) ≤
        C * ∑ i ∈ S, a i ^ 2 := by
  classical
  obtain ⟨C, hC, hb⟩ := exists_linear_moment_bound μ p hp hmom hmean
  refine ⟨C, hC, fun S a => ?_⟩
  let e := S.equivFin.symm
  let v : Fin S.card → ι := fun i => (e i).val
  have hv : Function.Injective v := fun i j h => e.injective (Subtype.ext h)
  let read : (ι → ℝ) → Fin S.card → ℝ := fun ξ i => ξ (v i)
  have hread : MeasurePreserving read (Measure.infinitePi fun _ : ι => μ)
      (Measure.pi fun _ : Fin S.card => μ) :=
    ⟨measurable_pi_lambda _ (fun i => measurable_pi_apply (v i)), infinitePi_map_comp μ v hv⟩
  have he : ∀ f : ι → ℝ, (∑ i : Fin S.card, f (v i)) = ∑ j ∈ S, f j := by
    intro f
    exact (e.sum_comp (fun j : S => f j.val)).trans (Finset.sum_coe_sort S f)
  obtain ⟨hI, hB⟩ := hb S.card (fun i => a (v i))
  let F : (Fin S.card → ℝ) → ℝ := fun ξ => |∑ i, a (v i) * ξ i| ^ p
  have hF : Measurable F := by dsimp only [F]; fun_prop
  have hcomp : ∀ ξ : ι → ℝ, F (read ξ) = |∑ j ∈ S, a j * ξ j| ^ p := by
    intro ξ
    dsimp only [F, read]
    rw [he (fun j => a j * ξ j)]
  have hi := integrable_comp_mp hread F hF.aestronglyMeasurable hI
  have heq := integral_comp_mp hread F hF.aestronglyMeasurable
  have hsq := he (fun j => a j ^ 2)
  change (∫ ξ, F ξ ∂(Measure.pi fun _ : Fin S.card => μ)) ^ (2 / p) ≤
    C * ∑ i : Fin S.card, a (v i) ^ 2 at hB
  rw [heq, hsq] at hB
  simp only [hcomp] at hi hB
  exact ⟨hi, hB⟩

end Parking
