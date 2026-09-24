/- Transport of a finite linear lower bound to an infinite independent field. -/
import Parking.Support.LinearMoment

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset

theorem linear_abs_lower_infinitePi {ι : Type*} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {c : ℝ} (hb : ∀ (N : ℕ) (a : Fin N → ℝ), c * Real.sqrt (∑ i, a i ^ 2) ≤
      ∫ ξ : Fin N → ℝ, |∑ i, a i * ξ i| ∂(Measure.pi fun _ : Fin N => μ))
    (S : Finset ι) (a : ι → ℝ) :
    c * Real.sqrt (∑ i ∈ S, a i ^ 2) ≤
      ∫ ξ : ι → ℝ, |∑ i ∈ S, a i * ξ i| ∂(Measure.infinitePi fun _ : ι => μ) := by
  classical
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
  have hB := hb S.card (fun i => a (v i))
  let F : (Fin S.card → ℝ) → ℝ := fun ξ => |∑ i, a (v i) * ξ i|
  have hF : Measurable F := by dsimp only [F]; fun_prop
  have heq := integral_comp_mp hread F hF.aestronglyMeasurable
  have hcomp (ξ : ι → ℝ) : F (read ξ) = |∑ i ∈ S, a i * ξ i| := by
    dsimp only [F, read]
    rw [he (fun i => a i * ξ i)]
  change c * Real.sqrt (∑ i : Fin S.card, a (v i) ^ 2) ≤
    (∫ ξ, F ξ ∂(Measure.pi fun _ : Fin S.card => μ)) at hB
  rw [heq, he (fun i => a i ^ 2)] at hB
  simpa only [hcomp] using hB

end Parking
