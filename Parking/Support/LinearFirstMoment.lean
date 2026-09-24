/- First moments and centered positive parts of finite independent linear sums. -/
import Parking.Support.LinearMoment

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset

theorem integrable_linear_sum_infinitePi {ι : Type*} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (id : ℝ → ℝ) μ) (S : Finset ι) (a : ι → ℝ) :
    Integrable (fun ξ : ι → ℝ => ∑ i ∈ S, a i * ξ i) (Measure.infinitePi fun _ : ι => μ) := by
  apply integrable_finsetSum
  intro i _
  have h := integrable_comp_mp (measurePreserving_eval_infinitePi (fun _ : ι => μ) i)
    (id : ℝ → ℝ) measurable_id.aestronglyMeasurable hi
  exact h.const_mul (a i)

theorem integral_linear_sum_infinitePi {ι : Type*} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (id : ℝ → ℝ) μ) (hm : ∫ z : ℝ, z ∂μ = 0)
    (S : Finset ι) (a : ι → ℝ) :
    (∫ ξ : ι → ℝ, (∑ i ∈ S, a i * ξ i) ∂(Measure.infinitePi fun _ : ι => μ)) = 0 := by
  have hcoord (i : ι) : Integrable (fun ξ : ι → ℝ => ξ i) (Measure.infinitePi fun _ : ι => μ) :=
    integrable_comp_mp (measurePreserving_eval_infinitePi (fun _ : ι => μ) i)
      (id : ℝ → ℝ) measurable_id.aestronglyMeasurable hi
  have hmean (i : ι) : (∫ ξ : ι → ℝ, ξ i ∂(Measure.infinitePi fun _ : ι => μ)) = 0 :=
    (integral_comp_mp (measurePreserving_eval_infinitePi (fun _ : ι => μ) i)
      (id : ℝ → ℝ) measurable_id.aestronglyMeasurable).symm.trans hm
  rw [integral_finsetSum S (fun i _ => (hcoord i).const_mul (a i))]
  simp only [integral_const_mul, hmean, mul_zero, sum_const_zero]

theorem integral_max_zero_eq_half_abs {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω)
    {X : Ω → ℝ} (hi : Integrable X Q) (hm : ∫ ω, X ω ∂Q = 0) :
    (∫ ω, max 0 (X ω) ∂Q) = (1 / 2 : ℝ) * ∫ ω, |X ω| ∂Q := by
  have he (ω : Ω) : 2 * max 0 (X ω) = |X ω| + X ω := by
    by_cases h : 0 ≤ X ω
    · rw [max_eq_right h, abs_of_nonneg h]; ring
    · rw [max_eq_left (not_le.mp h).le, abs_of_neg (not_le.mp h)]; ring
  have h : 2 * (∫ ω, max 0 (X ω) ∂Q) = (∫ ω, |X ω| ∂Q) := by
    rw [← integral_const_mul, integral_congr_ae (Filter.Eventually.of_forall he), integral_add hi.abs hi,
      hm, add_zero]
  linarith

end Parking
