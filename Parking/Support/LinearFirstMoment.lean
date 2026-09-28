import Parking.Support.LinearMoment

/-!
# First moments and centered positive parts of finite linear sums

First moments and centered positive parts of finite independent linear sums. A finite linear
combination of i.i.d. coordinates with integrable coordinates is itself integrable, has mean
zero when each coordinate does, and for a mean-zero integrable random variable the mean of its
positive part is half the mean of its absolute value.
-/

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset

/-- A finite linear combination `∑ i ∈ S, a i * ξ i` of independent coordinates with integrable
law `μ` is itself integrable, term by term via `integrable_comp_mp` and `Integrable.const_mul`. -/
theorem integrable_linear_sum_infinitePi {ι : Type*} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (id : ℝ → ℝ) μ) (S : Finset ι) (a : ι → ℝ) :
    Integrable (fun ξ : ι → ℝ => ∑ i ∈ S, a i * ξ i) (Measure.infinitePi fun _ : ι => μ) := by
  apply integrable_finsetSum
  intro i _
  have h := integrable_comp_mp (measurePreserving_eval_infinitePi (fun _ : ι => μ) i)
    (id : ℝ → ℝ) measurable_id.aestronglyMeasurable hi
  exact h.const_mul (a i)

/-- A finite linear combination `∑ i ∈ S, a i * ξ i` of independent mean-zero coordinates has
mean `0`, since each coordinate's mean is `0` by `hm` transported through `integral_comp_mp`. -/
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

/-- For a mean-zero integrable `X`, `E[max 0 X] = (1/2) * E[|X|]`, from the pointwise identity
`2 * max 0 X = |X| + X`. -/
theorem integral_max_zero_eq_half_abs {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω)
    {X : Ω → ℝ} (hi : Integrable X Q) (hm : ∫ ω, X ω ∂Q = 0) :
    (∫ ω, max 0 (X ω) ∂Q) = (1 / 2 : ℝ) * ∫ ω, |X ω| ∂Q := by
  have he (ω : Ω) : 2 * max 0 (X ω) = |X ω| + X ω := by
    by_cases h : 0 ≤ X ω
    · rw [max_eq_right h, abs_of_nonneg h]; ring
    · rw [max_eq_left (not_le.mp h).le, abs_of_neg (not_le.mp h)]; ring
  have h : 2 * (∫ ω, max 0 (X ω) ∂Q) = (∫ ω, |X ω| ∂Q) := by
    rw [← integral_const_mul, integral_congr_ae (Filter.Eventually.of_forall he),
        integral_add hi.abs hi, hm, add_zero]
  linarith

end Parking
