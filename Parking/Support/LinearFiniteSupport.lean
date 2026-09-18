/- Moment bounds for finitely supported linear coefficients. -/
import Parking.Support.LinearSceneryMoment

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset

/-- The finite-coordinate estimate expressed as a lattice sum with its
support supplied explicitly, so no nonsummable total is used. -/
theorem exists_linear_moment_finite_support {ι : Type*} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 2 ≤ p) (hmom : Integrable (fun z : ℝ => |z| ^ p) μ)
    (hmean : ∫ z : ℝ, z ∂μ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ι) (a : ι → ℝ), (∀ i ∉ S, a i = 0) →
      Integrable (fun ξ : ι → ℝ => |∑' i, a i * ξ i| ^ p) (Measure.infinitePi fun _ : ι => μ) ∧
      (∫ ξ : ι → ℝ, |∑' i, a i * ξ i| ^ p ∂(Measure.infinitePi fun _ : ι => μ)) ^ (2 / p) ≤
        C * ∑' i, a i ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_linear_moment_infinitePi (ι := ι) μ p hp hmom hmean
  refine ⟨C, hC, fun S a ha => ?_⟩
  have he (ξ : ι → ℝ) : (∑' i, a i * ξ i) = ∑ i ∈ S, a i * ξ i :=
    tsum_eq_sum (fun i hi => by rw [ha i hi, zero_mul])
  have hs : (∑' i, a i ^ 2) = ∑ i ∈ S, a i ^ 2 :=
    tsum_eq_sum (fun i hi => by rw [ha i hi, zero_pow (by norm_num)])
  simp only [he, hs]
  exact hb S a

end Parking
