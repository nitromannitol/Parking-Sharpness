/- First-moment lower bounds for linear combinations of centered integer scenery. -/
import Parking.Support.LinearFourthLower
import Parking.Support.LinearConvex
import Parking.Support.SparseParameter

noncomputable section
namespace Parking
open MeasureTheory LatticeProb

/-- The coefficient square norm controls the first absolute moment, with no
fourth-moment requirement on the original integer law. -/
theorem exists_integer_linear_abs_lower (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hnc : ∀ k : ℤ, ν {k} ≠ 1) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k : ℤ, (k : ℝ) ∂ν = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (a : Fin N → ℝ),
      c * Real.sqrt (∑ i, a i ^ 2) ≤
        ∫ ξ : Fin N → ℝ, |∑ i, a i * ξ i| ∂(Measure.pi fun _ : Fin N => realLaw ν) := by
  obtain ⟨p, hp, hp2, hpν⟩ := exists_sparse_comparison_parameter ν hnc hint hmean
  haveI := threePointLaw_isProbability hp.le hp2
  have h4 : Integrable (fun z : ℝ => z ^ 4) (realLaw (threePointLaw p)) :=
    (realLaw_integrable_iff _ (measurable_id.pow_const 4)).mpr (integrable_threePointLaw p _)
  have hμm : (∫ z : ℝ, z ∂(realLaw (threePointLaw p))) = 0 :=
    realLaw_mean _ (criticalLaw_threePointLaw hp hp2)
  have hμv : 0 < ∫ z : ℝ, z ^ 2 ∂(realLaw (threePointLaw p)) := by
    rw [realLaw_integral (threePointLaw p) (f := fun z : ℝ => z ^ 2) (by fun_prop),
      integral_threePointLaw hp.le hp2]
    norm_num only [Int.cast_one, Int.cast_neg, Int.cast_zero, one_pow, neg_one_sq, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_one, mul_zero, add_zero]
    linarith
  obtain ⟨c, hc, hlo⟩ := exists_linear_abs_mean_lower (realLaw (threePointLaw p)) h4 hμm hμv
  have hμi : Integrable (id : ℝ → ℝ) (realLaw (threePointLaw p)) :=
    (realLaw_integrable_iff _ measurable_id).mpr (integrable_threePointLaw p _)
  have hνi : Integrable (id : ℝ → ℝ) (realLaw ν) := by
    apply (realLaw_integrable_iff ν measurable_id).mpr
    exact hint.mono' measurable_intCastReal.aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => by simp only [Real.norm_eq_abs]; rfl)
  refine ⟨c, hc, fun N a => (hlo N a).trans ?_⟩
  exact convex_lipschitz_integral_le_pi hμi hνi
    (fun f _ hconv hlip => threePoint_convex_integral_le ν hint hmean hp.le hp2 hpν f hconv hlip)
    N (convexOn_abs_linear_sum N a) (lipschitzWith_abs_linear_sum N a)

end Parking
