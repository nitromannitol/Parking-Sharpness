/- A uniform first-moment lower bound for centered iid linear combinations. -/
import Parking.Support.SecondFourthMean
import Parking.Support.LinearMoment

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory LatticeProb Finset

theorem integral_sq_linear_sum_pi (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h4 : Integrable (fun z : ℝ => z ^ 4) μ) (hmean : ∫ z : ℝ, z ∂μ = 0)
    (N : ℕ) (a : Fin N → ℝ) :
    (∫ ξ : Fin N → ℝ, (∑ i, a i * ξ i) ^ 2 ∂(Measure.pi fun _ : Fin N => μ)) =
      (∫ z : ℝ, z ^ 2 ∂μ) * ∑ i, a i ^ 2 := by
  let X : Fin N → (Fin N → ℝ) → ℝ := fun i ξ => a i * ξ i
  have hm (i : Fin N) : Measurable (X i) := by dsimp only [X]; fun_prop
  have h4i (i : Fin N) : Integrable (fun z : ℝ => (a i * z) ^ 4) μ := by
    simpa only [mul_pow] using h4.const_mul (a i ^ 4)
  have hi (i : Fin N) : Integrable (fun ξ => X i ξ ^ 4) (Measure.pi fun _ : Fin N => μ) :=
    integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) (h4i i)
  have hind : iIndepFun X (Measure.pi fun _ : Fin N => μ) :=
    iIndepFun_pi (fun i : Fin N => (measurable_id.const_mul (a i)).aemeasurable)
  have hmi (i : Fin N) : (∫ ξ, X i ξ ∂(Measure.pi fun _ : Fin N => μ)) = 0 := by
    dsimp only [X]
    have he := integral_comp_eval (μ := fun _ : Fin N => μ) (i := i)
      (measurable_id.const_mul (a i)).aestronglyMeasurable
    calc (∫ ξ : Fin N → ℝ, a i * ξ i ∂(Measure.pi fun _ : Fin N => μ)) =
        ∫ z : ℝ, a i * z ∂μ := by simpa only [id_eq] using he
      _ = 0 := by rw [integral_const_mul, hmean, mul_zero]
  have hsq := integral_sq_finsetSum X hm hind hi hmi univ
  have he (i : Fin N) : (∫ ξ, X i ξ ^ 2 ∂(Measure.pi fun _ : Fin N => μ)) =
      a i ^ 2 * (∫ z : ℝ, z ^ 2 ∂μ) := by
    dsimp only [X]
    have hh := integral_comp_eval (μ := fun _ : Fin N => μ) (i := i)
      ((measurable_id.const_mul (a i)).pow_const 2).aestronglyMeasurable
    simpa only [id_eq, mul_pow, integral_const_mul] using hh
  simpa only [he, ← sum_mul, mul_comm] using hsq

theorem exists_linear_abs_mean_lower (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h4 : Integrable (fun z : ℝ => z ^ 4) μ) (hmean : ∫ z : ℝ, z ∂μ = 0)
    (hvar : 0 < ∫ z : ℝ, z ^ 2 ∂μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (a : Fin N → ℝ),
      c * Real.sqrt (∑ i, a i ^ 2) ≤
        ∫ ξ : Fin N → ℝ, |∑ i, a i * ξ i| ∂(Measure.pi fun _ : Fin N => μ) := by
  have habs4 (x : ℝ) : |x| ^ (4 : ℝ) = x ^ 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [show |x| ^ 4 = (|x| ^ 2) ^ 2 by ring, sq_abs]
    ring
  have h4r : Integrable (fun z : ℝ => |z| ^ (4 : ℝ)) μ := by simpa only [habs4] using h4
  obtain ⟨C, hC, hb⟩ := exists_linear_moment_bound μ 4 (by norm_num) h4r hmean
  let v := ∫ z : ℝ, z ^ 2 ∂μ
  refine ⟨v ^ 2 / (4 * C ^ 2) * Real.sqrt (v / 2), by dsimp only [v]; positivity, fun N a => ?_⟩
  let V := ∑ i : Fin N, a i ^ 2
  have hV : 0 ≤ V := sum_nonneg fun i _ => sq_nonneg _
  by_cases hV0 : V = 0
  · change _ * Real.sqrt V ≤ _
    rw [hV0, Real.sqrt_zero, mul_zero]
    exact integral_nonneg fun ξ => abs_nonneg _
  · have hVp : 0 < V := lt_of_le_of_ne hV (Ne.symm hV0)
    obtain ⟨hi, hbound⟩ := hb N a
    simp only [habs4] at hi hbound
    have hI0 : 0 ≤ ∫ ξ : Fin N → ℝ, (∑ i, a i * ξ i) ^ 4 ∂(Measure.pi fun _ : Fin N => μ) :=
      integral_nonneg fun ξ => by positivity
    have hfourth : (∫ ξ : Fin N → ℝ, (∑ i, a i * ξ i) ^ 4 ∂(Measure.pi fun _ : Fin N => μ)) ≤
        C ^ 2 * V ^ 2 := by
      have hh := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) hbound (by norm_num : (0 : ℝ) ≤ 2)
      rw [← Real.rpow_mul hI0, show (2 / (4 : ℝ)) * 2 = 1 by norm_num, Real.rpow_one,
        Real.rpow_two, mul_pow] at hh
      exact hh
    exact abs_mean_lower_of_second_fourth (Measure.pi fun _ : Fin N => μ)
      (fun ξ => ∑ i, a i * ξ i) (by fun_prop) hi hvar (sq_pos_of_pos hC) hVp
      (integral_sq_linear_sum_pi μ h4 hmean N a) hfourth

end Parking
