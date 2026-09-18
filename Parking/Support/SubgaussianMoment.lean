import Parking.Support.BoundedProduct
import Parking.Support.DiscrepancyNorm

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- An explicit power-exponential bound, with a real exponent. -/
theorem rpow_le_scaled_exp {r θ : ℝ} (hr : 0 < r) (hθ : 0 < θ) (x : ℝ) (hx : 0 ≤ x) :
    x ^ r ≤ (r / θ) ^ r * Real.exp (θ * x) := by
  have hz : 0 ≤ θ * x / r := by positivity
  have he : θ * x / r ≤ Real.exp (θ * x / r) := by linarith [Real.add_one_le_exp (θ * x / r)]
  have hp := Real.rpow_le_rpow hz he hr.le
  rw [← Real.exp_mul] at hp
  have heq : θ * x / r * r = θ * x := by field_simp
  rw [heq] at hp
  calc
    x ^ r = ((r / θ) * (θ * x / r)) ^ r := by congr 1; field_simp
    _ = (r / θ) ^ r * (θ * x / r) ^ r := Real.mul_rpow (by positivity) hz
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

/-- A sub-Gaussian moment-generating bound gives the square-root moment scale. -/
theorem subgaussian_rNorm_le {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hXm : Measurable X)
    (V : ℝ≥0) (hX : HasSubgaussianMGF X V μ) (r : ℝ) (hr : 2 ≤ r) :
    Integrable (fun ω => |X ω| ^ r) μ ∧
      rNorm μ r X ≤ (2 * Real.exp ((V : ℝ) / 2)) * Real.sqrt r := by
  have hr0 : 0 < r := by linarith
  let θ := Real.sqrt r
  have hθ : 0 < θ := Real.sqrt_pos.mpr hr0
  have hθ2 : θ ^ 2 = r := Real.sq_sqrt hr0.le
  have he (x : ℝ) : Real.exp (θ * |x|) ≤ Real.exp (θ * x) + Real.exp (-θ * x) := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_neg (lt_of_not_ge hx), mul_neg, ← neg_mul]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have hei : Integrable (fun ω => Real.exp (θ * |X ω|)) μ :=
    Integrable.mono' ((hX.integrable_exp_mul θ).add (hX.integrable_exp_mul (-θ)))
      ((hXm.abs.const_mul θ).exp.aestronglyMeasurable) (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact he (X ω))
  have hE : ∫ ω, Real.exp (θ * |X ω|) ∂μ ≤ 2 * Real.exp ((V : ℝ) * r / 2) := by
    calc
      _ ≤ ∫ ω, Real.exp (θ * X ω) + Real.exp (-θ * X ω) ∂μ :=
        integral_mono hei ((hX.integrable_exp_mul θ).add (hX.integrable_exp_mul (-θ))) (fun ω => he (X ω))
      _ = (∫ ω, Real.exp (θ * X ω) ∂μ) + ∫ ω, Real.exp (-θ * X ω) ∂μ :=
        integral_add (hX.integrable_exp_mul θ) (hX.integrable_exp_mul (-θ))
      _ ≤ _ := by
        have hp := hX.mgf_le θ
        have hn := hX.mgf_le (-θ)
        simp only [mgf, neg_sq, hθ2] at hp hn
        linarith
  have hdiv : r / θ = θ := by apply (div_eq_iff hθ.ne').mpr; nlinarith [hθ2]
  have hi : Integrable (fun ω => |X ω| ^ r) μ :=
    Integrable.mono' (hei.const_mul (θ ^ r)) ((hXm.abs.pow measurable_const).aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        simpa only [hdiv] using rpow_le_scaled_exp hr0 hθ |X ω| (abs_nonneg _))
  refine ⟨hi, ?_⟩
  have hI : ∫ ω, |X ω| ^ r ∂μ ≤ θ ^ r * (2 * Real.exp ((V : ℝ) * r / 2)) := by
    calc
      _ ≤ ∫ ω, θ ^ r * Real.exp (θ * |X ω|) ∂μ :=
        integral_mono hi (hei.const_mul _) (fun ω => by
          simpa only [hdiv] using rpow_le_scaled_exp hr0 hθ |X ω| (abs_nonneg _))
      _ = θ ^ r * ∫ ω, Real.exp (θ * |X ω|) ∂μ := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg hθ.le _)
  unfold rNorm
  apply (Real.rpow_le_rpow (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _) hI (by positivity : 0 ≤ 1 / r)).trans
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hθ.le,
    show r * (1 / r) = 1 by field_simp, Real.rpow_one,
    Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
  have heq : ((V : ℝ) * r / 2) * (1 / r) = (V : ℝ) / 2 := by field_simp
  rw [heq]
  have htwo : (2 : ℝ) ^ (1 / r) ≤ 2 := by
    apply Real.rpow_le_self_of_one_le (by norm_num)
    exact (div_le_one hr0).mpr (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right htwo (Real.exp_pos ((V : ℝ) / 2)).le]
end Parking
