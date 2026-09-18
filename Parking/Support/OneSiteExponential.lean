/- A quadratic exponential-moment bound near the origin for a centered law. -/
import Parking.Support.ExponentialRemainder
import Parking.Support.ConfMoments

noncomputable section
namespace Parking
open MeasureTheory

theorem exists_oneSite_exponential_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (id : ℝ → ℝ) μ) (hm : ∫ z : ℝ, z ∂μ = 0)
    {θ : ℝ} (hθ : 0 < θ) (he : Integrable (fun z : ℝ => Real.exp (θ * |z|)) μ) :
    ∃ τ D : ℝ, 0 < τ ∧ 0 < D ∧ ∀ t : ℝ, |t| ≤ τ →
      Integrable (fun z : ℝ => Real.exp (t * z)) μ ∧
      (∫ z : ℝ, Real.exp (t * z) ∂μ) ≤ Real.exp (D * t ^ 2) := by
  let τ := θ / 2
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  obtain ⟨C, _hC, hbound⟩ := rpow_le_const_mul_exp (r := (2 : ℝ)) (by norm_num) hτ
  let W : ℝ → ℝ := fun z => z ^ 2 * Real.exp (τ * |z|)
  have hW : Integrable W μ := by
    refine (he.const_mul C).mono' (by dsimp only [W]; fun_prop)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp only [W]; positivity)]
    have hz := hbound |z| (abs_nonneg z)
    rw [Real.rpow_two, sq_abs] at hz
    calc W z ≤ C * Real.exp (τ * |z|) * Real.exp (τ * |z|) :=
        mul_le_mul_of_nonneg_right hz (Real.exp_pos _).le
      _ = C * Real.exp (θ * |z|) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        dsimp only [τ]
        ring
  let D := (∫ z, W z ∂μ) + 1
  have hD : 0 < D := by
    have h : 0 ≤ ∫ z, W z ∂μ := integral_nonneg fun z => mul_nonneg (sq_nonneg z) (Real.exp_pos _).le
    dsimp only [D]
    linarith
  refine ⟨τ, D, hτ, hD, fun t ht => ?_⟩
  have htθ : |t| ≤ θ := by dsimp only [τ] at ht; linarith
  have htz (z : ℝ) : |t * z| ≤ τ * |z| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ht (abs_nonneg z)
  have hti : Integrable (fun z : ℝ => Real.exp (t * z)) μ := by
    refine he.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc t * z ≤ |t * z| := le_abs_self _
      _ ≤ θ * |z| := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right htθ (abs_nonneg z)
  have hpt (z : ℝ) : Real.exp (t * z) ≤ 1 + t * z + t ^ 2 * W z := by
    have h := exp_quadratic_remainder (t * z)
    have hrem := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (htz z)) (sq_nonneg (t * z))
    have heq : (t * z) ^ 2 * Real.exp (τ * |z|) = t ^ 2 * W z := by dsimp only [W]; ring
    rw [heq] at hrem
    linarith
  have hti0 : Integrable (fun z : ℝ => t * z) μ := by simpa only [id_eq] using hi.const_mul t
  have h1 : Integrable (fun z : ℝ => 1 + t * z) μ :=
    (integrable_const 1).add hti0
  have hlin : (∫ z : ℝ, 1 + t * z ∂μ) = 1 := by
    rw [integral_add (integrable_const 1) hti0, integral_const_mul, hm]
    simp
  have hraw := integral_mono hti (h1.add (hW.const_mul (t ^ 2))) hpt
  simp only [Pi.add_apply, integral_add h1 (hW.const_mul (t ^ 2)),
    hlin, integral_const_mul] at hraw
  refine ⟨hti, hraw.trans ?_⟩
  calc
    1 + t ^ 2 * (∫ z, W z ∂μ) ≤ D * t ^ 2 + 1 := by
      dsimp only [D]
      nlinarith [sq_nonneg t]
    _ ≤ _ := Real.add_one_le_exp _

end Parking
