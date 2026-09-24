/- Exponential moments of finite independent linear combinations. -/
import Parking.Support.OneSiteExponential
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
namespace Parking
open MeasureTheory Finset

theorem linear_exponential_pi (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {τ D : ℝ} (hτ : 0 ≤ τ)
    (hb : ∀ t : ℝ, |t| ≤ τ →
      Integrable (fun z : ℝ => Real.exp (t * z)) μ ∧
      (∫ z : ℝ, Real.exp (t * z) ∂μ) ≤ Real.exp (D * t ^ 2))
    (N : ℕ) (a : Fin N → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    Integrable (fun ξ : Fin N → ℝ => Real.exp (τ * ∑ i, a i * ξ i))
        (Measure.pi fun _ : Fin N => μ) ∧
      (∫ ξ : Fin N → ℝ, Real.exp (τ * ∑ i, a i * ξ i)
        ∂(Measure.pi fun _ : Fin N => μ)) ≤ Real.exp (D * τ ^ 2 * ∑ i, a i ^ 2) := by
  have ht (i : Fin N) : |τ * a i| ≤ τ := by
    rw [abs_mul, abs_of_nonneg hτ]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (ha i) hτ
  have hp (ξ : Fin N → ℝ) : Real.exp (τ * ∑ i, a i * ξ i) =
      ∏ i, Real.exp ((τ * a i) * ξ i) := by
    rw [mul_sum, Real.exp_sum]
    congr 1
    funext i
    rw [mul_assoc]
  have hi := Integrable.fintype_prod (fun i : Fin N => (hb (τ * a i) (ht i)).1)
  refine ⟨by simpa only [← hp] using hi, ?_⟩
  simp_rw [hp]
  rw [integral_fintype_prod_eq_prod (fun (i : Fin N) (z : ℝ) => Real.exp ((τ * a i) * z))]
  calc (∏ i : Fin N, ∫ z : ℝ, Real.exp ((τ * a i) * z) ∂μ) ≤
      ∏ i : Fin N, Real.exp (D * (τ * a i) ^ 2) :=
        Finset.prod_le_prod (fun i _ => integral_nonneg fun z => (Real.exp_pos _).le)
          (fun i _ => (hb (τ * a i) (ht i)).2)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring

end Parking
