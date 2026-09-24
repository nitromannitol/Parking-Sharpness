/- Exponential moments of directed potentials from their square norms. -/
import Parking.Support.LinearExponentialLift
import Parking.Support.OrientedFinite
import Parking.Support.OrientedLogNorm

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem orientedGreen_box_sq (n : ℕ) (x : Site d) :
    (∑ z ∈ boxFinset x n, orientedGreen d n (z - x) ^ 2) =
      ∑' z : Site d, orientedGreen d n z ^ 2 := by
  have hs : (∑' z : Site d, orientedGreen d n (z - x) ^ 2) =
      ∑ z ∈ boxFinset x n, orientedGreen d n (z - x) ^ 2 :=
    tsum_eq_sum fun z hz => by rw [orientedGreen_sub_zero_outside hz, zero_pow (by norm_num)]
  have ht := (Equiv.addRight x).tsum_eq (fun z : Site d => orientedGreen d n (z - x) ^ 2)
  simp only [Equiv.coe_addRight, add_sub_cancel_right] at ht
  exact hs.symm.trans ht.symm

theorem exists_orientedPotential_exponential (hd : 3 ≤ d)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (id : ℝ → ℝ) μ) (hm : ∫ z : ℝ, z ∂μ = 0)
    {θ : ℝ} (hθ : 0 < θ) (he : Integrable (fun z : ℝ => Real.exp (θ * |z|)) μ) :
    ∃ τ A : ℝ, 0 < τ ∧ 0 < A ∧ ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, m ≤ n → ∀ x : Site d,
      Integrable (fun η : Site d → ℝ => Real.exp (τ * |orientedPotential η m x|)) (iidLaw d μ) ∧
        (∫ η : Site d → ℝ, Real.exp (τ * |orientedPotential η m x|) ∂(iidLaw d μ)) ≤
          2 * Real.exp (A * Real.log ((n : ℝ) + 1)) := by
  obtain ⟨τ, B, hτ, hB, hb⟩ := exists_linear_abs_exponential (ι := Site d) μ hi hm hθ he
  obtain ⟨C, hC, hnorm⟩ := exists_orientedGreen_sq_log_bound hd
  refine ⟨τ, B * C, hτ, by positivity, fun n hn m hmn x => ?_⟩
  obtain ⟨hI, hBound⟩ := hb (boxFinset x m) (fun z => orientedGreen d m (z - x))
    (fun z _ => by rw [abs_of_nonneg (orientedGreen_nonneg m (z - x))]; exact orientedGreen_le_one (by omega) m (z - x))
  simp only [← orientedPotential_eq_box, orientedGreen_box_sq] at hI hBound
  refine ⟨hI, hBound.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))⟩
  have h := mul_le_mul_of_nonneg_left (hnorm n hn m hmn) hB.le
  simpa only [mul_assoc] using h

end Parking
