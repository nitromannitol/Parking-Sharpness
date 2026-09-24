import Parking.Support.ArrivalCompensator
import Parking.Support.RoundNoArrival

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The no-arrival indicator multiplied by the exponential of the entrance compensator. -/
def noArrivalWeight (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (t : ℕ) (x : Site d) : ℝ :=
  if noArrivalFlag η ρ σ t x then Real.exp (arrivalCompensator η ρ σ t x) else 0

theorem noArrivalWeight_zero (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (x : Site d) :
    noArrivalWeight η ρ σ 0 x = 1 := by
  simp [noArrivalWeight, noArrivalFlag, arrivalCompensator_zero]

theorem measurable_noArrivalWeight (hd : 1 ≤ d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (t : ℕ) (x : Site d) :
    Measurable (fun σ : RoundNoise d => noArrivalWeight η ρ σ t x) := by
  exact Measurable.ite ((measurable_noArrivalFlag hd η ρ t x) (measurableSet_singleton true))
    (measurable_arrivalCompensator hd η ρ t x).exp measurable_const

theorem noArrivalWeight_bound (hd : 1 ≤ d) (η : Site d → ℤ) (K : ℕ)
    (hη : ∀ y, (η y).toNat ≤ K) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (t : ℕ) (x : Site d) :
    ‖noArrivalWeight η ρ σ t x‖ ≤ Real.exp ((t * ((2 * t + 1) ^ d * K) : ℕ) : ℝ) := by
  unfold noArrivalWeight
  split
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (arrivalCompensator_bound hd η K hη ρ σ t x)
  · simp only [norm_zero]
    exact (Real.exp_pos _).le

/-- Each fresh round decreases the expected no-arrival exponential weight. -/
theorem noArrivalWeight_section (hd : 1 ≤ d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (t : ℕ) (x : Site d) :
    ∫ τ, noArrivalWeight η ρ (Function.update σ t τ) (t + 1) x
      ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d) ≤ noArrivalWeight η ρ σ t x := by
  classical
  haveI := stepLaw_isProbability hd
  let A := matchedCount η ρ σ t
  let c := arrivalCompensator η ρ σ t x
  let b := walkOp (fun y => (A y : ℝ)) x
  have heA (τ : RoundSlot d → Fin d × Bool) : matchedCount η ρ (Function.update σ t τ) t = A := by
    funext y
    unfold matchedCount
    rw [matchedState_update η ρ σ t t τ le_rfl]
    rfl
  by_cases hf : noArrivalFlag η ρ σ t x = true
  · have he (τ : RoundSlot d → Fin d × Bool) : noArrivalWeight η ρ (Function.update σ t τ) (t + 1) x =
        Real.exp (c + b) * (if (countArrivals A τ x).card = 0 then (1 : ℝ) else 0) := by
      unfold noArrivalWeight
      rw [noArrivalFlag, noArrivalFlag_update η ρ σ t t τ le_rfl, hf]
      simp only [Bool.true_and, decide_eq_true_eq]
      rw [card_matchedArrivals_eq_countArrivals, heA, Function.update_self,
        arrivalCompensator_succ, arrivalCompensator_update η ρ σ t t τ le_rfl, heA]
      by_cases hz : (countArrivals A τ x).card = 0 <;> simp [hz, c, b]
    simp_rw [he]
    rw [integral_const_mul, noArrivalWeight, if_pos hf]
    have h := mul_le_mul_of_nonneg_left (integral_noArrivals_le_exp hd A x) (Real.exp_pos (c + b)).le
    apply h.trans_eq
    rw [← Real.exp_add]
    congr 1
    dsimp only [c, b]
    ring
  · have he (τ : RoundSlot d → Fin d × Bool) : noArrivalWeight η ρ (Function.update σ t τ) (t + 1) x = 0 := by
      unfold noArrivalWeight
      rw [noArrivalFlag, noArrivalFlag_update η ρ σ t t τ le_rfl]
      simp [hf]
    simp_rw [he]
    rw [integral_zero, noArrivalWeight, if_neg hf]
end Parking
