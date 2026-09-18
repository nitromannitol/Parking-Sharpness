/- The directed particle mean dominates the divisible odometer for fixed scenery. -/
import Parking.Support.OrientedArrivalMean
import Parking.Support.OrientedPotential

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

theorem uOriented_le_mean_orientedOdometer (hd : 1 ≤ d) (η : Site d → ℤ) (n : ℕ) (x : Site d) :
    uOriented (fun y => (η y : ℝ)) n x ≤
      ∫ σ : Site d × ℕ → Site d, (orientedOdometer η σ n x : ℝ) ∂(orientedStackLaw d) := by
  haveI := orientedStackLaw_isProbability hd
  induction n generalizing x with
  | zero => simp [uOriented, orientedOdometer]
  | succ n ih =>
    have hNI := integrable_orientedArrivals_given hd η n x
    have hUI := integrable_orientedOdometer_given hd η (n + 1) x
    have hpt (σ : Site d × ℕ → Site d) : (η x : ℝ) + (orientedArrivalCount η σ n x : ℝ) ≤
        (orientedOdometer η σ (n + 1) x : ℝ) := by
      rw [orientedOdometer_succ, toNat_cast_eq_max, Int.cast_add, Int.cast_natCast]
      exact le_max_left _ _
    have hraw := integral_mono ((integrable_const (η x : ℝ)).add hNI) hUI hpt
    simp only [Pi.add_apply, integral_add (integrable_const (η x : ℝ)) hNI,
      integral_const, probReal_univ, one_smul, integral_orientedArrivalCount_given hd η n x] at hraw
    change max 0 ((η x : ℝ) + orientedOp (uOriented (fun y => (η y : ℝ)) n) x) ≤ _
    apply max_le (integral_nonneg fun σ => Nat.cast_nonneg _)
    have hmono := orientedOp_mono ih x
    linarith

end Parking
