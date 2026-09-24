import Parking.Support.MatchedBounds
import Parking.Support.SingleInfluence

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Mean odometer over the common instruction tables, with configuration and priorities fixed. -/
def matchedMeanU (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) : ℝ :=
  ∫ σ, ((matchedState η ρ σ T).departures x : ℝ) ∂(roundNoiseLaw d)

/-- One addition has nonnegative expected influence bounded by the Green function. -/
theorem matchedMeanU_addParticle (hd : 3 ≤ d) (η : Site d → ℤ)
    (v : Site d) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) :
    0 ≤ matchedMeanU (addParticle v η) ρ T x - matchedMeanU η ρ T x ∧
      matchedMeanU (addParticle v η) ρ T x - matchedMeanU η ρ T x ≤ fullGreen d (v - x) := by
  have hd1 : 1 ≤ d := by omega
  unfold matchedMeanU
  rw [← integral_sub (integrable_matchedOdometer hd1 _ _ _ _) (integrable_matchedOdometer hd1 _ _ _ _)]
  constructor
  · apply integral_nonneg
    intro σ
    dsimp only [Pi.zero_apply]
    rw [singleAddition_odometer_difference]
    exact Finset.sum_nonneg fun t _ => by unfold discrepancyDeparture; split <;> positivity
  · exact integral_singleAddition_odometer_difference_le hd η v ρ T x

theorem addParticle_update_self (η : Site d → ℤ) (v : Site d) (k : ℤ) :
    addParticle v (Function.update η v k) = Function.update η v (k + 1) := by
  classical
  ext y
  simp [addParticle, Function.update_apply]
  split <;> omega

/-- Raising one coordinate by an integer amount costs at most that many Green functions. -/
theorem matchedMeanU_update_le (hd : 3 ≤ d) (η : Site d → ℤ) (v : Site d)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (k : ℤ) (n : ℕ) :
    0 ≤ matchedMeanU (Function.update η v (k + n)) ρ T x -
        matchedMeanU (Function.update η v k) ρ T x ∧
      matchedMeanU (Function.update η v (k + n)) ρ T x -
        matchedMeanU (Function.update η v k) ρ T x ≤ (n : ℝ) * fullGreen d (v - x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h := matchedMeanU_addParticle hd (Function.update η v (k + n)) v ρ T x
      rw [addParticle_update_self] at h
      push_cast
      rw [← add_assoc]
      constructor <;> nlinarith

/-- The oscillation between two initial values is controlled by their integer distance. -/
theorem matchedMeanU_update_abs_le (hd : 3 ≤ d) (η : Site d → ℤ) (v : Site d)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (a b : ℤ) :
    |matchedMeanU (Function.update η v a) ρ T x - matchedMeanU (Function.update η v b) ρ T x| ≤
      |(a : ℝ) - b| * fullGreen d (v - x) := by
  wlog hab : b ≤ a generalizing a b
  · simpa only [abs_sub_comm] using this b a (le_of_not_ge hab)
  have h := matchedMeanU_update_le hd η v ρ T x b (a - b).toNat
  have he : b + ((a - b).toNat : ℤ) = a := by omega
  rw [he] at h
  rw [abs_of_nonneg h.1, abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr hab)]
  have hcast : ((a - b).toNat : ℝ) = (a : ℝ) - b := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr hab), Int.cast_sub]
  simpa only [hcast] using h.2
end Parking
