import Parking.Support.RoundArrivalMean
import Parking.Support.MatchedCountIntegral
import Parking.Support.LayerIntegral
import Parking.Support.WalkIntegral

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The expected arrivals in a round equal the walk average of the expected active counts. -/
theorem integral_matchedArrivals (hd : 1 ≤ d) (η : Site d → ℤ) (K : ℕ)
    (hη : ∀ y, (η y).toNat ≤ K) (ρ : Label d × ℕ → ℝ) (t : ℕ) (x : Site d) :
    ∫ σ, ((matchedArrivals η ρ σ t x).card : ℝ) ∂(roundNoiseLaw d) =
      walkOp (fun y => ∫ σ, (matchedCount η ρ σ t y : ℝ) ∂(roundNoiseLaw d)) x := by
  haveI := stepLaw_isProbability hd
  haveI := roundNoiseLaw_isProbability hd
  let Q := Measure.infinitePi fun _ : RoundSlot d => stepLaw d
  let F : RoundNoise d → ℝ := fun σ => ((matchedArrivals η ρ σ t x).card : ℝ)
  have hb (σ : RoundNoise d) : ‖F σ‖ ≤ (((2 * (t + 1) + 1) ^ d * K : ℕ) : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact Nat.cast_le.mpr (matchedArrivals_le_box η K hη ρ σ t x)
  have hsec (σ : RoundNoise d) : (∫ τ, F (Function.update σ t τ) ∂Q) =
      walkOp (fun y => (matchedCount η ρ σ t y : ℝ)) x := by
    have heA (τ : RoundSlot d → Fin d × Bool) : matchedCount η ρ (Function.update σ t τ) t =
        matchedCount η ρ σ t := by
      funext y
      unfold matchedCount
      rw [matchedState_update η ρ σ t t τ le_rfl]
    simp only [F, card_matchedArrivals_eq_countArrivals, heA, Function.update_self]
    exact integral_countArrivals hd (matchedCount η ρ σ t) x
  have he := integral_layer_sections Q F (measurable_card_matchedArrivals hd η ρ t x) _ hb t
  simp_rw [hsec] at he
  exact he.trans (integral_walkOp (roundNoiseLaw d) (fun σ y => (matchedCount η ρ σ t y : ℝ)) x
    (fun y _ => integrable_matchedCount_bounded hd η K hη ρ t y _))

/-- Averaged settling preserves the signed balance in each round. -/
theorem integral_matchedSigned_succ (hd : 1 ≤ d) (η : Site d → ℤ) (K : ℕ)
    (hη : ∀ y, (η y).toNat ≤ K) (ρ : Label d × ℕ → ℝ) (t : ℕ) (x : Site d) :
    (∫ σ, (matchedCount η ρ σ (t + 1) x : ℝ) ∂(roundNoiseLaw d)) -
        (∫ σ, ((matchedState η ρ σ (t + 1)).holes x : ℝ) ∂(roundNoiseLaw d)) =
      walkOp (fun y => ∫ σ, (matchedCount η ρ σ t y : ℝ) ∂(roundNoiseLaw d)) x -
        ∫ σ, ((matchedState η ρ σ t).holes x : ℝ) ∂(roundNoiseLaw d) := by
  haveI := roundNoiseLaw_isProbability hd
  rw [← integral_sub (integrable_matchedCount_bounded hd η K hη ρ (t + 1) x _)
    (integrable_matchedHoles hd η ρ (t + 1) x _)]
  have he (σ : RoundNoise d) : (matchedCount η ρ σ (t + 1) x : ℝ) -
      ((matchedState η ρ σ (t + 1)).holes x : ℝ) =
      ((matchedArrivals η ρ σ t x).card : ℝ) - ((matchedState η ρ σ t).holes x : ℝ) := by
    exact_mod_cast matchedSigned_succ η ρ σ t x
  simp_rw [he]
  rw [integral_sub (integrable_matchedArrivals_bounded hd η K hη ρ t x _)
    (integrable_matchedHoles hd η ρ t x _), integral_matchedArrivals hd η K hη ρ t x]

/-- The one-step mean odometer increment is the mean active population. -/
theorem matchedMeanU_succ (hd : 1 ≤ d) (η : Site d → ℤ) (K : ℕ)
    (hη : ∀ y, (η y).toNat ≤ K) (ρ : Label d × ℕ → ℝ) (t : ℕ) (x : Site d) :
    matchedMeanU η ρ (t + 1) x = matchedMeanU η ρ t x +
      ∫ σ, (matchedCount η ρ σ t x : ℝ) ∂(roundNoiseLaw d) := by
  haveI := roundNoiseLaw_isProbability hd
  have he (σ : RoundNoise d) : ((matchedState η ρ σ (t + 1)).departures x : ℝ) =
      ((matchedState η ρ σ t).departures x : ℝ) + (matchedCount η ρ σ t x : ℝ) := Nat.cast_add _ _
  unfold matchedMeanU
  simp_rw [he]
  exact integral_add (integrable_matchedOdometer hd η ρ t x) (integrable_matchedCount_bounded hd η K hη ρ t x _)

/-- Averaging the signed conservation law gives the Poisson equation for the conditional mean odometer. -/
theorem matchedMeanU_signed_balance (hd : 1 ≤ d) (η : Site d → ℤ) (K : ℕ)
    (hη : ∀ y, (η y).toNat ≤ K) (ρ : Label d × ℕ → ℝ) (t : ℕ) (x : Site d) :
    walkOp (matchedMeanU η ρ t) x - matchedMeanU η ρ t x =
      (∫ σ, (matchedCount η ρ σ t x : ℝ) ∂(roundNoiseLaw d)) -
        (∫ σ, ((matchedState η ρ σ t).holes x : ℝ) ∂(roundNoiseLaw d)) - (η x : ℝ) := by
  haveI := roundNoiseLaw_isProbability hd
  induction t with
  | zero =>
      have hm : matchedMeanU η ρ 0 = 0 := by funext y; simp [matchedMeanU, matchedState, initial]
      rw [hm]
      simp only [walkOp, nbrSum, Pi.zero_apply, zero_add, Finset.sum_const_zero, zero_div, sub_self,
        matchedCount_zero, matchedState, initial, integral_const, probReal_univ, one_smul]
      have hi : ((η x).toNat : ℤ) - ((-η x).toNat : ℤ) = η x := by omega
      have hir : ((η x).toNat : ℝ) - ((-η x).toNat : ℝ) = (η x : ℝ) := by exact_mod_cast hi
      linarith
  | succ t ih =>
      have hfun : matchedMeanU η ρ (t + 1) = fun y => matchedMeanU η ρ t y +
          ∫ σ, (matchedCount η ρ σ t y : ℝ) ∂(roundNoiseLaw d) :=
        funext fun y => matchedMeanU_succ hd η K hη ρ t y
      have hwalk (f g : Site d → ℝ) : walkOp (fun y => f y + g y) x = walkOp f x + walkOp g x := by
        simp only [walkOp_eq_nbrFinset, Finset.sum_add_distrib, add_div]
      rw [hfun, hwalk, integral_matchedSigned_succ hd η K hη ρ t x]
      have h := ih
      dsimp only at *
      linarith
end Parking
