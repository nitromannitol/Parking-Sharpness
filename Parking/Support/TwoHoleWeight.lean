import Parking.Support.HoleCost
import Parking.Support.LayerSubmartingale

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Each complete round decreases the discounted product of conditional hole means. -/
theorem twoHoleWeight_section (hd : 3 ≤ d) (η : Site d → ℤ) (K : ℕ)
    (hη : ∀ y, (η y).toNat ≤ K) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d)
    (T s : ℕ) (hs : s < T) (x z u : Site d) (R : ℕ)
    (hxR : boxFinset x T ⊆ boxFinset u R) (hzR : boxFinset z T ⊆ boxFinset u R) :
    (∫ τ, twoHoleWeight η ρ (Function.update σ s τ) T (s + 1) x z u R
      ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d)) ≤ twoHoleWeight η ρ σ T s x z u R := by
  have hd1 : 1 ≤ d := by omega
  haveI := stepLaw_isProbability hd1
  let A := matchedCount η ρ σ s
  let H := (matchedState η ρ σ s).holes
  let c := holeCostTotal η ρ σ s x z u R
  let b := (∑ y ∈ boxFinset u R, holeKernel d x z y * (A y : ℝ)) / (1 / (2 * escapeConst d)) ^ 2
  let P := futureHoleValue η ρ σ T s x * futureHoleValue η ρ σ T s z
  have htime : T - s - 1 + 1 ≤ T := by omega
  have hbX := futureHoleValue_bellman hd1 η ρ σ T s hs x
  have hbZ := futureHoleValue_bellman hd1 η ρ σ T s hs z
  simp_rw [futureHoleValue_update_succ] at hbX hbZ
  have hround := round_hole_product_factor hd A H ((2 * s + 1) ^ d * K)
    (matchedCount_le_box η K hη ρ σ s) ρ (T - s - 1) x z u R
    ((boxFinset_mono htime).trans hxR) ((boxFinset_mono htime).trans hzR)
  dsimp only [A, H] at hround
  rw [hbX, hbZ] at hround
  change (∫ τ, matchedMeanH (roundSigned A H τ) ρ (T - s - 1) x *
      matchedMeanH (roundSigned A H τ) ρ (T - s - 1) z
      ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d)) ≤ Real.exp b * P at hround
  simp only [twoHoleWeight, futureHoleValue_update_succ, holeCostTotal_update_succ]
  rw [integral_mul_const]
  change (∫ τ, matchedMeanH (roundSigned A H τ) ρ (T - s - 1) x *
      matchedMeanH (roundSigned A H τ) ρ (T - s - 1) z
      ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d)) * Real.exp (-(c + b)) ≤ P * Real.exp (-c)
  calc
    _ ≤ (Real.exp b * P) * Real.exp (-(c + b)) := mul_le_mul_of_nonneg_right hround (Real.exp_pos _).le
    _ = P * (Real.exp b * Real.exp (-(c + b))) := by ring
    _ = P * Real.exp (b + -(c + b)) := by rw [Real.exp_add]
    _ = P * Real.exp (-c) := by congr 2; ring

/-- Conditional on any bounded initial field, the instruction factor pays for the joint hole event. -/
theorem integral_twoHole_discount_le (hd : 3 ≤ d) (η : Site d → ℤ) (K : ℕ)
    (hη : ∀ y, (η y).toNat ≤ K) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x z u : Site d) (R : ℕ)
    (hxR : boxFinset x T ⊆ boxFinset u R) (hzR : boxFinset z T ⊆ boxFinset u R) :
    (∫ σ, (((matchedState η ρ σ T).holes x : ℝ) * ((matchedState η ρ σ T).holes z : ℝ)) *
      Real.exp (-holeCostTotal η ρ σ T x z u R) ∂(roundNoiseLaw d)) ≤
      matchedMeanH η ρ T x * matchedMeanH η ρ T z := by
  have hd1 : 1 ≤ d := by omega
  haveI := stepLaw_isProbability hd1
  haveI := roundNoiseLaw_isProbability hd1
  let V := fun σ s => -twoHoleWeight η ρ σ T s x z u R
  have hm (s : ℕ) : Measurable (fun σ : RoundNoise d => V σ s) := (measurable_twoHoleWeight hd1 η ρ T s x z u R).neg
  have hb (σ : RoundNoise d) (s : ℕ) : ‖V σ s‖ ≤ ((-η x).toNat : ℝ) * ((-η z).toNat : ℝ) := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (twoHoleWeight_bounds hd η ρ σ T s x z u R).1]
    exact (twoHoleWeight_bounds hd η ρ σ T s x z u R).2
  have hv := layer_submartingale_integral_le (Measure.infinitePi fun _ : RoundSlot d => stepLaw d)
    V hm _ hb T (fun s hs σ => by
      change -twoHoleWeight η ρ σ T s x z u R ≤ ∫ τ, -twoHoleWeight η ρ (Function.update σ s τ) T (s + 1) x z u R ∂_
      rw [integral_neg]
      exact neg_le_neg (twoHoleWeight_section hd η K hη ρ σ T s hs x z u R hxR hzR))
  dsimp only [V] at hv
  rw [integral_neg, integral_neg] at hv
  have h := neg_le_neg_iff.mp hv
  simp only [twoHoleWeight, futureHoleValue_zero, holeCostTotal_zero, neg_zero, Real.exp_zero, mul_one,
    futureHoleValue_terminal hd1, integral_const, probReal_univ, one_smul] at h
  exact h
end Parking
