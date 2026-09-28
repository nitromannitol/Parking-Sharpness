import Parking.Support.RoundHoleFactor
import Parking.Support.FutureHole

/-!
# The instruction cost charged against a pair of future-hole events

`holeCostTotal` accumulates, over a finite propagation box `boxFinset u R`, the instructions
already spent (`departures`) at each site weighted by the hole kernel between two sites `x`
and `z`; `twoHoleWeight` is the product of the two conditional future-hole values at `x` and
`z`, discounted by `Real.exp` of that accumulated cost. This module establishes the basic
nonnegativity, vanishing at time `0`, measurability, one-step update, and upper bound
properties these two quantities need.
-/

open LatticeProb (measurable_from_countable')

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Accumulated instruction cost in a finite propagation box. -/
def holeCostTotal (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d)
    (s : ℕ) (x z u : Site d) (R : ℕ) : ℝ :=
  (∑ y ∈ boxFinset u R, holeKernel d x z y * ((matchedState η ρ σ s).departures y : ℝ)) /
    (1 / (2 * escapeConst d)) ^ 2

/-- The accumulated cost is nonnegative, since it sums nonnegative kernel-weighted departure
counts and divides by a square. -/
theorem holeCostTotal_nonneg (hd : 3 ≤ d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (s : ℕ) (x z u : Site d) (R : ℕ) : 0 ≤ holeCostTotal η ρ σ s x z u R :=
  div_nonneg (Finset.sum_nonneg fun y _ => mul_nonneg (holeKernel_nonneg hd x z y)
      (Nat.cast_nonneg _)) (sq_nonneg _)

/-- At time `0` no departures have occurred, so the accumulated cost is zero. -/
theorem holeCostTotal_zero (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (x z u : Site d) (R : ℕ) : holeCostTotal η ρ σ 0 x z u R = 0 := by
  simp [holeCostTotal, matchedState, initial]

/-- `holeCostTotal`, as a function of the round noise `σ` alone, is measurable, via the
measurability of `matchedState`'s departure counts. -/
theorem measurable_holeCostTotal (hd : 1 ≤ d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (s : ℕ) (x z u : Site d) (R : ℕ) :
        Measurable (fun σ : RoundNoise d => holeCostTotal η ρ σ s x z u R) := by
  have hS := measurableState_matchedState ⟨0, hd⟩ (fun _ : RoundNoise d => η) (fun _ => ρ) id
    measurable_const measurable_const measurable_id s
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro y _
  exact ((measurable_from_countable' fun n : ℕ => (n : ℝ)).comp (hS.2.2.2 y)).const_mul _

/-- The next cost increment is already determined by the outgoing active counts. -/
theorem holeCostTotal_update_succ (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (s : ℕ) (x z u : Site d) (R : ℕ) (τ : RoundSlot d → Fin d × Bool) :
    holeCostTotal η ρ (Function.update σ s τ) (s + 1) x z u R = holeCostTotal η ρ σ s x z u R +
      (∑ y ∈ boxFinset u R, holeKernel d x z y * (matchedCount η ρ σ s y : ℝ)) /
        (1 / (2 * escapeConst d)) ^ 2 := by
  have hs : ∀ y : Site d, ((matchedState η ρ (Function.update σ s τ) (s + 1)).departures y : ℝ) =
      ((matchedState η ρ σ s).departures y : ℝ) + (matchedCount η ρ σ s y : ℝ) := by
    intro y
    change (((matchedState η ρ (Function.update σ s τ) s).departures y +
      matchedCount η ρ (Function.update σ s τ) s y : ℕ) : ℝ) = _
    rw [matchedState_update _ _ _ _ _ _ le_rfl, matchedCount_update _ _ _ _ _ _ le_rfl,
      Nat.cast_add]
  simp only [holeCostTotal, hs, mul_add, Finset.sum_add_distrib, add_div]

/-- The product of the two conditional hole means, discounted by the instructions already used. -/
def twoHoleWeight (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d)
    (T s : ℕ) (x z u : Site d) (R : ℕ) : ℝ :=
  (futureHoleValue η ρ σ T s x * futureHoleValue η ρ σ T s z) *
    Real.exp (-holeCostTotal η ρ σ s x z u R)

/-- `twoHoleWeight` is nonnegative and bounded above by the product of the two initial hole
sizes `(-η x).toNat` and `(-η z).toNat`, since each `futureHoleValue` factor is so bounded and
the exponential discount is at most one. -/
theorem twoHoleWeight_bounds (hd : 3 ≤ d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (T s : ℕ) (x z u : Site d) (R : ℕ) :
    0 ≤ twoHoleWeight η ρ σ T s x z u R ∧
      twoHoleWeight η ρ σ T s x z u R ≤ ((-η x).toNat : ℝ) * ((-η z).toNat : ℝ) := by
  have hd1 : 1 ≤ d := by omega
  have hx := futureHoleValue_bounds hd1 η ρ σ T s x
  have hz := futureHoleValue_bounds hd1 η ρ σ T s z
  have hc : Real.exp (-holeCostTotal η ρ σ s x z u R) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (holeCostTotal_nonneg hd η ρ σ s x z u R))
  constructor
  · exact mul_nonneg (mul_nonneg hx.1 hz.1) (Real.exp_pos _).le
  · apply (mul_le_mul_of_nonneg_right (mul_le_mul hx.2 hz.2 hz.1 (Nat.cast_nonneg _))
      (Real.exp_pos _).le).trans
    exact (mul_le_mul_of_nonneg_left hc
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans_eq (mul_one _)

/-- `twoHoleWeight` is measurable in the round noise `σ`, as a product of the measurable
`futureHoleValue` factors and the measurable exponential of the negated cost. -/
theorem measurable_twoHoleWeight (hd : 1 ≤ d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (T s : ℕ) (x z u : Site d) (R : ℕ) :
        Measurable (fun σ : RoundNoise d => twoHoleWeight η ρ σ T s x z u R) :=
  ((measurable_futureHoleValue hd η ρ T s x).mul (measurable_futureHoleValue hd η ρ T s z)).mul
    (Real.measurable_exp.comp (measurable_holeCostTotal hd η ρ s x z u R).neg)
end Parking
