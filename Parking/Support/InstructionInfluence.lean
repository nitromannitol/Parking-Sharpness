import Parking.Support.CenteredVariance
import Parking.Support.InstructionField
import Parking.Support.SingleMean

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- With every other instruction of the round fixed, the future mean lies above a common background
by at most the Green function of this instruction's destination. -/
theorem instruction_future_influence (hd : 3 ≤ d) (A H : Site d → ℕ)
    (τ : RoundSlot d → Fin d × Bool) (v : Site d) (j : ℕ) (hj : j < A v)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (a : Fin d × Bool) :
    0 ≤ matchedMeanU (roundSigned A H (Function.update τ (Sum.inl (v, j)) a)) ρ T x -
        matchedMeanU (roundWithout A H τ v j) ρ T x ∧
      matchedMeanU (roundSigned A H (Function.update τ (Sum.inl (v, j)) a)) ρ T x -
        matchedMeanU (roundWithout A H τ v j) ρ T x ≤ fullGreen d (v + stepVec a - x) := by
  rw [roundSigned_eq_addParticle _ _ _ _ _ hj, Function.update_self, roundWithout_update]
  exact matchedMeanU_addParticle hd (roundWithout A H τ v j) (v + stepVec a) ρ T x

/-- One instruction has a centered increment bounded by G(0), with variance bounded by PG². -/
theorem instruction_future_centered_bounds (hd : 3 ≤ d) (A H : Site d → ℕ)
    (τ : RoundSlot d → Fin d × Bool) (v : Site d) (j : ℕ) (hj : j < A v)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) :
    let f := fun a : Fin d × Bool => matchedMeanU
      (roundSigned A H (Function.update τ (Sum.inl (v, j)) a)) ρ T x
    (∀ a, |f a - ∫ b, f b ∂(stepLaw d)| ≤ escapeConst d) ∧
      (∫ a, (f a - ∫ b, f b ∂(stepLaw d)) ^ 2 ∂(stepLaw d)) ≤
        walkOp (fun y => fullGreen d (y - x) ^ 2) v := by
  dsimp only
  haveI := stepLaw_isProbability (by omega : 1 ≤ d)
  have h := centered_influence_bounds (stepLaw d)
    (fun a => matchedMeanU (roundSigned A H (Function.update τ (Sum.inl (v, j)) a)) ρ T x)
    (fun a => fullGreen d (v + stepVec a - x))
    (matchedMeanU (roundWithout A H τ v j) ρ T x) (escapeConst d)
    (measurable_from_countable' _) (measurable_from_countable' _) (fun a =>
      ⟨(instruction_future_influence hd A H τ v j hj ρ T x a).1,
        (instruction_future_influence hd A H τ v j hj ρ T x a).2,
        fullGreen_le_escapeConst hd _⟩)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  exact integral_stepLaw_add (by omega) (fun y => fullGreen d (y - x) ^ 2) v
end Parking
