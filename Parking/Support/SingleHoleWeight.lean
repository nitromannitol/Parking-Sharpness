import Parking.Support.FutureHole
import Parking.Support.SingleFreshSlot
import Parking.Support.EscapePotential
import Parking.Support.CoordinateFactor

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The base future hole count weighted by the unique discrepancy's escape probability. -/
def singleHoleWeight (η : Site d → ℤ) (v : Site d) (ρ : Label d × ℕ → ℝ)
    (σ : RoundNoise d) (T s : ℕ) (x : Site d) : ℝ :=
  futureHoleValue η ρ σ T s x *
    escapePotential d x ((discrepancyState (singleAdditionPair η v) ρ σ s).pos (v, 0))

theorem singleHoleWeight_bounds (hd : 3 ≤ d) (η : Site d → ℤ) (v : Site d)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (T s : ℕ) (x : Site d) :
    0 ≤ singleHoleWeight η v ρ σ T s x ∧ singleHoleWeight η v ρ σ T s x ≤ ((-η x).toNat : ℝ) := by
  have hF := futureHoleValue_bounds (by omega : 1 ≤ d) η ρ σ T s x
  have hE := escapePotential_bounds hd x ((discrepancyState (singleAdditionPair η v) ρ σ s).pos (v, 0))
  exact ⟨mul_nonneg hF.1 hE.1, (mul_le_of_le_one_right hF.1 hE.2).trans hF.2⟩

theorem measurable_singleHoleWeight (hd : 3 ≤ d) (η : Site d → ℤ) (v : Site d)
    (ρ : Label d × ℕ → ℝ) (T s : ℕ) (x : Site d) :
    Measurable (fun σ : RoundNoise d => singleHoleWeight η v ρ σ T s x) := by
  have hS := measurableState_discrepancyState ⟨0, by omega⟩ (fun _ : RoundNoise d => singleAdditionPair η v)
    (fun _ => ρ) id measurable_const measurable_const measurable_id s
  exact (measurable_futureHoleValue (by omega) η ρ T s x).mul
    ((measurable_from_countable' (escapePotential d x)).comp (hS.2.1 (v, 0)))

/-- The fresh surplus instruction is independent of the base process's future hole probability. -/
theorem singleHoleWeight_section_ge (hd : 3 ≤ d) (η : Site d → ℤ) (v : Site d)
    (ρ : Label d × ℕ → ℝ) (σ : RoundNoise d) (T s : ℕ) (hs : s < T) (x : Site d) :
    singleHoleWeight η v ρ σ T s x ≤
      ∫ τ, singleHoleWeight η v ρ (Function.update σ s τ) T (s + 1) x
        ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d) := by
  classical
  have hd1 : 1 ≤ d := by omega
  haveI := stepLaw_isProbability hd1
  let c := singleAdditionPair η v
  let y := (discrepancyState c ρ σ s).pos (v, 0)
  let q := discrepancyIndex c ρ σ s (v, 0)
  let F : (RoundSlot d → Fin d × Bool) → ℝ := fun τ => futureHoleValue η ρ (Function.update σ s τ) T (s + 1) x
  have hF : Measurable F := (measurable_futureHoleValue hd1 η ρ T (s + 1) x).comp (measurable_update σ)
  have hFB : (∫ τ, F τ ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d)) = futureHoleValue η ρ σ T s x :=
    futureHoleValue_bellman hd1 η ρ σ T s hs x
  unfold singleHoleWeight
  simp_rw [discrepancyPosition_update_succ]
  by_cases hm : discrepancyDoesMove c ρ σ s (v, 0) = true
  · obtain ⟨j, hj, hq⟩ := singleAddition_index_unused η v ρ σ s hm
    let b : Fin d × Bool := (⟨0, by omega⟩, true)
    have hinv (τ : RoundSlot d → Fin d × Bool) : F (Function.update τ q b) = F τ := by
      dsimp only [F, q, c]
      rw [hq, futureHoleValue_update_succ, futureHoleValue_update_succ,
        roundSigned_update_unused _ _ _ _ _ hj]
    have hfactor := integral_mul_coordinate_of_update_invariant (fun _ : RoundSlot d => stepLaw d) q b F hF hinv
      (fun a => escapePotential d x (y + stepVec a)) (measurable_from_countable' _)
    change futureHoleValue η ρ σ T s x * escapePotential d x y ≤
      ∫ τ, F τ * escapePotential d x (if discrepancyDoesMove c ρ σ s (v, 0) then
        y + stepVec (τ q) else y) ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d)
    simp only [hm, ↓reduceIte]
    rw [hfactor, hFB]
    exact mul_le_mul_of_nonneg_left (integral_step_escapePotential_ge hd x y)
      (futureHoleValue_bounds hd1 η ρ σ T s x).1
  · change futureHoleValue η ρ σ T s x * escapePotential d x y ≤
      ∫ τ, F τ * escapePotential d x (if discrepancyDoesMove c ρ σ s (v, 0) then
        y + stepVec (τ q) else y) ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d)
    simp only [if_neg hm]
    rw [integral_mul_const, hFB]
end Parking
