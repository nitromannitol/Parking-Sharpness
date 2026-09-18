import Parking.Support.InstructionHole
import Parking.Support.HoleKernel
import Parking.Support.DeficitFactor

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Two direction-dependent relative survival bounds control the product of their means. -/
theorem integral_hole_factor (hd : 3 ≤ d) (x z v : Site d)
    (f g : Fin d × Bool → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ a, escapePotential d x (v + stepVec a) * A ≤ f a ∧ f a ≤ A)
    (hg : ∀ a, escapePotential d z (v + stepVec a) * B ≤ g a ∧ g a ≤ B) :
    (∫ a, f a * g a ∂(stepLaw d)) ≤
      Real.exp (holeKernel d x z v / (1 / (2 * escapeConst d)) ^ 2) *
        ((∫ a, f a ∂(stepLaw d)) * ∫ a, g a ∂(stepLaw d)) := by
  have hd1 : 1 ≤ d := by omega
  haveI := stepLaw_isProbability hd1
  let δ : ℝ := 1 / (2 * escapeConst d)
  have hδ : 0 < δ := by
    dsimp only [δ]
    have hG : 0 < escapeConst d := zero_lt_one.trans_le (one_le_escapeConst hd)
    positivity
  have hfn (a) : 0 ≤ f a := (mul_nonneg (escapePotential_bounds hd x _).1 hA).trans (hf a).1
  have hgn (a) : 0 ≤ g a := (mul_nonneg (escapePotential_bounds hd z _).1 hB).trans (hg a).1
  have hMF : δ * A ≤ ∫ a, f a ∂(stepLaw d) := by
    calc
      δ * A ≤ (∫ a, escapePotential d x (v + stepVec a) ∂(stepLaw d)) * A :=
        mul_le_mul_of_nonneg_right (integral_step_escapePotential_gap hd x v) hA
      _ = ∫ a, escapePotential d x (v + stepVec a) * A ∂(stepLaw d) := (integral_mul_const _ _).symm
      _ ≤ ∫ a, f a ∂(stepLaw d) := integral_mono (integrable_step_fun hd1 _) (integrable_step_fun hd1 _) (fun a => (hf a).1)
  have hMG : δ * B ≤ ∫ a, g a ∂(stepLaw d) := by
    calc
      δ * B ≤ (∫ a, escapePotential d z (v + stepVec a) ∂(stepLaw d)) * B :=
        mul_le_mul_of_nonneg_right (integral_step_escapePotential_gap hd z v) hB
      _ = ∫ a, escapePotential d z (v + stepVec a) * B ∂(stepLaw d) := (integral_mul_const _ _).symm
      _ ≤ ∫ a, g a ∂(stepLaw d) := integral_mono (integrable_step_fun hd1 _) (integrable_step_fun hd1 _) (fun a => (hg a).1)
  apply integral_mul_factor_of_deficits (stepLaw d) f g (measurable_from_countable' _) (measurable_from_countable' _)
    A B δ (holeKernel d x z v) hA hB hδ (holeKernel_nonneg hd x z v)
    (fun a => ⟨hfn a, (hf a).2⟩) (fun a => ⟨hgn a, (hg a).2⟩) hMF hMG
  have hp (a : Fin d × Bool) : (A - f a) * (B - g a) ≤
      ((1 - escapePotential d x (v + stepVec a)) * (1 - escapePotential d z (v + stepVec a))) * (A * B) := by
    have ha : A - f a ≤ (1 - escapePotential d x (v + stepVec a)) * A := by linarith [(hf a).1]
    have hb : B - g a ≤ (1 - escapePotential d z (v + stepVec a)) * B := by linarith [(hg a).1]
    exact (mul_le_mul ha hb (sub_nonneg.mpr (hg a).2)
      (mul_nonneg (sub_nonneg.mpr (escapePotential_bounds hd x _).2) hA)).trans_eq (by ring)
  have hi := integral_mono (integrable_step_fun hd1 _) (integrable_step_fun hd1 _) hp
  rw [integral_mul_const] at hi
  exact hi

/-- The multiplicative instruction factor is valid after every finite partial reveal. -/
theorem instruction_partial_hole_factor (hd : 3 ≤ d) (A H : Site d → ℕ)
    (v : Site d) (j : ℕ) (hj : j < A v) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x z : Site d)
    (S : Set (RoundSlot d)) [DecidablePred (· ∈ S)] (τ : RoundSlot d → Fin d × Bool) :
    let f := fun a : Fin d × Bool => partialInt (fun _ : RoundSlot d => stepLaw d)
      (insert (Sum.inl (v, j)) S) (fun ζ => matchedMeanH (roundSigned A H ζ) ρ T x)
        (Function.update τ (Sum.inl (v, j)) a)
    let g := fun a : Fin d × Bool => partialInt (fun _ : RoundSlot d => stepLaw d)
      (insert (Sum.inl (v, j)) S) (fun ζ => matchedMeanH (roundSigned A H ζ) ρ T z)
        (Function.update τ (Sum.inl (v, j)) a)
    (∫ a, f a * g a ∂(stepLaw d)) ≤
      Real.exp (holeKernel d x z v / (1 / (2 * escapeConst d)) ^ 2) *
        ((∫ a, f a ∂(stepLaw d)) * ∫ a, g a ∂(stepLaw d)) := by
  obtain ⟨b, hb, hf⟩ := instruction_partial_hole_relative hd A H v j hj ρ T x S τ
  obtain ⟨c, hc, hg⟩ := instruction_partial_hole_relative hd A H v j hj ρ T z S τ
  exact integral_hole_factor hd x z v _ _ b c hb hc hf hg
end Parking
