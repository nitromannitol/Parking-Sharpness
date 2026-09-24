import Parking.Support.InstructionHoleFactor
import Parking.Support.PartialInvariant

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Only used departing entries contribute a two-hole reveal cost. -/
def roundHoleCost (d : ℕ) (A : Site d → ℕ) (x z : Site d) (q : RoundSlot d) : ℝ :=
  match q with
  | Sum.inl (v, j) => if j < A v then holeKernel d x z v / (1 / (2 * escapeConst d)) ^ 2 else 0
  | Sum.inr _ => 0

/-- The unused per-label directions do not affect the next signed field. -/
theorem roundSigned_update_inr (A H : Site d → ℕ) (τ : RoundSlot d → Fin d × Bool)
    (p : Label d) (a : Fin d × Bool) :
    roundSigned A H (Function.update τ (Sum.inr p) a) = roundSigned A H τ := by
  funext y
  simp only [roundSigned, countArrivals, Function.update_of_ne Sum.inl_ne_inr]

/-- An unused coordinate has a constant partial future hole expectation. -/
theorem partial_roundMeanH_update_invariant (A H : Site d → ℕ) (ρ : Label d × ℕ → ℝ)
    (T : ℕ) (x : Site d) (S : Set (RoundSlot d)) [DecidablePred (· ∈ S)] (q : RoundSlot d)
    (hq : ∀ τ a, roundSigned A H (Function.update τ q a) = roundSigned A H τ)
    (τ : RoundSlot d → Fin d × Bool) (a : Fin d × Bool) :
    partialInt (fun _ : RoundSlot d => stepLaw d) S (fun ζ => matchedMeanH (roundSigned A H ζ) ρ T x)
      (Function.update τ q a) =
    partialInt (fun _ : RoundSlot d => stepLaw d) S (fun ζ => matchedMeanH (roundSigned A H ζ) ρ T x) τ := by
  apply partialInt_update_invariant
  intro ζ b
  rw [hq]

/-- Every current entry has its prescribed factor, including the factor one for unused entries. -/
theorem instruction_partial_hole_factor_any (hd : 3 ≤ d) (A H : Site d → ℕ)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x z : Site d) (q : RoundSlot d)
    (S : Set (RoundSlot d)) [DecidablePred (· ∈ S)] (τ : RoundSlot d → Fin d × Bool) :
    let f := fun a : Fin d × Bool => partialInt (fun _ : RoundSlot d => stepLaw d)
      (insert q S) (fun ζ => matchedMeanH (roundSigned A H ζ) ρ T x) (Function.update τ q a)
    let g := fun a : Fin d × Bool => partialInt (fun _ : RoundSlot d => stepLaw d)
      (insert q S) (fun ζ => matchedMeanH (roundSigned A H ζ) ρ T z) (Function.update τ q a)
    (∫ a, f a * g a ∂(stepLaw d)) ≤ Real.exp (roundHoleCost d A x z q) *
      ((∫ a, f a ∂(stepLaw d)) * ∫ a, g a ∂(stepLaw d)) := by
  have hd1 : 1 ≤ d := by omega
  haveI := stepLaw_isProbability hd1
  have hunused (hq : ∀ τ a, roundSigned A H (Function.update τ q a) = roundSigned A H τ)
      (hc : roundHoleCost d A x z q = 0) :
      (∫ a, partialInt (fun _ : RoundSlot d => stepLaw d) (insert q S)
        (fun ζ => matchedMeanH (roundSigned A H ζ) ρ T x) (Function.update τ q a) *
        partialInt (fun _ : RoundSlot d => stepLaw d) (insert q S)
        (fun ζ => matchedMeanH (roundSigned A H ζ) ρ T z) (Function.update τ q a) ∂(stepLaw d)) ≤
      Real.exp (roundHoleCost d A x z q) *
        ((∫ a, partialInt (fun _ : RoundSlot d => stepLaw d) (insert q S)
          (fun ζ => matchedMeanH (roundSigned A H ζ) ρ T x) (Function.update τ q a) ∂(stepLaw d)) *
        ∫ a, partialInt (fun _ : RoundSlot d => stepLaw d) (insert q S)
          (fun ζ => matchedMeanH (roundSigned A H ζ) ρ T z) (Function.update τ q a) ∂(stepLaw d)) := by
    simp only [partial_roundMeanH_update_invariant A H ρ T x (insert q S) q hq,
      partial_roundMeanH_update_invariant A H ρ T z (insert q S) q hq,
      hc, Real.exp_zero, integral_const, probReal_univ, one_smul, one_mul, le_refl]
  cases q with
  | inl q =>
      rcases q with ⟨v, j⟩
      by_cases hj : j < A v
      · simpa only [roundHoleCost, if_pos hj] using instruction_partial_hole_factor hd A H v j hj ρ T x z S τ
      · exact hunused (fun ζ a => roundSigned_update_unused A H ζ v j (Nat.le_of_not_gt hj) a)
          (by simp only [roundHoleCost, if_neg hj])
  | inr p => exact hunused (fun ζ a => roundSigned_update_inr A H ζ p a) rfl

/-- The factor compares the after-reveal product to the before-reveal product pointwise. -/
theorem round_hole_reveal_section (hd : 3 ≤ d) (A H : Site d → ℕ)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x z : Site d) (S : Finset (RoundSlot d))
    (q : RoundSlot d) (hq : q ∉ S) (τ : RoundSlot d → Fin d × Bool) :
    (∫ a, partialInt (fun _ : RoundSlot d => stepLaw d) (↑(insert q S) : Set (RoundSlot d))
      (fun ζ => matchedMeanH (roundSigned A H ζ) ρ T x) (Function.update τ q a) *
      partialInt (fun _ : RoundSlot d => stepLaw d) (↑(insert q S) : Set (RoundSlot d))
      (fun ζ => matchedMeanH (roundSigned A H ζ) ρ T z) (Function.update τ q a) ∂(stepLaw d)) ≤
      Real.exp (roundHoleCost d A x z q) *
        (partialInt (fun _ : RoundSlot d => stepLaw d) (↑S : Set (RoundSlot d))
          (fun ζ => matchedMeanH (roundSigned A H ζ) ρ T x) τ *
        partialInt (fun _ : RoundSlot d => stepLaw d) (↑S : Set (RoundSlot d))
          (fun ζ => matchedMeanH (roundSigned A H ζ) ρ T z) τ) := by
  classical
  have hd1 : 1 ≤ d := by omega
  haveI := stepLaw_isProbability hd1
  have hm (v : Site d) : Measurable (fun ζ : RoundSlot d → Fin d × Bool => matchedMeanH (roundSigned A H ζ) ρ T v) :=
    (measurable_matchedMeanH hd1 ρ T v).comp
      (measurable_roundSigned (fun _ => A) (fun _ => H) id measurable_const measurable_const measurable_id)
  have he (v : Site d) := partialInt_insert_coordinate (fun _ : RoundSlot d => stepLaw d)
    (↑S : Set (RoundSlot d)) q hq (fun ζ => matchedMeanH (roundSigned A H ζ) ρ T v)
    (hm v) (H v : ℝ) (roundMeanH_bound hd1 A H ρ T v) τ
  have h := instruction_partial_hole_factor_any hd A H ρ T x z q (↑S : Set (RoundSlot d)) τ
  dsimp only at h
  rw [← he x, ← he z] at h
  simpa only [Finset.coe_insert] using h
end Parking
