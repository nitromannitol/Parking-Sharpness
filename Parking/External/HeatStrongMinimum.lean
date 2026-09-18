/-
The classical strong minimum principle for the heat operator `(2d)⁻¹Δ`, used
in Step 4 of `parking.tex:1785-1805`. A nonnegative smooth classical solution
which vanishes at a point vanishes along every backward vertical segment
through that point contained in its open domain.
-/
import Parking.Support.Continuum

open MeasureTheory

noncomputable section

-- FROZEN-STATEMENT-BEGIN
/-- The strong minimum principle for the heat operator `(2d)^{-1}Δ`, sign-adapted from the
usual strong maximum principle: standard classical parabolic PDE, uncited by the paper
(`parking.tex:1785-1805`, Step 4 of the proof of `prop:spatial-scaling`).  A smooth,
nonnegative classical solution on an open set that vanishes at a point
vanishes on every backward-in-time, space-fixed segment through that point which lies entirely
in the open set. -/
def Parking.External.HeatStrongMinimum : Prop :=
  ∀ (d : ℕ) (U : Set (ℝ × (Fin d → ℝ))), IsOpen U →
    ∀ v : ℝ × (Fin d → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v U →
      (∀ p ∈ U, 0 ≤ v p) →
      (∀ p ∈ U, HasDerivAt (fun s => v (s, p.2))
        (Parking.contOp d (fun x => v (p.1, x)) p.2) p.1) →
      ∀ s₀ : ℝ, ∀ x₀ : Fin d → ℝ, (s₀, x₀) ∈ U → v (s₀, x₀) = 0 →
      ∀ τ : ℝ, τ < s₀ → (Set.Ioc τ s₀ ×ˢ ({x₀} : Set (Fin d → ℝ))) ⊆ U →
      ∀ s ∈ Set.Ioc τ s₀, v (s, x₀) = 0
-- FROZEN-STATEMENT-END

end
