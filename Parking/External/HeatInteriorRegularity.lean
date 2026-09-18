/-
Classical interior regularity for the heat operator `(2d)⁻¹Δ` on open subsets
of positive space-time, used in Step 3 of `parking.tex:1785-1805`. A continuous
weak solution has a smooth representative which agrees with it pointwise and
solves the equation classically.
-/
import Parking.Support.Continuum

open MeasureTheory

noncomputable section

-- FROZEN-STATEMENT-BEGIN
/-- The hypoelliptic (Weyl-type) interior regularity theorem for the heat operator
`(2d)^{-1}Δ`: standard classical parabolic PDE, uncited by the paper (`parking.tex:1785-1805`,
Step 3 of the proof of `prop:spatial-scaling`).  A continuous function
that solves `∂_s u = (2d)^{-1}Δu` in the sense of distributions on an open set, tested against
every space-time test function supported there, is represented on that set by a function smooth
there and solving the equation classically. -/
def Parking.External.HeatInteriorRegularity : Prop :=
  ∀ (d : ℕ) (U : Set (ℝ × (Fin d → ℝ))), IsOpen U →
    U ⊆ {p : ℝ × (Fin d → ℝ) | 0 < p.1} →
    ∀ u : ℝ × (Fin d → ℝ) → ℝ, Continuous u →
      (∀ ψ : ℝ × (Fin d → ℝ) → ℝ, Parking.IsSpaceTimeTest ψ → tsupport ψ ⊆ U →
        -∫ p : ℝ × (Fin d → ℝ), u p * deriv (fun s => ψ (s, p.2)) p.1
          = ∫ p : ℝ × (Fin d → ℝ), u p * Parking.contOp d (fun x => ψ (p.1, x)) p.2) →
      ∃ v : ℝ × (Fin d → ℝ) → ℝ,
        ContDiffOn ℝ (⊤ : ℕ∞) v U ∧
        (∀ p ∈ U, u p = v p) ∧
        (∀ p ∈ U, HasDerivAt (fun s => v (s, p.2))
          (Parking.contOp d (fun x => v (p.1, x)) p.2) p.1)
-- FROZEN-STATEMENT-END

end
