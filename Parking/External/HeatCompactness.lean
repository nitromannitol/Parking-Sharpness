/-
Local compactness of nonnegative classical heat solutions, used in Step 3 of
`parking.tex:1785-1805`. Standard parabolic interior estimates bound every
derivative on a compact subset by a local `L¹` norm on a larger compact subset.
A diagonal subsequence therefore converges smoothly on compact subsets. The
form below records the locally uniform convergence and smooth classical limit
needed to identify the derivative of a continuous primitive.
-/
import Parking.Support.Continuum
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

open MeasureTheory Filter Topology

noncomputable section

-- FROZEN-STATEMENT-BEGIN
/-- Classical parabolic compactness for `(2d)⁻¹Δ`: a sequence of nonnegative smooth
heat solutions with uniformly bounded local `L¹` norms has a subsequence converging
locally uniformly to a smooth classical heat solution. This is the compactness
consequence of standard parabolic interior derivative estimates used in
`parking.tex:1785-1805`, Step 3 of `prop:spatial-scaling`. -/
def Parking.External.HeatCompactness : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (U : Set (ℝ × (Fin d → ℝ))), IsOpen U →
    ∀ f : ℕ → ℝ × (Fin d → ℝ) → ℝ,
      (∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (f n) U) →
      (∀ n p, p ∈ U → 0 ≤ f n p) →
      (∀ n p, p ∈ U → HasDerivAt (fun s => f n (s, p.2))
        (Parking.contOp d (fun x => f n (p.1, x)) p.2) p.1) →
      (∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → K ⊆ U →
        ∃ C : ℝ, ∀ n, IntegrableOn (f n) K ∧ (∫ p in K, ‖f n p‖) ≤ C) →
      ∃ (r : ℕ → ℕ) (v : ℝ × (Fin d → ℝ) → ℝ), StrictMono r ∧
        ContDiffOn ℝ (⊤ : ℕ∞) v U ∧
        (∀ p ∈ U, 0 ≤ v p) ∧
        (∀ p ∈ U, HasDerivAt (fun s => v (s, p.2))
          (Parking.contOp d (fun x => v (p.1, x)) p.2) p.1) ∧
        (∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → K ⊆ U →
          TendstoUniformlyOn (fun n => f (r n)) v atTop K)
-- FROZEN-STATEMENT-END

end
