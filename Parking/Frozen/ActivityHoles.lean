/-
Lemma 3.6 of parking.tex, frozen.  `parking.tex:768-774` (label
`lem:activity-holes`):

  "Let $\eta$ be translation invariant with $\E|\eta(0)|<\infty$.  Then, for
   every $t\geq0$, $\E A_t(0)-\E H_t(0)=\E\eta(0)$."

The configuration law is any translation invariant law on `Z^d`, not only an
i.i.d. one; the stacks and the uniform variables carry their own laws, as in
`dataLaw`.  The finiteness of the two expectations, which the proof establishes
from `A_t(0) ≤ ∑_{|y| ≤ t} η(y)⁺`, is asserted alongside the identity, so that
an undefined integral cannot satisfy it through its junk value.
-/
import Parking.Support.ActivityHoles

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.activity_holes (d : ℕ) (hd : 1 ≤ d)
    (μ : Measure (Parking.Site d → ℤ)) (hprob : IsProbabilityMeasure μ)
    (hti : Parking.TranslationInvariant μ)
    (hint : Integrable (fun η : Parking.Site d → ℤ => |((η 0 : ℤ) : ℝ)|) μ) (t : ℕ) :
    Integrable (fun ω => (Parking.A ω t 0 : ℝ)) (Parking.dataLaw d μ) ∧
      Integrable (fun ω => (Parking.H ω t 0 : ℝ)) (Parking.dataLaw d μ) ∧
      ∫ ω, (Parking.A ω t 0 : ℝ) ∂(Parking.dataLaw d μ)
          - ∫ ω, (Parking.H ω t 0 : ℝ) ∂(Parking.dataLaw d μ)
        = ∫ η, ((η 0 : ℤ) : ℝ) ∂μ
-- FROZEN-STATEMENT-END
:= by
  haveI := hprob
  exact ⟨Parking.integrable_A_data hd hti hint t 0,
    Parking.integrable_H_data hd hti hint t 0,
    Parking.activity_holes_main hd hti hint t⟩
