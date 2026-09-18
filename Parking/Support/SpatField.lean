/-
The rescaled divisible odometer `Parking.barDivisible`, read as a multi-parameter
process on a compact box of positive times: the object the Kolmogorov-Chentsov
route to the third (equicontinuity) clause of `prop:spatial-scaling` runs on.

`Parking.barDivisible` and its measurability (`Parking.measurable_barDivisible`)
and boundedness on a compact set (`Parking.exists_bound_on_compact`) are already
in `Parking/Support/Continuum.lean` and `Parking/Support/NearestBallEvent.lean`;
what is added here is the assembly into `ProbabilityTheory.IsKolmogorovProcess`
at a fixed rescaling `R`, given a uniform increment moment bound, and the
restriction of the field's domain to a compact set of positive times, which is
what the frozen clause quantifies over.
-/
import Parking.Support.NearestBallEvent
import Mathlib.Probability.Process.Kolmogorov

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {d : ℕ}

/-- **The rescaled divisible odometer's potential part, at a fixed scale `R`, as a
process indexed by space-time `ℝ × (Fin d → ℝ)`.** -/
def spatField (d : ℕ) (R : ℝ) (p : ℝ × (Fin d → ℝ)) (w : Data d) : ℝ :=
  barDivisible w R p.1 p.2

theorem spatField_apply (R : ℝ) (s : ℝ) (x : Fin d → ℝ) (w : Data d) :
    spatField d R (s, x) w = barDivisible w R s x := rfl

/-- **Each fixed-point reading of `spatField` is measurable.** -/
theorem measurable_spatField (R : ℝ) (p : ℝ × (Fin d → ℝ)) :
    Measurable (spatField d R p) :=
  measurable_barDivisible R p.1 p.2

/-- **`spatField` at a fixed scale `R` is a Kolmogorov process**, given a uniform
moment bound on its increments: assembled from plain pointwise measurability by
`ProbabilityTheory.IsKolmogorovProcess.mk_of_secondCountableTopology`, since `ℝ`
is second countable. -/
theorem isKolmogorovProcess_spatField (R : ℝ) (ν : Measure (Data d)) [IsProbabilityMeasure ν]
    {p q : ℝ} {M : ℝ≥0} (hp : 0 < p) (hq : 0 < q)
    (hbound : ∀ u v : ℝ × (Fin d → ℝ),
      ∫⁻ w, edist (spatField d R u w) (spatField d R v w) ^ p ∂ν ≤ M * edist u v ^ q) :
    ProbabilityTheory.IsKolmogorovProcess (spatField d R) ν p q M :=
  ProbabilityTheory.IsKolmogorovProcess.mk_of_secondCountableTopology
    (fun u => measurable_spatField R u) hbound hp hq

/-- **`spatField` is bounded on every compact set of space-time**, uniformly in the
sample, for each fixed scale `R`: the field reads only finitely many lattice
points there. -/
theorem exists_bound_spatField (hd : 1 ≤ d) (w : Data d) {R : ℝ} (hR : 0 ≤ R)
    (K : Set (ℝ × (Fin d → ℝ))) (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ K, |spatField d R p w| ≤ B := by
  obtain ⟨B, hB, hbd, _⟩ := exists_bound_on_compact hd w hR K hK
  exact ⟨B, hB, fun p hp => hbd p hp⟩

end Parking
end
