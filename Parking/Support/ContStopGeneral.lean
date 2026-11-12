import LatticeProb.ContinuumStoppingBounds
import Parking.Support.ContOrientedLimit
import LatticeProb.ContinuumStoppingValue
import Parking.Support.ContSpatialValue

/-!
# The Brownian optimal-stopping value at a general reward

The cited stability estimates are about a general bounded reward `G : ℝ → ℝ → ℝ`, with the
elapsed time as its first argument.  `Parking.contValue B PB G T` is the value
`sup_{τ≤T} E_0 G(τ, B_τ)` of a real-valued driving process `B`, the supremum running over the
stopping times of the natural filtration of `B` (`Parking.IsNaturalStopping`), the class of
rules of the cited optimal-stopping literature.

The value is an `sSup` over the reals of the attainable payoffs; the rule that stops at once is
admissible, so the set is never empty, and a bound on the reward bounds the value.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- The payoffs `E_0 G(τ, B_τ)` attained by the stopping times of the natural filtration of `B`
bounded by `T`.  The first argument of `G` is the elapsed time.

The payoff of a rule counts only when it is integrable: the definition conjoins integrability,
so that no rule contributes the junk value of a Bochner integral. -/
def contPayoffs {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB)
    (G : ℝ → ℝ → ℝ) (T : ℝ) : Set ℝ :=
  {a : ℝ | ∃ τ : ΩB → ℝ≥0, IsNaturalStopping B τ ∧ (∀ β, (τ β : ℝ) ≤ T) ∧
    Integrable (fun β => G (τ β) (B (τ β) β)) PB ∧
    a = ∫ β, G (τ β) (B (τ β) β) ∂PB}

/-- `sup_{τ ≤ T} E_0 G(τ, B_τ)`, the Brownian optimal-stopping value at the reward `G`, over the
stopping times of the natural filtration of `B`. -/
def contValue {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ) (PB : Measure ΩB)
    (G : ℝ → ℝ → ℝ) (T : ℝ) : ℝ :=
  sSup (contPayoffs B PB G T)

/-- The stopping time `0` is admissible, so the set of attainable payoffs is never empty,
whenever the reward at time `0` is integrable. -/
theorem zero_mem_contPayoffs {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ)
    (PB : Measure ΩB) (G : ℝ → ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hint : Integrable (fun β => G 0 (B 0 β)) PB) :
    (∫ β, G 0 (B 0 β) ∂PB) ∈ contPayoffs B PB G T := by
  refine ⟨fun _ => 0, isNaturalStopping_const B 0, fun _ => ?_, ?_, ?_⟩
  · simpa using hT
  · simpa using hint
  · simp

/-- A bound on the reward bounds the value. -/
theorem contValue_le {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ)
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (G : ℝ → ℝ → ℝ) (T : ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ s y : ℝ, G s y ≤ M) :
    contValue B PB G T ≤ M := by
  refine Real.sSup_le (fun a ha => ?_) hM
  obtain ⟨τ, _, _, hint, rfl⟩ := ha
  have hmono : (∫ β, G (τ β) (B (τ β) β) ∂PB) ≤ ∫ _β : ΩB, M ∂PB :=
    integral_mono hint (integrable_const M) (fun β => hbound _ _)
  simpa using hmono

/-- Every attainable payoff is at most the value, once the reward is bounded. -/
theorem le_contValue {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ)
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (G : ℝ → ℝ → ℝ) (T : ℝ)
    {M : ℝ} (hbound : ∀ s y : ℝ, G s y ≤ M) {a : ℝ} (ha : a ∈ contPayoffs B PB G T) :
    a ≤ contValue B PB G T := by
  refine le_csSup ⟨M, ?_⟩ ha
  rintro b ⟨τ, _, _, hint, rfl⟩
  have hmono : (∫ β, G (τ β) (B (τ β) β) ∂PB) ≤ ∫ _β : ΩB, M ∂PB :=
    integral_mono hint (integrable_const M) (fun β => hbound _ _)
  simpa using hmono

end Parking

end
