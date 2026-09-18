/-
**The continuum optimal-stopping value `Parking.spatialContValue` is `1`-Lipschitz in its
terminal reward for the supremum norm.** The continuum analogue of
`Parking.abs_stoppingSup_sub_le` (`Parking/Support/ValueLipschitz.lean`), for the `Fin
d`-dimensional Brownian stopping problem (`Parking/Support/ContSpatialValue.lean`).

This is what lets the discrete-to-continuum value transfer go through the extended continuous
mapping theorem (`Parking.Support.ExtendedMapping.extended_continuous_mapping`,
`Parking.Support.tendsto_integral_comp_real_of_lipschitz`) with the LIMIT function
`f : E → ℝ` taken to be `G ↦ spatialContValue B PB G T` on the metric space `E` of
bounded continuous rewards: `f` is `1`-Lipschitz, hence continuous, hence Borel, with NO
separate argument about the measurability of the value as a functional of the sample space
`ΩB`. This is a different matter from the measurability of a directly built
`sSup`-over-stopping-times as a function of the REWARD FIELD's own sample point, once the driving
Brownian randomness has already been integrated out: there the difficulty is that the field
`contZ` has no regularity at all as a function of the field's sample space. That difficulty
does not arise on `E`, the space of REWARDS itself, which is an ordinary metric space with the
sup norm.
-/
import Parking.Support.ContSpatialValue

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace Parking

variable {d : ℕ}

/-- **A bound on the reward, at a bounded, measurable driving process value, gives
integrability of the reward at the rule that stops at once.** Used to supply the
nonemptiness hypothesis `zero_mem_spatialContPayoffs` needs from a global bound on the
reward alone. -/
theorem integrable_stopAtZero_of_bound {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → (Fin d → ℝ)) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (G : ℝ → (Fin d → ℝ) → ℝ) {M : ℝ} (hGb : ∀ s y, |G s y| ≤ M)
    (hBm : Measurable (B 0)) (hGm : Measurable (G 0)) :
    Integrable (fun β => G 0 (B 0 β)) PB := by
  refine Integrable.mono' (integrable_const M) (hGm.comp hBm).aestronglyMeasurable ?_
  filter_upwards with β
  rw [Real.norm_eq_abs]
  exact hGb 0 (B 0 β)

/-- **The set of attainable payoffs at a globally bounded, measurable reward is never
empty.** -/
theorem spatialContPayoffs_nonempty {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → (Fin d → ℝ)) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (G : ℝ → (Fin d → ℝ) → ℝ) {T M : ℝ} (hT : 0 ≤ T)
    (hGb : ∀ s y, |G s y| ≤ M) (hBm : Measurable (B 0)) (hGm : Measurable (G 0)) :
    (spatialContPayoffs B PB G T).Nonempty :=
  ⟨_, zero_mem_spatialContPayoffs B PB G hT
    (integrable_stopAtZero_of_bound B PB G hGb hBm hGm)⟩

/-- **The set of attainable payoffs at a globally bounded reward is bounded above.** -/
theorem bddAbove_spatialContPayoffs {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → (Fin d → ℝ)) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (G : ℝ → (Fin d → ℝ) → ℝ) (T : ℝ) {M : ℝ} (hGb : ∀ s y, G s y ≤ M) :
    BddAbove (spatialContPayoffs B PB G T) := by
  refine ⟨M, ?_⟩
  rintro a ⟨τ, _, _, hint, rfl⟩
  have hmono : (∫ β, G (τ β) (B (τ β) β) ∂PB) ≤ ∫ _β : ΩB, M ∂PB :=
    integral_mono hint (integrable_const M) (fun β => hGb _ _)
  simpa using hmono

/-- **Two admissible payoffs from rewards within `c` of each other are within `c`.** The
Dynkin-style pairwise comparison one level below `abs_spatialContValue_sub_le`. -/
theorem abs_payoff_sub_le {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → (Fin d → ℝ)) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (G G' : ℝ → (Fin d → ℝ) → ℝ) {c : ℝ} (hdiff : ∀ s y, |G s y - G' s y| ≤ c)
    {τ : ΩB → ℝ≥0} (hint : Integrable (fun β => G (τ β) (B (τ β) β)) PB)
    (hint' : Integrable (fun β => G' (τ β) (B (τ β) β)) PB) :
    |(∫ β, G (τ β) (B (τ β) β) ∂PB) - ∫ β, G' (τ β) (B (τ β) β) ∂PB| ≤ c := by
  rw [← integral_sub hint hint']
  calc |∫ β, (G (τ β) (B (τ β) β) - G' (τ β) (B (τ β) β)) ∂PB|
      ≤ ∫ β, |G (τ β) (B (τ β) β) - G' (τ β) (B (τ β) β)| ∂PB := abs_integral_le_integral_abs
    _ ≤ ∫ _β : ΩB, c ∂PB :=
        integral_mono (hint.sub hint').abs (integrable_const c) (fun β => hdiff _ _)
    _ = c := by simp

/-- **`Parking.spatialContValue` is `1`-Lipschitz in its terminal reward for the supremum
norm**, uniformly in the horizon. Transposed from `Parking.abs_stoppingSup_sub_le`
(`Parking/Support/ValueLipschitz.lean`), reading `sSup` in place of the discrete
`sSup`-over-stopping-rules and using that every attainable payoff already carries its own
integrability (`Parking.spatialContPayoffs`'s own definition).

`hcross`/`hcross'` record exactly the one extra fact the discrete proof got for free from
finite dependence (`Parking.integrable_of_finite_dependence`, which has no continuum
analogue on the infinite-dimensional path space `ΩB`): a stopping rule admissible for one
reward is admissible for the other. It holds whenever `G` and `G'` are both, say, jointly
continuous and `τ` is composed with a jointly measurable driving process, which is the
shape every use of this lemma in this repository supplies; it is recorded as a hypothesis
here, not derived, since `IsSpatialContStopping` (Galmarino's criterion) does not by itself
make `τ` measurable. -/
theorem abs_spatialContValue_sub_le {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → (Fin d → ℝ)) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (G G' : ℝ → (Fin d → ℝ) → ℝ) (T : ℝ) {c M : ℝ}
    (hGb : ∀ s y, |G s y| ≤ M) (hG'b : ∀ s y, |G' s y| ≤ M)
    (hdiff : ∀ s y, |G s y - G' s y| ≤ c)
    (hT : 0 ≤ T) (hBm : Measurable (B 0))
    (hGm : Measurable (G 0)) (hG'm : Measurable (G' 0))
    (hcross : ∀ τ : ΩB → ℝ≥0, IsSpatialContStopping B τ → (∀ β, (τ β : ℝ) ≤ T) →
      Integrable (fun β => G (τ β) (B (τ β) β)) PB →
      Integrable (fun β => G' (τ β) (B (τ β) β)) PB)
    (hcross' : ∀ τ : ΩB → ℝ≥0, IsSpatialContStopping B τ → (∀ β, (τ β : ℝ) ≤ T) →
      Integrable (fun β => G' (τ β) (B (τ β) β)) PB →
      Integrable (fun β => G (τ β) (B (τ β) β)) PB) :
    |spatialContValue B PB G T - spatialContValue B PB G' T| ≤ c := by
  have hneG := spatialContPayoffs_nonempty B PB G hT hGb hBm hGm
  have hneG' := spatialContPayoffs_nonempty B PB G' hT hG'b hBm hG'm
  have hbG := bddAbove_spatialContPayoffs B PB G T (fun s y => (abs_le.mp (hGb s y)).2)
  have hbG' := bddAbove_spatialContPayoffs B PB G' T (fun s y => (abs_le.mp (hG'b s y)).2)
  have h1 : spatialContValue B PB G T ≤ spatialContValue B PB G' T + c := by
    refine csSup_le hneG ?_
    rintro a ⟨τ, hτ, hτT, hint, rfl⟩
    have hint' := hcross τ hτ hτT hint
    have h1' : (∫ β, G' (τ β) (B (τ β) β) ∂PB) ≤ spatialContValue B PB G' T :=
      le_csSup hbG' ⟨τ, hτ, hτT, hint', rfl⟩
    have h2' := abs_payoff_sub_le B PB G G' hdiff hint hint'
    have := (abs_sub_le_iff.mp h2').1
    linarith
  have h2 : spatialContValue B PB G' T ≤ spatialContValue B PB G T + c := by
    refine csSup_le hneG' ?_
    rintro a ⟨τ, hτ, hτT, hint, rfl⟩
    have hint' := hcross' τ hτ hτT hint
    have h1' : (∫ β, G (τ β) (B (τ β) β) ∂PB) ≤ spatialContValue B PB G T :=
      le_csSup hbG ⟨τ, hτ, hτT, hint', rfl⟩
    have h2' := abs_payoff_sub_le B PB G' G (fun s y => by rw [abs_sub_comm]; exact hdiff s y)
      hint hint'
    have := (abs_sub_le_iff.mp h2').1
    linarith
  rw [abs_sub_le_iff]
  constructor <;> linarith

end Parking

end
