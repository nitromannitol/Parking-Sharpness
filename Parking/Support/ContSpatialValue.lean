/-
The `Fin d`-dimensional Brownian optimal-stopping value, generalizing
`Parking.contValue`/`Parking.contPayoffs` (`Parking/Support/ContStopGeneral.lean`, built for
the ORIENTED walk's one-real-dimensional driving process) to a `(Fin d → ℝ)`-valued driving
process, for the UNDIRECTED (spatial) node `prop:spatial-scaling`.

The shared library now carries a genuine `Fin d`-dimensional Brownian motion,
`LatticeProb.IsBrownianSpace d x B P` (`../Lattice-Probability-clean/LatticeProb/Prob/
BrownianExit.lean`, built exactly as a product of `d` independent one-dimensional Brownian
motions, with generator `Δ/(2d)`, matching `parking.tex`'s `L = (2d)^{-1}Δ`), and
`LatticeProb.exists_isBrownianSpace_cont` proves one exists with every path continuous.  Its
driving space is `EuclideanSpace ℝ (Fin d)` (so that its norm is the one the paper's Brownian
motion needs); `Parking.Support.Continuum`'s own frozen vocabulary for `prop:spatial-scaling`
is `Fin d → ℝ`, the plain Pi type, so a stopping problem in the paper's own vocabulary is
recorded here for a general `(Fin d → ℝ)`-valued driving process, to be applied at
`fun t ω => (EuclideanSpace.equiv (Fin d) ℝ) (B t ω)` for a `LatticeProb.IsBrownianSpace`.

As everywhere in the repository, a stopping time is recorded by Galmarino's criterion, and
the value is an `sSup` over the reals attained by the admissible rules; the rule that stops at
once is admissible, so the set is never empty.
-/
import Mathlib
import LatticeProb.Prob.BrownianContAll
import Parking.Basic

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- **Galmarino's criterion**, for a stopping time of a `(Fin d → ℝ)`-valued process: if `τ`
takes the value `t` at a path and a second path agrees with it up to time `t`, then `τ` takes
the value `t` there too.  The `Fin d`-dimensional analogue of `Parking.IsContStopping`
(`Parking/Support/ContOrientedLimit.lean`), which is hard-wired to a real-valued process. -/
def IsSpatialContStopping {Ω : Type*} {d : ℕ} (B : ℝ≥0 → Ω → (Fin d → ℝ)) (τ : Ω → ℝ≥0) :
    Prop :=
  ∀ (t : ℝ≥0) (ω ω' : Ω), τ ω = t → (∀ s ≤ t, B s ω = B s ω') → τ ω' = t

/-- The payoffs `E_0 G(τ, B_τ)` attained by the stopping times of `B` bounded by `T`, for a
`(Fin d → ℝ)`-valued driving process.  The first argument of `G` is the elapsed time.

The payoff of a rule counts only when it exists: Galmarino's criterion does not make `τ`
measurable, so for a general rule the integrand need not be measurable and the Bochner
integral is then the junk value zero; conjoining integrability is standing ruling R2 applied
to a definition, exactly as `Parking.contPayoffs` does for the one-dimensional case. -/
def spatialContPayoffs {d : ℕ} {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → (Fin d → ℝ))
    (PB : Measure ΩB) (G : ℝ → (Fin d → ℝ) → ℝ) (T : ℝ) : Set ℝ :=
  {a : ℝ | ∃ τ : ΩB → ℝ≥0, IsSpatialContStopping B τ ∧ (∀ β, (τ β : ℝ) ≤ T) ∧
    Integrable (fun β => G (τ β) (B (τ β) β)) PB ∧
    a = ∫ β, G (τ β) (B (τ β) β) ∂PB}

/-- `sup_{τ ≤ T} E_0 G(τ, B_τ)`, the Brownian optimal-stopping value at the reward `G`, for a
`(Fin d → ℝ)`-valued driving process. -/
def spatialContValue {d : ℕ} {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → (Fin d → ℝ))
    (PB : Measure ΩB) (G : ℝ → (Fin d → ℝ) → ℝ) (T : ℝ) : ℝ :=
  sSup (spatialContPayoffs B PB G T)

/-- The stopping time `0` is admissible, so the set of attainable payoffs is never empty,
whenever the reward at time `0` is integrable at the driving process's starting distribution. -/
theorem zero_mem_spatialContPayoffs {d : ℕ} {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → (Fin d → ℝ)) (PB : Measure ΩB) (G : ℝ → (Fin d → ℝ) → ℝ) {T : ℝ}
    (hT : 0 ≤ T) (hint : Integrable (fun β => G 0 (B 0 β)) PB) :
    (∫ β, G 0 (B 0 β) ∂PB) ∈ spatialContPayoffs B PB G T := by
  refine ⟨fun _ => 0, ?_, ?_, ?_, rfl⟩
  · intro t β β' h _
    exact h
  · intro β
    simpa using hT
  · simpa using hint

/-- A bound on the reward bounds the value. -/
theorem spatialContValue_le {d : ℕ} {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → (Fin d → ℝ)) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (G : ℝ → (Fin d → ℝ) → ℝ) (T : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ s (y : Fin d → ℝ), G s y ≤ M) :
    spatialContValue B PB G T ≤ M := by
  refine Real.sSup_le (fun a ha => ?_) hM
  obtain ⟨τ, _, _, hint, rfl⟩ := ha
  have hmono : (∫ β, G (τ β) (B (τ β) β) ∂PB) ≤ ∫ _β : ΩB, M ∂PB :=
    integral_mono hint (integrable_const M) (fun β => hbound _ _)
  simpa using hmono

/-- Every attainable payoff is at most the value, once the reward is bounded. -/
theorem le_spatialContValue {d : ℕ} {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → (Fin d → ℝ)) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (G : ℝ → (Fin d → ℝ) → ℝ) (T : ℝ) {M : ℝ} (hbound : ∀ s (y : Fin d → ℝ), G s y ≤ M)
    {a : ℝ} (ha : a ∈ spatialContPayoffs B PB G T) :
    a ≤ spatialContValue B PB G T := by
  refine le_csSup ⟨M, ?_⟩ ha
  rintro b ⟨τ, _, _, hint, rfl⟩
  have hmono : (∫ β, G (τ β) (B (τ β) β) ∂PB) ≤ ∫ _β : ΩB, M ∂PB :=
    integral_mono hint (integrable_const M) (fun β => hbound _ _)
  simpa using hmono

/-- **At horizon `0`, the only admissible stopping time is `0`**: `IsSpatialContStopping`
forces `τ β = 0` for every `β` once `τ β ≤ 0`, since `τ` is `ℝ≥0`-valued. -/
theorem spatialContPayoffs_zero_eq_singleton {d : ℕ} {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → (Fin d → ℝ)) (PB : Measure ΩB) (G : ℝ → (Fin d → ℝ) → ℝ)
    (hG0 : ∀ y, G 0 y = 0) :
    spatialContPayoffs B PB G 0 = {0} := by
  ext a
  simp only [spatialContPayoffs, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨τ, _, hτT, _, rfl⟩
    have hτ0 : ∀ β, τ β = 0 := fun β => by
      have h1 : (τ β : ℝ) ≤ 0 := hτT β
      have h2 : (0 : ℝ) ≤ (τ β : ℝ) := (τ β).coe_nonneg
      exact_mod_cast le_antisymm h1 h2
    have heq : (fun β => G (τ β) (B (τ β) β)) = fun _ => (0 : ℝ) := by
      funext β; rw [hτ0 β]; exact hG0 _
    rw [heq]; simp
  · intro ha
    refine ⟨fun _ => 0, fun t ω ω' h _ => h, fun β => le_refl 0, ?_, ?_⟩
    · simp [hG0]
    · simp [ha, hG0]

/-- **The continuum optimal-stopping value at horizon `0` vanishes**, for any reward that
vanishes at time `0`. -/
theorem spatialContValue_eq_zero_of_zero {d : ℕ} {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → (Fin d → ℝ)) (PB : Measure ΩB) (G : ℝ → (Fin d → ℝ) → ℝ)
    (hG0 : ∀ y, G 0 y = 0) :
    spatialContValue B PB G 0 = 0 := by
  unfold spatialContValue
  rw [spatialContPayoffs_zero_eq_singleton B PB G hG0, csSup_singleton]

/-- **The driving process of a `LatticeProb.IsBrownianSpace`, read in the paper's own
`Fin d → ℝ` vocabulary.** -/
def ofBrownianSpace {d : ℕ} {Ω : Type*} (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) :
    ℝ≥0 → Ω → (Fin d → ℝ) :=
  fun t ω => (EuclideanSpace.equiv (Fin d) ℝ) (B t ω)

theorem measurable_ofBrownianSpace {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} {t : ℝ≥0} (hBt : Measurable (B t)) :
    Measurable (ofBrownianSpace B t) :=
  (EuclideanSpace.equiv (Fin d) ℝ).continuous.measurable.comp hBt

/-- **The rescaled site of the simple random walk**, `z ↦ z/√n`: the inverse of
`barDivisible`'s own `⌊Rx⌋` at `R = √n`, matching `Parking.orientedScaledSite`'s role for the
oriented walk. -/
def spatialScaledSite (n : ℕ) {d : ℕ} (z : Site d) (i : Fin d) : ℝ := (z i : ℝ) / Real.sqrt n

end Parking

end
