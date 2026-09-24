/-
**The cutoff construction for the `Fin d`-dimensional Brownian optimal-stopping value**
`Parking.spatialContValue` (`Parking/Support/ContSpatialValue.lean`), the continuum analogue of
`Parking.Support.SpatialStoppingCutoff`'s cutoff construction for the discrete simple random
walk.

Joint continuity of `Parking.contUc` cannot go through `Parking.abs_spatialContValue_sub_le`
(`ContValueLipschitz.lean`) directly, because that Lipschitz bound needs a GLOBAL sup bound on
the reward, whereas `Uc`'s own reward `k y ↦ -Z ω' (s-k) (x+y)` reads `Z` at every real argument
(even though only `k ∈ [0,s]` is read by an admissible rule) and `Z` is only LOCALLY bounded (by
continuity), not globally. This is the SAME "unbounded reward domain forces a cutoff" obstruction
that the discrete oscillation clause meets. The library carries the exact probabilistic tool
that removes it, proved unconditionally in general dimension:
`LatticeProb.brownian_exit_tail_pos`/`brownian_exit_tail_closed`
(`../Lattice-Probability-clean/LatticeProb/Prob/BrownianExit.lean`), the continuum analogue of
this repository's own `Parking.measureReal_sup_walkPath_graphNorm_le`.

This module builds the comparison, for a GENERAL bounded reward `G`, mirroring
`Parking.Support.SpatialStoppingCutoff` step by step: the cutoff reward
(`Parking.contCutoffReward`), its exactness inside the box, the cutoff value
(`Parking.contCutoffValue`), and the cutoff error bound
(`Parking.abs_spatialContValue_sub_contCutoffValue_le`) — no External, no `sorry`. As in
`Parking.abs_spatialContValue_sub_le` (`ContValueLipschitz.lean`, whose own docstring explains
why), the cross-integrability of an admissible rule's payoff between the true and the cutoff
reward is recorded as an explicit hypothesis rather than derived: `IsSpatialContStopping`
(Galmarino's criterion) does not by itself make a stopping time jointly measurable with the
driving process, so integrability of the two composite payoffs is not a free consequence of
either reward's own measurability. The box is cut at the Pi (sup) norm on `Fin d → ℝ`,
`Parking.norm_ofBrownianSpace_le` transporting the library's own Euclidean-norm exit tail
(stated for `EuclideanSpace ℝ (Fin d)`, the driving space of `LatticeProb.IsBrownianSpace`) to
it: the sup norm of a vector is at most its Euclidean norm, coordinatewise, so a sup-norm exit
is an Euclidean-norm exit, and the library's tail bound applies unchanged.
-/
import Parking.Support.ContValueLipschitz
import LatticeProb.Prob.BrownianExitTime

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace Parking

variable {d : ℕ}

/-! ### The Pi (sup) norm on `Fin d → ℝ` is dominated by the Euclidean norm -/

/-- **The sup norm of a vector is at most its Euclidean norm.** -/
theorem norm_equiv_le (z : EuclideanSpace ℝ (Fin d)) :
    ‖(EuclideanSpace.equiv (Fin d) ℝ) z‖ ≤ ‖z‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg z)]
  intro i
  rw [EuclideanSpace.norm_eq]
  have hmem : ‖z i‖ ^ 2 ≤ ∑ j, ‖z j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have heq : ((EuclideanSpace.equiv (Fin d) ℝ) z) i = z i := rfl
  rw [heq]
  calc ‖z i‖ = Real.sqrt (‖z i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ j, ‖z j‖ ^ 2) := Real.sqrt_le_sqrt hmem

/-- **The sup norm of `Parking.ofBrownianSpace B t ω` is at most the Euclidean norm of
`B t ω`.** -/
theorem norm_ofBrownianSpace_le {Ω : Type*} (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (t : ℝ≥0) (ω : Ω) : ‖ofBrownianSpace B t ω‖ ≤ ‖B t ω‖ :=
  norm_equiv_le (B t ω)

/-! ### The cutoff reward, and its exactness inside the box -/

/-- **The cutoff reward**: `G` truncated to the open box of sup-norm radius `A` about the
origin, `0` outside (open, to match the library's own exit-tail event `A ≤ ‖·‖` exactly at the
complement). -/
def contCutoffReward (G : ℝ → (Fin d → ℝ) → ℝ) (A : ℝ) (k : ℝ) (y : Fin d → ℝ) : ℝ :=
  if ‖y‖ < A then G k y else 0

theorem contCutoffReward_eq_of_lt (G : ℝ → (Fin d → ℝ) → ℝ) (A : ℝ) (k : ℝ) (y : Fin d → ℝ)
    (hy : ‖y‖ < A) : contCutoffReward G A k y = G k y := if_pos hy

theorem contCutoffReward_eq_zero_of_le (G : ℝ → (Fin d → ℝ) → ℝ) (A : ℝ) (k : ℝ) (y : Fin d → ℝ)
    (hy : A ≤ ‖y‖) : contCutoffReward G A k y = 0 := if_neg (not_lt.mpr hy)

/-- **A bound on the true reward bounds the cutoff reward, everywhere.** -/
theorem abs_contCutoffReward_le (G : ℝ → (Fin d → ℝ) → ℝ) (A : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hGb : ∀ k y, |G k y| ≤ M) (k : ℝ) (y : Fin d → ℝ) : |contCutoffReward G A k y| ≤ M := by
  unfold contCutoffReward
  split_ifs
  · exact hGb k y
  · simpa using hM

theorem measurable_contCutoffReward_zero {G : ℝ → (Fin d → ℝ) → ℝ} (A : ℝ)
    (hG0m : Measurable (G 0)) : Measurable (contCutoffReward G A 0) := by
  unfold contCutoffReward
  exact hG0m.piecewise (measurableSet_lt continuous_norm.measurable measurable_const)
    measurable_const

/-! ### The cutoff optimal-stopping value -/

/-- **The cutoff continuum optimal-stopping value.** -/
def contCutoffValue {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → (Fin d → ℝ))
    (PB : Measure ΩB) (G : ℝ → (Fin d → ℝ) → ℝ) (A T : ℝ) : ℝ :=
  spatialContValue B PB (contCutoffReward G A) T

/-! ### The exit event, and its measurability -/

/-- **The event that the driving process leaves the box of sup-radius `A` by time `T`, read as
a Euclidean-norm exit event.** -/
def contExitEvent {ΩB' : Type*} (B' : ℝ≥0 → ΩB' → EuclideanSpace ℝ (Fin d)) (A T : ℝ) :
    Set ΩB' := {β | ∃ s : ℝ≥0, (s : ℝ) ≤ T ∧ A ≤ ‖B' s β‖}

theorem measurableSet_contExitEvent {ΩB' : Type*} [MeasurableSpace ΩB']
    (B' : ℝ≥0 → ΩB' → EuclideanSpace ℝ (Fin d))
    (hcont : ∀ ω, Continuous fun s => B' s ω) (hBm : ∀ s, Measurable (B' s)) (A T : ℝ)
    (hT0 : 0 ≤ T) : MeasurableSet (contExitEvent B' A T) := by
  have hEeq : contExitEvent B' A T = {β | ∃ s ≤ T.toNNReal, A ≤ ‖B' s β - 0‖} := by
    ext β
    simp only [contExitEvent, sub_zero, Set.mem_setOf_eq]
    constructor
    · rintro ⟨s, hs, hA⟩
      exact ⟨s, (Real.le_toNNReal_iff_coe_le hT0).2 hs, hA⟩
    · rintro ⟨s, hs, hA⟩
      exact ⟨s, (Real.le_toNNReal_iff_coe_le hT0).1 hs, hA⟩
  rw [hEeq]
  exact LatticeProb.measurableSet_exists_le_le_norm B' hBm hcont 0 A T.toNNReal

/-! ### The cutoff error bound -/

/-- **The cutoff error bound, rule by rule**: for one fixed bounded stopping rule with the
cross-integrability of its cutoff payoff, the true and cutoff terminal rewards differ only
through the event that the driving process leaves the box of sup-radius `A` by the horizon
`T`, and there by at most the reward's own bound. -/
theorem abs_contPayoff_sub_cutoffReward_le {ΩB' : Type*} [MeasurableSpace ΩB']
    (B' : ℝ≥0 → ΩB' → EuclideanSpace ℝ (Fin d)) (PB' : Measure ΩB') [IsProbabilityMeasure PB']
    (hcont : ∀ ω, Continuous fun s => B' s ω) (hBm : ∀ s, Measurable (B' s))
    (G : ℝ → (Fin d → ℝ) → ℝ) (A M : ℝ) (hGb : ∀ k y, |G k y| ≤ M) (T : ℝ) (hT0 : 0 ≤ T)
    {τ : ΩB' → ℝ≥0} (hτT : ∀ β, (τ β : ℝ) ≤ T)
    (hint : Integrable (fun β => G (τ β) (ofBrownianSpace B' (τ β) β)) PB')
    (hint' : Integrable (fun β => contCutoffReward G A (τ β) (ofBrownianSpace B' (τ β) β))
      PB') :
    |(∫ β, G (τ β) (ofBrownianSpace B' (τ β) β) ∂PB')
        - ∫ β, contCutoffReward G A (τ β) (ofBrownianSpace B' (τ β) β) ∂PB'|
      ≤ M * PB'.real (contExitEvent B' A T) := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hGb 0 0)
  have hEmeas : MeasurableSet (contExitEvent B' A T) :=
    measurableSet_contExitEvent B' hcont hBm A T hT0
  have hpt : ∀ β, |G (τ β) (ofBrownianSpace B' (τ β) β)
      - contCutoffReward G A (τ β) (ofBrownianSpace B' (τ β) β)|
      ≤ (contExitEvent B' A T).indicator (fun _ => M) β := by
    intro β
    by_cases hbox : ‖ofBrownianSpace B' (τ β) β‖ < A
    · rw [contCutoffReward_eq_of_lt G A _ _ hbox, sub_self, abs_zero]
      exact Set.indicator_nonneg (fun _ _ => hM) β
    · rw [contCutoffReward_eq_zero_of_le G A _ _ (not_lt.mp hbox), sub_zero]
      have hmem : β ∈ contExitEvent B' A T :=
        ⟨τ β, hτT β, le_trans (not_lt.mp hbox) (norm_ofBrownianSpace_le B' (τ β) β)⟩
      rw [Set.indicator_of_mem hmem]
      exact hGb (τ β) (ofBrownianSpace B' (τ β) β)
  calc |(∫ β, G (τ β) (ofBrownianSpace B' (τ β) β) ∂PB')
      - ∫ β, contCutoffReward G A (τ β) (ofBrownianSpace B' (τ β) β) ∂PB'|
      = |∫ β, (G (τ β) (ofBrownianSpace B' (τ β) β)
          - contCutoffReward G A (τ β) (ofBrownianSpace B' (τ β) β)) ∂PB'| := by
        rw [integral_sub hint hint']
    _ ≤ ∫ β, |G (τ β) (ofBrownianSpace B' (τ β) β)
          - contCutoffReward G A (τ β) (ofBrownianSpace B' (τ β) β)| ∂PB' :=
        abs_integral_le_integral_abs
    _ ≤ ∫ β, (contExitEvent B' A T).indicator (fun _ => M) β ∂PB' :=
        integral_mono (hint.sub hint').abs ((integrable_const M).indicator hEmeas) hpt
    _ = M * PB'.real (contExitEvent B' A T) := by
        rw [integral_indicator_const _ hEmeas, smul_eq_mul, mul_comm, measureReal_def]

/-- **The cutoff error bound for the VALUE**: the true and cutoff continuum optimal-stopping
values differ by at most `M` times the driving process's own probability of leaving the box of
sup-radius `A` within the horizon `T`, uniformly over every admissible stopping rule bounded by
`T`, given the cross-integrability of every admissible rule's cutoff payoff
(`hcross`/`hcross'`, exactly as `Parking.abs_spatialContValue_sub_le` records it). -/
theorem abs_spatialContValue_sub_contCutoffValue_le {ΩB' : Type*} [MeasurableSpace ΩB']
    (B' : ℝ≥0 → ΩB' → EuclideanSpace ℝ (Fin d)) (PB' : Measure ΩB') [IsProbabilityMeasure PB']
    (hcont : ∀ ω, Continuous fun s => B' s ω) (hBm : ∀ s, Measurable (B' s))
    (G : ℝ → (Fin d → ℝ) → ℝ) (A M : ℝ) (hGb : ∀ k y, |G k y| ≤ M) (T : ℝ) (hT0 : 0 ≤ T)
    (hG0m : Measurable (G 0))
    (hcross : ∀ τ : ΩB' → ℝ≥0, IsSpatialContStopping (ofBrownianSpace B') τ →
      (∀ β, (τ β : ℝ) ≤ T) →
      Integrable (fun β => G (τ β) (ofBrownianSpace B' (τ β) β)) PB' →
      Integrable (fun β => contCutoffReward G A (τ β) (ofBrownianSpace B' (τ β) β)) PB')
    (hcross' : ∀ τ : ΩB' → ℝ≥0, IsSpatialContStopping (ofBrownianSpace B') τ →
      (∀ β, (τ β : ℝ) ≤ T) →
      Integrable (fun β => contCutoffReward G A (τ β) (ofBrownianSpace B' (τ β) β)) PB' →
      Integrable (fun β => G (τ β) (ofBrownianSpace B' (τ β) β)) PB') :
    |spatialContValue (ofBrownianSpace B') PB' G T
        - contCutoffValue (ofBrownianSpace B') PB' G A T|
      ≤ M * PB'.real (contExitEvent B' A T) := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hGb 0 0)
  set c : ℝ := M * PB'.real (contExitEvent B' A T) with hcdef
  have hc0 : 0 ≤ c := mul_nonneg hM measureReal_nonneg
  have hcm0 : Measurable (contCutoffReward G A 0) := measurable_contCutoffReward_zero A hG0m
  have hbG := bddAbove_spatialContPayoffs (ofBrownianSpace B') PB' G T
    (fun s y => (abs_le.mp (hGb s y)).2)
  have hbG' := bddAbove_spatialContPayoffs (ofBrownianSpace B') PB' (contCutoffReward G A) T
    (fun s y => (abs_le.mp (abs_contCutoffReward_le G A hM hGb s y)).2)
  have hneG := spatialContPayoffs_nonempty (ofBrownianSpace B') PB' G hT0 hGb
    (measurable_ofBrownianSpace (hBm 0)) hG0m
  have hneG' := spatialContPayoffs_nonempty (ofBrownianSpace B') PB' (contCutoffReward G A) hT0
    (abs_contCutoffReward_le G A hM hGb) (measurable_ofBrownianSpace (hBm 0)) hcm0
  have h1 : spatialContValue (ofBrownianSpace B') PB' G T
      ≤ contCutoffValue (ofBrownianSpace B') PB' G A T + c := by
    refine csSup_le hneG ?_
    rintro a ⟨τ, hτ, hτT, hint, rfl⟩
    have hint' := hcross τ hτ hτT hint
    have h1' : (∫ β, contCutoffReward G A (τ β) (ofBrownianSpace B' (τ β) β) ∂PB')
        ≤ contCutoffValue (ofBrownianSpace B') PB' G A T :=
      le_csSup hbG' ⟨τ, hτ, hτT, hint', rfl⟩
    have h2' := abs_contPayoff_sub_cutoffReward_le B' PB' hcont hBm G A M hGb T hT0 hτT hint hint'
    have := (abs_sub_le_iff.mp h2').1
    linarith
  have h2 : contCutoffValue (ofBrownianSpace B') PB' G A T
      ≤ spatialContValue (ofBrownianSpace B') PB' G T + c := by
    refine csSup_le hneG' ?_
    rintro a ⟨τ, hτ, hτT, hint, rfl⟩
    have hint' := hcross' τ hτ hτT hint
    have h1' : (∫ β, G (τ β) (ofBrownianSpace B' (τ β) β) ∂PB')
        ≤ spatialContValue (ofBrownianSpace B') PB' G T :=
      le_csSup hbG ⟨τ, hτ, hτT, hint', rfl⟩
    have h2' := abs_contPayoff_sub_cutoffReward_le B' PB' hcont hBm G A M hGb T hT0 hτT hint'
      hint
    have := (abs_sub_le_iff.mp h2').2
    linarith
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- **The cutoff error, as `A → ∞`**: combining
`Parking.abs_spatialContValue_sub_contCutoffValue_le` with
`LatticeProb.brownian_exit_tail_closed`, the right-hand side visibly `→ 0` as `A → ∞` for each
fixed `T`. -/
theorem abs_spatialContValue_sub_contCutoffValue_le_exp {ΩB' : Type*} [MeasurableSpace ΩB']
    (B' : ℝ≥0 → ΩB' → EuclideanSpace ℝ (Fin d)) (PB' : Measure ΩB') [IsProbabilityMeasure PB']
    (hcont : ∀ ω, Continuous fun s => B' s ω) (hBm : ∀ s, Measurable (B' s))
    (hB' : LatticeProb.IsBrownianSpace d 0 B' PB')
    (G : ℝ → (Fin d → ℝ) → ℝ) (A M : ℝ) (hGb : ∀ k y, |G k y| ≤ M) (T : ℝ) (hT0 : 0 < T)
    (hA : 0 < A) (hG0m : Measurable (G 0))
    (hcross : ∀ τ : ΩB' → ℝ≥0, IsSpatialContStopping (ofBrownianSpace B') τ →
      (∀ β, (τ β : ℝ) ≤ T) →
      Integrable (fun β => G (τ β) (ofBrownianSpace B' (τ β) β)) PB' →
      Integrable (fun β => contCutoffReward G A (τ β) (ofBrownianSpace B' (τ β) β)) PB')
    (hcross' : ∀ τ : ΩB' → ℝ≥0, IsSpatialContStopping (ofBrownianSpace B') τ →
      (∀ β, (τ β : ℝ) ≤ T) →
      Integrable (fun β => contCutoffReward G A (τ β) (ofBrownianSpace B' (τ β) β)) PB' →
      Integrable (fun β => G (τ β) (ofBrownianSpace B' (τ β) β)) PB') :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      |spatialContValue (ofBrownianSpace B') PB' G T
          - contCutoffValue (ofBrownianSpace B') PB' G A T|
        ≤ M * (C * Real.exp (-(c * A ^ 2 / (T + 1)))) := by
  obtain ⟨C, c, hC, hc, hbound⟩ := LatticeProb.brownian_exit_tail_closed d
  refine ⟨C, c, hC, hc, ?_⟩
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hGb 0 0)
  have hstep := abs_spatialContValue_sub_contCutoffValue_le B' PB' hcont hBm G A M hGb T hT0.le
    hG0m hcross hcross'
  refine hstep.trans (mul_le_mul_of_nonneg_left ?_ hM)
  have hexit := hbound 0 ΩB' PB' inferInstance B' hB' A hA (T + 1) (by linarith)
  have hsub : contExitEvent B' A T ⊆ {ω | ∃ s : ℝ≥0, (s : ℝ) < T + 1 ∧ A ≤ ‖B' s ω - 0‖} := by
    rintro β ⟨s, hs, hA'⟩
    exact ⟨s, by linarith, by simpa using hA'⟩
  calc PB'.real (contExitEvent B' A T)
      ≤ PB'.real {ω | ∃ s : ℝ≥0, (s : ℝ) < T + 1 ∧ A ≤ ‖B' s ω - 0‖} :=
        measureReal_mono hsub
    _ ≤ C * Real.exp (-(c * A ^ 2 / (T + 1))) := by
        rw [measureReal_def]
        have := ENNReal.toReal_mono (by finiteness) hexit
        rwa [ENNReal.toReal_ofReal (by positivity)] at this

end Parking

end
