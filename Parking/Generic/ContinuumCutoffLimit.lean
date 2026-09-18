/-
**The randomized cutoff-to-true bound for a continuum Brownian optimal-stopping value**, stated
for an arbitrary `(Fin d → ℝ)`-valued driving process and an arbitrary reward: this module makes
no reference to `Parking.External.LinearFieldScaling`, the white-noise field `Z`, or any other
object specific to this paper.  It is the construction that the continuum membrane field of the
divisible-sandpile paper requires.

`Parking.Support.ContSpatialCutoff`'s
`Parking.abs_spatialContValue_sub_contCutoffValue_le`/`_le_exp` compare a reward's TRUE optimal-
stopping value to its cutoff at radius `A`, but need the reward itself to be GLOBALLY bounded —
false for `Parking.contUc`'s own reward, which reads a jointly continuous but otherwise unbounded
field. This module instead compares the cutoff value at ONE level `A` to the cutoff value
at a SLIGHTLY LARGER level `A'`, which needs only a bound WITHIN the `A'`-ball (`contCutoffReward
G A'` is automatically globally bounded, being `0` outside), via the elementary fact that cutting
twice, at `A ≤ A'`, is the same as cutting once at `A` (`contCutoffReward_idem`). Chaining this
pairwise bound over consecutive integers, using Borel–Cantelli to control a summable sequence of
"exceptional" events on which the within-ball bound may fail, gives an ALMOST-SURE Cauchy (hence
convergent) sequence of cutoff values, with no reference to the possibly ill-posed "value of the
uncut reward" (whose very well-posedness — integrability of even the trivial stopping rule —
already needs a growth control on the reward, so it is not taken as the starting point here; the
limit constructed below serves as its rigorous replacement).

Three independent pieces:
1. `contCutoffReward_idem` and `abs_contCutoffValue_sub_contCutoffValue_le`: the deterministic
   double-cutoff identity and the resulting pairwise comparison, in terms of the driving
   process's own RAW exit probability `PB'.real (contExitEvent B' A T)` (not yet converted to an
   explicit exponential bound, so that no existential constants from `LatticeProb.
   brownian_exit_tail_closed` need to be threaded across the many pairwise applications below —
   each application would otherwise expose its own opaque witness pair, not visibly equal to any
   other application's, even though the underlying construction is deterministic).
2. `spatialContValue_congr_of_eqOn_Icc`: a reward's continuum optimal-stopping value depends only
   on its values on `[0,T] × (Fin d → ℝ)`, since every admissible stopping time is bounded by `T`
   — needed to replace a reward whose TIME argument ranges unclamped over all of `ℝ` (such as
   `Parking.contUc`'s own `fun k y => -Z ω' (s - k) (x + y)`) by a version clamped to `[0,s]` in
   the time argument, without changing the value, so that a within-a-ball bound at a FIXED time
   window becomes a genuine global bound on the clamped reward.
3. `ae_exists_tendsto_of_summable_step` and `ae_exists_tendsto_contCutoffValue_of_summable_exitTerm`:
   the Borel–Cantelli argument itself (fully generic, no continuum-value content at all) and its
   combination with item 1's pairwise bound.
-/
import Parking.Support.ContSpatialCutoff

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking.Generic.ContinuumCutoffLimit

variable {d : ℕ}

/-! ### The deterministic double-cutoff identity -/

/-- **Cutting twice, at `A ≤ A'`, is the same as cutting once at `A`.** -/
theorem contCutoffReward_idem (G : ℝ → (Fin d → ℝ) → ℝ) {A A' : ℝ} (hA : A ≤ A') :
    Parking.contCutoffReward (Parking.contCutoffReward G A') A = Parking.contCutoffReward G A := by
  funext k y
  unfold Parking.contCutoffReward
  by_cases h1 : ‖y‖ < A
  · have h2 : ‖y‖ < A' := lt_of_lt_of_le h1 hA
    simp [h1, h2]
  · simp [h1]

/-- **The pairwise cutoff comparison, raw form**: the cutoff value at level `A'` and at level
`A ≤ A'` of the SAME reward differ by at most `M` times the driving process's own probability of
leaving the `A`-ball by time `T`, given only that the reward is bounded by `M` WITHIN the
`A'`-ball (not globally, unlike `Parking.abs_spatialContValue_sub_contCutoffValue_le`, whose
hypothesis this reduces to via `contCutoffReward_idem` applied to the reward already cut at
`A'`). The exit probability is left unconverted to an exponential bound (see the module
docstring) so that the caller controls the constants uniformly across every pairwise
application. -/
theorem abs_contCutoffValue_sub_contCutoffValue_le {ΩB' : Type*} [MeasurableSpace ΩB']
    (B' : ℝ≥0 → ΩB' → EuclideanSpace ℝ (Fin d)) (PB' : Measure ΩB') [IsProbabilityMeasure PB']
    (hcont : ∀ ω, Continuous fun s => B' s ω) (hBm : ∀ s, Measurable (B' s))
    (G : ℝ → (Fin d → ℝ) → ℝ) (A A' M : ℝ) (hAA' : A ≤ A')
    (hGbA' : ∀ k y, ‖y‖ < A' → |G k y| ≤ M) (hM : 0 ≤ M)
    (T : ℝ) (hT0 : 0 ≤ T) (hG0m : Measurable (G 0))
    (hcross : ∀ τ : ΩB' → ℝ≥0, Parking.IsSpatialContStopping (Parking.ofBrownianSpace B') τ →
      (∀ β, (τ β : ℝ) ≤ T) →
      Integrable (fun β => Parking.contCutoffReward G A' (τ β)
        (Parking.ofBrownianSpace B' (τ β) β)) PB' →
      Integrable (fun β => Parking.contCutoffReward G A (τ β)
        (Parking.ofBrownianSpace B' (τ β) β)) PB')
    (hcross' : ∀ τ : ΩB' → ℝ≥0, Parking.IsSpatialContStopping (Parking.ofBrownianSpace B') τ →
      (∀ β, (τ β : ℝ) ≤ T) →
      Integrable (fun β => Parking.contCutoffReward G A (τ β)
        (Parking.ofBrownianSpace B' (τ β) β)) PB' →
      Integrable (fun β => Parking.contCutoffReward G A' (τ β)
        (Parking.ofBrownianSpace B' (τ β) β)) PB') :
    |Parking.contCutoffValue (Parking.ofBrownianSpace B') PB' G A' T
        - Parking.contCutoffValue (Parking.ofBrownianSpace B') PB' G A T|
      ≤ M * PB'.real (Parking.contExitEvent B' A T) := by
  set G' : ℝ → (Fin d → ℝ) → ℝ := Parking.contCutoffReward G A' with hG'def
  have hGb' : ∀ k y, |G' k y| ≤ M := by
    intro k y
    rw [hG'def]
    unfold Parking.contCutoffReward
    split_ifs with h
    · exact hGbA' k y h
    · simpa using hM
  have hG0m' : Measurable (G' 0) := Parking.measurable_contCutoffReward_zero A' hG0m
  have hidem : Parking.contCutoffReward G' A = Parking.contCutoffReward G A :=
    contCutoffReward_idem G hAA'
  have hcross2 : ∀ τ : ΩB' → ℝ≥0, Parking.IsSpatialContStopping (Parking.ofBrownianSpace B') τ →
      (∀ β, (τ β : ℝ) ≤ T) →
      Integrable (fun β => G' (τ β) (Parking.ofBrownianSpace B' (τ β) β)) PB' →
      Integrable (fun β => Parking.contCutoffReward G' A (τ β)
        (Parking.ofBrownianSpace B' (τ β) β)) PB' := by
    intro τ hτ hτT hint
    rw [hidem]
    exact hcross τ hτ hτT hint
  have hcross2' : ∀ τ : ΩB' → ℝ≥0, Parking.IsSpatialContStopping (Parking.ofBrownianSpace B') τ →
      (∀ β, (τ β : ℝ) ≤ T) →
      Integrable (fun β => Parking.contCutoffReward G' A (τ β)
        (Parking.ofBrownianSpace B' (τ β) β)) PB' →
      Integrable (fun β => G' (τ β) (Parking.ofBrownianSpace B' (τ β) β)) PB' := by
    intro τ hτ hτT hint
    rw [hidem] at hint
    exact hcross' τ hτ hτT hint
  have hbound := Parking.abs_spatialContValue_sub_contCutoffValue_le B' PB' hcont hBm G' A M hGb'
    T hT0 hG0m' hcross2 hcross2'
  have heq1 : Parking.spatialContValue (Parking.ofBrownianSpace B') PB' G' T
      = Parking.contCutoffValue (Parking.ofBrownianSpace B') PB' G A' T := rfl
  have heq2 : Parking.contCutoffValue (Parking.ofBrownianSpace B') PB' G' A T
      = Parking.contCutoffValue (Parking.ofBrownianSpace B') PB' G A T := by
    unfold Parking.contCutoffValue
    rw [hidem]
  rwa [heq1, heq2] at hbound

/-! ### A reward's continuum optimal-stopping value only sees `[0,T] × (Fin d → ℝ)` -/

/-- **The continuum optimal-stopping value depends on the reward only through its values on
`[0,T] × (Fin d → ℝ)`**, since every admissible stopping time is bounded by `T` (and
nonnegative). Used to replace a reward whose time argument is unclamped by one clamped to
`[0,T]`, without changing the value. -/
theorem spatialContValue_congr_of_eqOn_Icc {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → (Fin d → ℝ)) (PB : Measure ΩB) (G G' : ℝ → (Fin d → ℝ) → ℝ) {T : ℝ}
    (heq : ∀ k ∈ Set.Icc (0 : ℝ) T, ∀ y, G k y = G' k y) :
    Parking.spatialContValue B PB G T = Parking.spatialContValue B PB G' T := by
  have hset : Parking.spatialContPayoffs B PB G T = Parking.spatialContPayoffs B PB G' T := by
    ext a
    constructor
    · rintro ⟨τ, hτ, hτT, hint, rfl⟩
      have hmem : ∀ β, (τ β : ℝ) ∈ Set.Icc (0 : ℝ) T := fun β => ⟨(τ β).coe_nonneg, hτT β⟩
      have hfun : (fun β => G (τ β) (B (τ β) β)) = fun β => G' (τ β) (B (τ β) β) := by
        funext β; exact heq (τ β) (hmem β) (B (τ β) β)
      exact ⟨τ, hτ, hτT, hfun ▸ hint, by rw [← hfun]⟩
    · rintro ⟨τ, hτ, hτT, hint, rfl⟩
      have hmem : ∀ β, (τ β : ℝ) ∈ Set.Icc (0 : ℝ) T := fun β => ⟨(τ β).coe_nonneg, hτT β⟩
      have hfun : (fun β => G (τ β) (B (τ β) β)) = fun β => G' (τ β) (B (τ β) β) := by
        funext β; exact heq (τ β) (hmem β) (B (τ β) β)
      exact ⟨τ, hτ, hτT, hfun ▸ hint, by rw [hfun]⟩
  unfold Parking.spatialContValue
  rw [hset]

/-! ### Borel–Cantelli: a summable telescoping bound on good events gives a.e. convergence -/

/-- **A summable telescoping bound on a family of good events, of summable exceptional
probability, gives a.e. convergence of the sequence.** Fully generic: no reference to any
optimal-stopping value, driving process, or field. -/
theorem ae_exists_tendsto_of_summable_step
    {Ω' : Type*} [MeasurableSpace Ω'] (Q' : Measure Ω')
    (f : ℕ → Ω' → ℝ) (Good : ℕ → Set Ω')
    (a : ℕ → ℝ) (hasummable : Summable a)
    (hstep : ∀ n ω', ω' ∈ Good n → dist (f n ω') (f (n + 1) ω') ≤ a n)
    (hgoodtail : ∑' n, Q' (Good n)ᶜ ≠ ⊤) :
    ∀ᵐ ω' ∂Q', ∃ L : ℝ, Tendsto (fun n => f n ω') atTop (𝓝 L) := by
  have hae : ∀ᵐ ω' ∂Q', ∀ᶠ n in atTop, ω' ∉ (Good n)ᶜ := ae_eventually_notMem hgoodtail
  filter_upwards [hae] with ω' hω'
  rw [Filter.eventually_atTop] at hω'
  obtain ⟨N, hN⟩ := hω'
  have hNgood : ∀ n, N ≤ n → ω' ∈ Good n := fun n hn => by simpa using hN n hn
  set g : ℕ → ℝ := fun m => f (m + N) ω' with hgdef
  have hgcauchy : CauchySeq g := by
    apply cauchySeq_of_dist_le_of_summable (fun m => a (m + N))
    · intro m
      have h1 := hstep (m + N) ω' (hNgood (m + N) (Nat.le_add_left N m))
      have h2 : m + N + 1 = m.succ + N := by omega
      rwa [h2] at h1
    · exact hasummable.comp_injective (add_left_injective N)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hgcauchy
  exact ⟨L, (tendsto_add_atTop_iff_nat (f := fun n => f n ω') N).mp hL⟩

/-- **The randomized cutoff-to-true bound, assembled**: given, for every `n`, a "good" event
(exceptional probability summable over `n`) on which the reward `G ω'` is bounded within the
ball of radius `(n:ℝ) + 2`, and given that the resulting sequence of `M n` times the driving
process's own exit probability from the `(n:ℝ)+1`-ball is summable, the sequence of cutoff
values `n ↦ Parking.contCutoffValue (ofBrownianSpace B') PB' (G ω') ((n:ℝ)+1) T` converges
almost surely as `n → ∞`. No reference to the value of the uncut reward. -/
theorem ae_exists_tendsto_contCutoffValue_of_summable_exitTerm
    {Ω' : Type*} [MeasurableSpace Ω'] (Q' : Measure Ω')
    {ΩB' : Type*} [MeasurableSpace ΩB'] (B' : ℝ≥0 → ΩB' → EuclideanSpace ℝ (Fin d))
    (PB' : Measure ΩB') [IsProbabilityMeasure PB']
    (hcont : ∀ ω, Continuous fun s => B' s ω) (hBm : ∀ s, Measurable (B' s))
    (G : Ω' → ℝ → (Fin d → ℝ) → ℝ) (T : ℝ) (hT0 : 0 ≤ T)
    (M : ℕ → ℝ) (hM0 : ∀ n, 0 ≤ M n)
    (Good : ℕ → Set Ω')
    (hGoodBound : ∀ n, ∀ ω' ∈ Good n, ∀ k y, ‖y‖ < (n : ℝ) + 2 → |G ω' k y| ≤ M n)
    (hgoodtail : ∑' n, Q' (Good n)ᶜ ≠ ⊤)
    (hG0m : ∀ ω', Measurable (G ω' 0))
    (hcross : ∀ n ω', ∀ τ : ΩB' → ℝ≥0,
      Parking.IsSpatialContStopping (Parking.ofBrownianSpace B') τ →
      (∀ β, (τ β : ℝ) ≤ T) →
      Integrable (fun β => Parking.contCutoffReward (G ω') ((n : ℝ) + 2) (τ β)
        (Parking.ofBrownianSpace B' (τ β) β)) PB' →
      Integrable (fun β => Parking.contCutoffReward (G ω') ((n : ℝ) + 1) (τ β)
        (Parking.ofBrownianSpace B' (τ β) β)) PB')
    (hcross' : ∀ n ω', ∀ τ : ΩB' → ℝ≥0,
      Parking.IsSpatialContStopping (Parking.ofBrownianSpace B') τ →
      (∀ β, (τ β : ℝ) ≤ T) →
      Integrable (fun β => Parking.contCutoffReward (G ω') ((n : ℝ) + 1) (τ β)
        (Parking.ofBrownianSpace B' (τ β) β)) PB' →
      Integrable (fun β => Parking.contCutoffReward (G ω') ((n : ℝ) + 2) (τ β)
        (Parking.ofBrownianSpace B' (τ β) β)) PB')
    (hexitsummable : Summable
      (fun n : ℕ => M n * PB'.real (Parking.contExitEvent B' ((n : ℝ) + 1) T))) :
    ∀ᵐ ω' ∂Q', ∃ L : ℝ,
      Tendsto (fun n : ℕ =>
          Parking.contCutoffValue (Parking.ofBrownianSpace B') PB' (G ω') ((n : ℝ) + 1) T)
        atTop (𝓝 L) := by
  apply ae_exists_tendsto_of_summable_step Q'
    (fun n ω' => Parking.contCutoffValue (Parking.ofBrownianSpace B') PB' (G ω') ((n : ℝ) + 1) T)
    Good (fun n => M n * PB'.real (Parking.contExitEvent B' ((n : ℝ) + 1) T)) hexitsummable ?_
    hgoodtail
  intro n ω' hω'
  have hAA' : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) + 1 := by linarith
  have hstepbound := abs_contCutoffValue_sub_contCutoffValue_le B' PB' hcont hBm (G ω')
    ((n : ℝ) + 1) (((n : ℝ) + 1) + 1) (M n) hAA'
    (by
      intro k y hy
      exact hGoodBound n ω' hω' k y (by
        have h : ((n : ℝ) + 1) + 1 = (n : ℝ) + 2 := by ring
        rwa [h] at hy))
    (hM0 n) T hT0 (hG0m ω')
    (by
      intro τ hτ hτT hint
      have h : ((n : ℝ) + 1) + 1 = (n : ℝ) + 2 := by ring
      rw [h] at hint
      exact hcross n ω' τ hτ hτT hint)
    (by
      intro τ hτ hτT hint
      have h : ((n : ℝ) + 1) + 1 = (n : ℝ) + 2 := by ring
      have h2 := hcross' n ω' τ hτ hτT hint
      rwa [h])
  have hcast : ((n + 1 : ℕ) : ℝ) + 1 = ((n : ℝ) + 1) + 1 := by push_cast; ring
  rw [dist_comm, Real.dist_eq, hcast]
  exact hstepbound

end Parking.Generic.ContinuumCutoffLimit

end
