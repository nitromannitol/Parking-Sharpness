/-
**The continuum randomized cutoff-to-true bound for `Parking.contUc`'s own stopping-value
summand**, instantiating `Parking.Generic.ContinuumCutoffLimit` for the white-noise field `Z` of
`Parking.External.LinearFieldScaling`.

The module has two independent parts:

1. **A pointwise tail bound for `Z`** (`exists_measureReal_abs_Z_gt_le`): Chebyshev's inequality
   applied to `Z ω' t x`'s own second moment, read directly off the covariance formula that
   `LinearFieldScaling` exposes at `r = s = t`, `x = y` — no Gaussianity, no heat-kernel Hölder
   estimate, no citation. This is unconditional and general (any `d`, `t`, `x`), but it bounds
   `Z` at a SINGLE point, not the SUPREMUM over a growing space-time box that `contCutoffReward`
   genuinely needs (see the remark on the hypotheses below).

2. **The randomized cutoff-to-true bound for the clamped stopping-value summand**
   (`ae_tendsto_contCutoffValue_sub_contStoppingValue`): `Parking.contUc`'s reward
   `k y ↦ -Z ω' (s - k) (x + y)` is genuinely unbounded in BOTH its time argument (as `k` ranges
   over all of `ℝ`, not just `[0,s]`) and its space argument, so
   `Parking.Generic.ContinuumCutoffLimit.abs_contCutoffValue_sub_contCutoffValue_le` cannot be
   applied to it directly. `clampTime`/`clampedStoppingReward` clamp the time argument to `[0,s]`
   (invisible to `Parking.spatialContValue`, since every admissible rule is already bounded by
   `s`, via `Parking.Generic.ContinuumCutoffLimit.spatialContValue_congr_of_eqOn_Icc`), reducing
   the remaining unboundedness to exactly the supremum of `Z` over the joint space-time box,
   which a maximal inequality (the analogue for suprema of the pointwise bound of part 1)
   controls. `Parking.contStoppingValue` is built as the resulting almost-sure LIMIT of the
   cutoff values, rather than as `Parking.spatialContValue` of the raw (possibly ill-posed)
   reward.

**The hypotheses `hGoodBound`/`hgoodtail`/`hexitsummable`** of
`ae_tendsto_contCutoffValue_sub_contStoppingValue` are exactly the shape that a continuum maximal
inequality for `Z` over the GROWING joint box `[0,s] × {‖y‖ < (n:ℝ)+2}` supplies: a family of
"good" events of summable exceptional probability on which `Z` is bounded within the box, by a
witness `M n` making the resulting exit-probability series summable. The pointwise bound of
part 1 is not of this kind, since it controls `Z` at a single point and not its supremum over
the box.
-/
import Parking.Generic.ContinuumCutoffLimit
import Parking.Support.ContUc
import Parking.External.LinearFieldScaling

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking

variable {d : ℕ}

/-! ### A pointwise Chebyshev tail bound for `Z`, from its own covariance -/

/-- **A pointwise tail bound for `Z`, from Chebyshev's inequality applied to its own second
moment.** No Gaussianity is used: `LinearFieldScaling`'s covariance clause already exposes
`∫ (Z ω' t x)²` in closed form; this is the elementary Markov bound on that moment. General in
`t`, `x`; does not by itself bound the SUPREMUM of `Z` over a box (see the module docstring). -/
theorem exists_measureReal_abs_Z_gt_le {Ω' : Type} [MeasurableSpace Ω'] (Q' : Measure Ω')
    [IsProbabilityMeasure Q'] (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ)
    (t : ℝ) (_ht : 0 ≤ t) (x : Fin d → ℝ)
    (hint : Integrable (fun ω' => Z ω' t x * Z ω' t x) Q') (S2 : ℝ)
    (hS2 : ∫ ω', Z ω' t x * Z ω' t x ∂Q' = S2) (M : ℝ) (hM : 0 < M) :
    Q'.real {ω' | M ≤ |Z ω' t x|} ≤ S2 / M ^ 2 := by
  have hnonneg : 0 ≤ᵐ[Q'] fun ω' => Z ω' t x * Z ω' t x := by
    filter_upwards with ω'; exact mul_self_nonneg _
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hint (M ^ 2)
  rw [hS2] at hmarkov
  have hset : {ω' | M ^ 2 ≤ Z ω' t x * Z ω' t x} = {ω' | M ≤ |Z ω' t x|} := by
    ext ω'
    have habs : Z ω' t x * Z ω' t x = |Z ω' t x| * |Z ω' t x| := (abs_mul_abs_self _).symm
    simp only [Set.mem_setOf_eq, habs, sq]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      nlinarith [abs_nonneg (Z ω' t x)]
    · intro h
      nlinarith [abs_nonneg (Z ω' t x)]
  rw [hset] at hmarkov
  have hmarkov' : Q'.real {ω' | M ≤ |Z ω' t x|} * M ^ 2 ≤ S2 := by
    rw [mul_comm]; exact hmarkov
  rw [le_div_iff₀ (by positivity : (0:ℝ) < M ^ 2)]
  exact hmarkov'

/-! ### The randomized cutoff-to-true bound for the clamped stopping-value summand -/

/-- **The time argument, clamped to `[0,s]`.** -/
def clampTime (s k : ℝ) : ℝ := max 0 (min s k)

theorem clampTime_eq_self_of_mem {s k : ℝ} (hk : k ∈ Set.Icc (0 : ℝ) s) : clampTime s k = k := by
  unfold clampTime
  rw [min_eq_right hk.2, max_eq_right hk.1]

theorem clampTime_mem {s : ℝ} (hs : 0 ≤ s) (k : ℝ) : clampTime s k ∈ Set.Icc (0 : ℝ) s := by
  unfold clampTime
  constructor
  · exact le_max_left 0 _
  · exact max_le hs (min_le_left s k)

/-- **`Parking.contUc`'s stopping-value summand's reward, with its time argument clamped to
`[0,s]`.** Agrees with the raw reward `fun k y => -Z ω' (s - k) (x + y)` on `[0,s] × (Fin d → ℝ)`
(`clampTime_eq_self_of_mem`), so
`Parking.Generic.ContinuumCutoffLimit.spatialContValue_congr_of_eqOn_Icc` transfers every
optimal-stopping-value statement between the two without change; unlike the raw reward, its time
argument never leaves `[0,s]`, so a bound on `Z` over the FIXED box `[0,s] × {‖y‖ < A}` bounds it
EVERYWHERE (not merely for `k ∈ [0,s]`). -/
def clampedStoppingReward {Ω' : Type} (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ) (ω' : Ω') (s : ℝ)
    (x : Fin d → ℝ) (k : ℝ) (y : Fin d → ℝ) : ℝ :=
  -Z ω' (s - clampTime s k) (x + y)

theorem clampedStoppingReward_eqOn {Ω' : Type} (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ) (ω' : Ω') (s : ℝ)
    (x : Fin d → ℝ) :
    ∀ k ∈ Set.Icc (0 : ℝ) s, ∀ y : Fin d → ℝ,
      (fun k y => -Z ω' (s - k) (x + y)) k y = clampedStoppingReward Z ω' s x k y := by
  intro k hk y
  unfold clampedStoppingReward
  rw [clampTime_eq_self_of_mem hk]

/-- **The contCutoffReward of the two rewards agree on `[0,s] × (Fin d → ℝ)`.** -/
theorem contCutoffReward_clampedStoppingReward_eqOn {Ω' : Type} (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ)
    (ω' : Ω') (s : ℝ) (x : Fin d → ℝ) (A : ℝ) :
    ∀ k ∈ Set.Icc (0 : ℝ) s, ∀ y : Fin d → ℝ,
      contCutoffReward (fun k y => -Z ω' (s - k) (x + y)) A k y
        = contCutoffReward (clampedStoppingReward Z ω' s x) A k y := by
  intro k hk y
  unfold contCutoffReward
  rw [clampedStoppingReward_eqOn Z ω' s x k hk y]

/-- **The cutoff value of the raw reward equals the cutoff value of the clamped reward**, at
every cutoff level `A`. -/
theorem contCutoffValue_eq_clampedStoppingReward {Ω' : Type} {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → (Fin d → ℝ)) (PB : Measure ΩB) (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ) (ω' : Ω')
    (s : ℝ) (_hs : 0 ≤ s) (x : Fin d → ℝ) (A : ℝ) :
    contCutoffValue B PB (fun k y => -Z ω' (s - k) (x + y)) A s
      = contCutoffValue B PB (clampedStoppingReward Z ω' s x) A s := by
  unfold contCutoffValue
  exact Generic.ContinuumCutoffLimit.spatialContValue_congr_of_eqOn_Icc B PB _ _
    (contCutoffReward_clampedStoppingReward_eqOn Z ω' s x A)

open Classical in
/-- **The continuum stopping-value summand of `Parking.contUc`, constructed as the almost-sure
limit of its own cutoff values** (`Parking.contCutoffValue` at the clamped reward, cutoff radius
`(n:ℝ)+1`), rather than as `Parking.spatialContValue` of the raw, possibly ill-posed reward
(whose own well-posedness, even the integrability of the trivial stopping rule, already needs
a growth control on `Z`). Junk value `0` where no limit is witnessed. -/
noncomputable def contStoppingValue {Ω' : Type} {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → (Fin d → ℝ)) (PB : Measure ΩB) (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ) (ω' : Ω')
    (s : ℝ) (x : Fin d → ℝ) : ℝ :=
  if h : ∃ L : ℝ, Tendsto
      (fun n : ℕ => contCutoffValue B PB (clampedStoppingReward Z ω' s x) ((n : ℝ) + 1) s)
      atTop (𝓝 L)
    then h.choose else 0

/-- **The randomized cutoff-to-true bound for `Parking.contUc`'s own stopping-value summand**:
given, for every `n`, a "good" event (summable exceptional probability) on which `Z` is bounded
within the joint box `[0,s] × {‖y‖ < (n:ℝ)+2}`, and given the resulting exit-probability series is
summable, `Parking.contCutoffValue (ofBrownianSpace B') PB' (fun k y => -Z ω' (s-k)(x+y))
((n:ℝ)+1) s` converges almost surely to `Parking.contStoppingValue (ofBrownianSpace B') PB' Z ω' s
x` as `n → ∞`. Using it requires a maximal inequality for `Z` to supply
`hGoodBound`/`hgoodtail`/`hexitsummable`. -/
theorem ae_tendsto_contCutoffValue_sub_contStoppingValue {Ω' : Type} [MeasurableSpace Ω']
    (Q' : Measure Ω') [IsProbabilityMeasure Q']
    {ΩB' : Type*} [MeasurableSpace ΩB'] (B' : ℝ≥0 → ΩB' → EuclideanSpace ℝ (Fin d))
    (PB' : Measure ΩB') [IsProbabilityMeasure PB']
    (hcont : ∀ ω, Continuous fun s => B' s ω) (hBm : ∀ s, Measurable (B' s))
    (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ)
    (hZcont : ∀ ω', Continuous fun p : ℝ × (Fin d → ℝ) => Z ω' p.1 p.2)
    (s : ℝ) (hs0 : 0 ≤ s) (x : Fin d → ℝ)
    (M : ℕ → ℝ) (hM0 : ∀ n, 0 ≤ M n)
    (Good : ℕ → Set Ω')
    (hGoodBound : ∀ n, ∀ ω' ∈ Good n, ∀ t ∈ Set.Icc (0 : ℝ) s, ∀ y : Fin d → ℝ,
      ‖y‖ < (n : ℝ) + 2 → |Z ω' t (x + y)| ≤ M n)
    (hgoodtail : ∑' n, Q' (Good n)ᶜ ≠ ⊤)
    (hcross : ∀ n ω', ∀ τ : ΩB' → ℝ≥0, IsSpatialContStopping (ofBrownianSpace B') τ →
      (∀ β, (τ β : ℝ) ≤ s) →
      Integrable (fun β => contCutoffReward (clampedStoppingReward Z ω' s x) ((n : ℝ) + 2) (τ β)
        (ofBrownianSpace B' (τ β) β)) PB' →
      Integrable (fun β => contCutoffReward (clampedStoppingReward Z ω' s x) ((n : ℝ) + 1) (τ β)
        (ofBrownianSpace B' (τ β) β)) PB')
    (hcross' : ∀ n ω', ∀ τ : ΩB' → ℝ≥0, IsSpatialContStopping (ofBrownianSpace B') τ →
      (∀ β, (τ β : ℝ) ≤ s) →
      Integrable (fun β => contCutoffReward (clampedStoppingReward Z ω' s x) ((n : ℝ) + 1) (τ β)
        (ofBrownianSpace B' (τ β) β)) PB' →
      Integrable (fun β => contCutoffReward (clampedStoppingReward Z ω' s x) ((n : ℝ) + 2) (τ β)
        (ofBrownianSpace B' (τ β) β)) PB')
    (hexitsummable : Summable
      (fun n : ℕ => M n * PB'.real (contExitEvent B' ((n : ℝ) + 1) s))) :
    ∀ᵐ ω' ∂Q', Tendsto
      (fun n : ℕ => contCutoffValue (ofBrownianSpace B') PB'
          (fun k y => -Z ω' (s - k) (x + y)) ((n : ℝ) + 1) s)
      atTop (𝓝 (contStoppingValue (ofBrownianSpace B') PB' Z ω' s x)) := by
  have hG0m : ∀ ω', Measurable (clampedStoppingReward Z ω' s x 0) := by
    intro ω'
    have hct : clampTime s 0 = 0 := by
      unfold clampTime
      rw [min_eq_right hs0, max_self]
    have heq : clampedStoppingReward Z ω' s x 0 = fun y => -Z ω' s (x + y) := by
      funext y; unfold clampedStoppingReward; rw [hct]; simp
    rw [heq]
    have hcm : Continuous fun y : Fin d → ℝ => -Z ω' s (x + y) := by
      have h1 : Continuous fun y : Fin d → ℝ => ((s, x + y) : ℝ × (Fin d → ℝ)) := by fun_prop
      exact ((hZcont ω').comp h1).neg
    exact hcm.measurable
  have hGoodBound' : ∀ n, ∀ ω' ∈ Good n, ∀ k y, ‖y‖ < (n : ℝ) + 2 →
      |clampedStoppingReward Z ω' s x k y| ≤ M n := by
    intro n ω' hω' k y hy
    unfold clampedStoppingReward
    rw [abs_neg]
    exact hGoodBound n ω' hω' (s - clampTime s k) (by
      have := clampTime_mem hs0 k
      constructor <;> [linarith [this.2]; linarith [this.1]]) y hy
  have hae := Generic.ContinuumCutoffLimit.ae_exists_tendsto_contCutoffValue_of_summable_exitTerm
    Q' B' PB' hcont hBm (clampedStoppingReward Z · s x) s hs0 M hM0 Good hGoodBound' hgoodtail
    hG0m hcross hcross' hexitsummable
  filter_upwards [hae] with ω' hω'
  have hchoice : ∃ L : ℝ, Tendsto
      (fun n : ℕ => contCutoffValue (ofBrownianSpace B') PB' (clampedStoppingReward Z ω' s x)
        ((n : ℝ) + 1) s)
      atTop (𝓝 L) := hω'
  have hval : contStoppingValue (ofBrownianSpace B') PB' Z ω' s x = hchoice.choose := by
    unfold contStoppingValue
    rw [dif_pos hchoice]
  rw [hval]
  have hfun : (fun n : ℕ => contCutoffValue (ofBrownianSpace B') PB'
        (fun k y => -Z ω' (s - k) (x + y)) ((n : ℝ) + 1) s)
      = fun n : ℕ => contCutoffValue (ofBrownianSpace B') PB' (clampedStoppingReward Z ω' s x)
        ((n : ℝ) + 1) s := by
    funext n
    exact contCutoffValue_eq_clampedStoppingReward (ofBrownianSpace B') PB' Z ω' s hs0 x
      ((n : ℝ) + 1)
  rw [hfun]
  exact hchoice.choose_spec

end Parking

end
