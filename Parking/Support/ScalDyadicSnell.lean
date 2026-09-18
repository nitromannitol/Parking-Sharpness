/-
The dyadic Snell recursion of the continuum optimal-stopping value of
`prop:oriented-scaling` (`parking.tex:3204-3222`).

The paper's Step 2 makes the value `U(T)` measurable by a backward recursion
over the dyadic grid of the Brownian horizon: at each dyadic time the value is
the maximum of the reward there and the conditional expectation of the next
value given the data up to that time.  The recursion is a finite induction, and
its measurability needs the conditional expectation to be measurable JOINTLY in
the noise parameter and the Brownian path, which is a result of the shared library
(`LatticeProb.Prob.CondExpParam`); it is carried here as an explicit hypothesis of the
recursion.

The reward is read from a modification `Y` of the noise field that is jointly
continuous in the space-time point, which is what
`Parking.exists_continuous_modification_contZ` supplies from the
multi-parameter Kolmogorov-Chentsov theorem.  Reading the reward from the raw
field `contZ` would not do: `contZ` is the coercion of an `L²` element, chosen
separately at each space-time point, so it has no joint regularity at all.
-/
import Parking.Support.ScalNoiseModification
import LatticeProb.Prob.CondExpParam

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- The reward of the dyadic Snell recursion at the dyadic time `k/2^m`, read
from a modification `Y` of the noise field: the negative of the field at the
space-time point `(k/2^m, B_{k/2^m})`. -/
def dyadicRewardY {ΩB : Type*} (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (B : ℝ≥0 → ΩB → ℝ) (m k : ℕ) : contNoiseSpace × ΩB → ℝ :=
  fun p => -Y (fun i => if i = 0 then (k : ℝ) / (2 : ℝ) ^ m
    else B (Real.toNNReal ((k : ℝ) / (2 : ℝ) ^ m)) p.2) p.1

/-- One backward step of the dyadic Snell recursion: the maximum of the reward
at the dyadic time and the conditional expectation of the next value given the
data up to that time. -/
def dyadicSnellStep {ΩB : Type*} [mB : MeasurableSpace ΩB] (PB : Measure ΩB)
    (𝒢 : MeasurableSpace ΩB) (G : contNoiseSpace × ΩB → ℝ)
    (V : contNoiseSpace × ΩB → ℝ) : contNoiseSpace × ΩB → ℝ :=
  fun p => max (G p) (PB[fun β' => V (p.1, β') | 𝒢] p.2)

/-- The backward recursion from the horizon, as a function of the number of
steps taken. -/
def dyadicSnellRecY {ΩB : Type*} [mB : MeasurableSpace ΩB] (PB : Measure ΩB)
    (𝒢 : ℕ → MeasurableSpace ΩB) (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (B : ℝ≥0 → ΩB → ℝ) (m : ℕ) : ℕ → contNoiseSpace × ΩB → ℝ :=
  Nat.rec (dyadicRewardY Y B m (2 ^ m))
    (fun j ih => dyadicSnellStep (mB := mB) PB (𝒢 (2 ^ m - (j + 1)))
      (dyadicRewardY Y B m (2 ^ m - (j + 1))) ih)

/-- The dyadic Snell recursion of the continuum stopping value: the value at
dyadic time `k/2^m` of the horizon `T`. -/
def dyadicSnellY {ΩB : Type*} [mB : MeasurableSpace ΩB] (PB : Measure ΩB)
    (𝒢 : ℕ → MeasurableSpace ΩB) (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (B : ℝ≥0 → ΩB → ℝ) (m k : ℕ) : contNoiseSpace × ΩB → ℝ :=
  if k ≤ 2 ^ m then dyadicSnellRecY (mB := mB) PB 𝒢 Y B m (2 ^ m - k)
  else fun _ => 0

/-- One backward step of the dyadic Snell recursion, with the conditional
expectation replaced by a jointly measurable representative `E`. -/
def dyadicSnellStepE {ΩB : Type*} (E : (contNoiseSpace × ΩB → ℝ) → contNoiseSpace × ΩB → ℝ)
    (G V : contNoiseSpace × ΩB → ℝ) : contNoiseSpace × ΩB → ℝ :=
  fun p => max (G p) (E V p)

/-- The backward recursion from the horizon, with `E` in place of the
conditional expectation. -/
def dyadicSnellRecE {ΩB : Type*} (E : (contNoiseSpace × ΩB → ℝ) → contNoiseSpace × ΩB → ℝ)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ) (B : ℝ≥0 → ΩB → ℝ) (m : ℕ) :
    ℕ → contNoiseSpace × ΩB → ℝ :=
  Nat.rec (dyadicRewardY Y B m (2 ^ m))
    (fun j ih => dyadicSnellStepE E (dyadicRewardY Y B m (2 ^ m - (j + 1))) ih)

/-- **A modification with continuous sample paths is jointly measurable.**  If
`Y` is measurable in the noise for each space-time point and continuous in the
point for every noise, then it is jointly measurable. -/
theorem measurable_uncurry_of_continuous_modification
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (hY : ∀ z, Measurable (Y z))
    (hcont : ∀ ω, Continuous fun z => Y z ω) :
    Measurable fun p : (Fin 2 → ℝ) × contNoiseSpace => Y p.1 p.2 :=
  measurable_uncurry_of_continuous_of_measurable (u := Y) hcont hY

/-- **The reward of the dyadic Snell recursion is measurable** when the
modification is jointly measurable and the Brownian path is jointly measurable
in `(t, β)`. -/
theorem measurable_dyadicRewardY {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin 2 → ℝ) × contNoiseSpace => Y p.1 p.2)
    (B : ℝ≥0 → ΩB → ℝ) (hB : Measurable fun p : ℝ≥0 × ΩB => B p.1 p.2)
    (m k : ℕ) :
    @Measurable (contNoiseSpace × ΩB) ℝ
      (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _
      (dyadicRewardY (ΩB := ΩB) Y B m k) := by
  unfold dyadicRewardY
  refine Measurable.neg ?_
  let F : contNoiseSpace × ΩB → (Fin 2 → ℝ) × contNoiseSpace :=
    fun p => ((fun i => if i = 0 then (k : ℝ) / (2 : ℝ) ^ m
        else B (Real.toNNReal ((k : ℝ) / (2 : ℝ) ^ m)) p.2), p.1)
  have hF : Measurable F := by
    refine Measurable.prodMk ?_ measurable_fst
    rw [measurable_pi_iff]
    intro i
    by_cases hi : i = 0
    · subst hi; exact measurable_const
    · simp only [if_neg hi]
      exact hB.comp (measurable_const.prodMk measurable_snd)
  exact hY.comp hF

/-- **The recursion with a jointly measurable representative is measurable at
every depth.** -/
theorem measurable_dyadicSnellRecE {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (E : (contNoiseSpace × ΩB → ℝ) → contNoiseSpace × ΩB → ℝ)
    (hE : ∀ r, @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ r →
        @Measurable (contNoiseSpace × ΩB) ℝ
          (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ (E r))
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin 2 → ℝ) × contNoiseSpace => Y p.1 p.2)
    (B : ℝ≥0 → ΩB → ℝ) (hB : Measurable fun p : ℝ≥0 × ΩB => B p.1 p.2) (m : ℕ) :
    ∀ j, @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _
        (dyadicSnellRecE (ΩB := ΩB) E Y B m j) := by
  intro j
  induction j with
  | zero => exact measurable_dyadicRewardY Y hY B hB m (2 ^ m)
  | succ j ih =>
      rw [dyadicSnellRecE]
      exact (measurable_dyadicRewardY Y hY B hB m (2 ^ m - (j + 1))).max (hE _ ih)

/-- **One backward step preserves measurability.** -/
theorem measurable_dyadicSnellStep {ΩB : Type*} [mB : MeasurableSpace ΩB] (PB : Measure ΩB)
    [IsFiniteMeasure PB] (𝒢 : MeasurableSpace ΩB)
    (hJoint : ∀ (r : contNoiseSpace × ΩB → ℝ),
      @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ r →
      (∀ ω, Integrable (fun β => r (ω, β)) PB) →
      @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _
        (fun p : contNoiseSpace × ΩB => PB[fun β => r (p.1, β) | 𝒢] p.2))
    (G V : contNoiseSpace × ΩB → ℝ)
    (hG : @Measurable (contNoiseSpace × ΩB) ℝ
      (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ G)
    (hV : @Measurable (contNoiseSpace × ΩB) ℝ
      (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ V)
    (hint : ∀ ω, Integrable (fun β => V (ω, β)) PB) :
    @Measurable (contNoiseSpace × ΩB) ℝ
      (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _
      (dyadicSnellStep (mB := mB) PB 𝒢 G V) := by
  unfold dyadicSnellStep
  exact hG.max (hJoint V hV hint)

/-- **The backward recursion from the jointly continuous modification is
measurable at every depth**, by induction on the number of steps, given the
joint measurability of the conditional expectation in the noise parameter. -/
theorem measurable_dyadicSnellRecY {ΩB : Type*} [mB : MeasurableSpace ΩB] (PB : Measure ΩB)
    [IsFiniteMeasure PB] (𝒢 : ℕ → MeasurableSpace ΩB)
    (hJoint : ∀ (k : ℕ) (r : contNoiseSpace × ΩB → ℝ),
      @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ r →
      (∀ ω, Integrable (fun β => r (ω, β)) PB) →
      @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _
        (fun p : contNoiseSpace × ΩB => PB[fun β => r (p.1, β) | 𝒢 k] p.2))
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin 2 → ℝ) × contNoiseSpace => Y p.1 p.2)
    (B : ℝ≥0 → ΩB → ℝ) (hB : Measurable fun p : ℝ≥0 × ΩB => B p.1 p.2) (m : ℕ)
    (hintY : ∀ k, ∀ ω, Integrable (fun β => dyadicRewardY Y B m k (ω, β)) PB) :
    ∀ j, @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _
        (dyadicSnellRecY (mB := mB) PB 𝒢 Y B m j) ∧
      (∀ ω, Integrable (fun β => dyadicSnellRecY (mB := mB) PB 𝒢 Y B m j (ω, β)) PB) := by
  intro j
  induction j with
  | zero =>
      refine ⟨?_, ?_⟩
      · simpa [dyadicSnellRecY] using measurable_dyadicRewardY Y hY B hB m (2 ^ m)
      · simpa [dyadicSnellRecY] using hintY (2 ^ m)
  | succ j ih =>
      rw [dyadicSnellRecY]
      refine ⟨?_, ?_⟩
      · exact measurable_dyadicSnellStep (mB := mB) PB (𝒢 (2 ^ m - (j + 1)))
          (fun r hr hi => hJoint (2 ^ m - (j + 1)) r hr hi)
          (dyadicRewardY Y B m (2 ^ m - (j + 1))) _
          (measurable_dyadicRewardY Y hY B hB m _) ih.1 ih.2
      · intro ω
        show Integrable (fun β => max (dyadicRewardY Y B m (2 ^ m - (j + 1)) (ω, β))
          (PB[fun β' => dyadicSnellRecY (mB := mB) PB 𝒢 Y B m j (ω, β') |
            𝒢 (2 ^ m - (j + 1))] β)) PB
        exact (hintY _ ω).sup (MeasureTheory.integrable_condExp (μ := PB)
          (m := 𝒢 (2 ^ m - (j + 1)))
          (f := fun β => dyadicSnellRecY (mB := mB) PB 𝒢 Y B m j (ω, β)))

/-- **The dyadic Snell recursion is measurable at every dyadic time.** -/
theorem measurable_dyadicSnellY {ΩB : Type*} [mB : MeasurableSpace ΩB] (PB : Measure ΩB)
    [IsFiniteMeasure PB] (𝒢 : ℕ → MeasurableSpace ΩB)
    (hJoint : ∀ (k : ℕ) (r : contNoiseSpace × ΩB → ℝ),
      @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ r →
      (∀ ω, Integrable (fun β => r (ω, β)) PB) →
      @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _
        (fun p : contNoiseSpace × ΩB => PB[fun β => r (p.1, β) | 𝒢 k] p.2))
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin 2 → ℝ) × contNoiseSpace => Y p.1 p.2)
    (B : ℝ≥0 → ΩB → ℝ) (hB : Measurable fun p : ℝ≥0 × ΩB => B p.1 p.2) (m : ℕ)
    (hintY : ∀ k, ∀ ω, Integrable (fun β => dyadicRewardY Y B m k (ω, β)) PB) :
    ∀ k, @Measurable (contNoiseSpace × ΩB) ℝ
      (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _
      (dyadicSnellY (mB := mB) PB 𝒢 Y B m k) := by
  intro k
  unfold dyadicSnellY
  by_cases hk : k ≤ 2 ^ m
  · simp only [hk, ↓reduceIte]
    exact (measurable_dyadicSnellRecY PB 𝒢 hJoint Y hY B hB m hintY (2 ^ m - k)).1
  · simp only [hk, ↓reduceIte]
    exact measurable_const

/-- **The dyadic Snell recursion is bounded by the uniform bound on the
reward**, almost everywhere in the Brownian path.  Every step is a maximum of
the reward and a conditional expectation of the previous value, so the bound
propagates backwards; the conditional expectation is bounded only almost
everywhere, which is all the stability estimate needs. -/
theorem ae_abs_dyadicSnellRecY_le {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (𝒢 : ℕ → MeasurableSpace ΩB)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (B : ℝ≥0 → ΩB → ℝ) (m : ℕ) {M : ℝ}
    (hYb : ∀ z ω, |Y z ω| ≤ M) :
    ∀ j ω, ∀ᵐ β ∂PB, |dyadicSnellRecY (mB := mB) PB 𝒢 Y B m j (ω, β)| ≤ M := by
  intro j
  induction j with
  | zero =>
      intro ω
      exact Filter.Eventually.of_forall (fun β => by
        simpa [dyadicSnellRecY, dyadicRewardY, abs_neg] using hYb _ ω)
  | succ j ih =>
      intro ω
      have hstep : dyadicSnellRecY (mB := mB) PB 𝒢 Y B m (j + 1)
          = dyadicSnellStep (mB := mB) PB (𝒢 (2 ^ m - (j + 1)))
              (dyadicRewardY Y B m (2 ^ m - (j + 1)))
              (dyadicSnellRecY (mB := mB) PB 𝒢 Y B m j) := rfl
      rw [hstep]
      simp only [dyadicSnellStep]
      filter_upwards [Filter.Eventually.of_forall (fun β : ΩB =>
          (by simpa [dyadicRewardY, abs_neg] using hYb _ ω :
            |dyadicRewardY Y B m (2 ^ m - (j + 1)) (ω, β)| ≤ M)),
        MeasureTheory.ae_bdd_abs_condExp_of_ae_bdd_abs (μ := PB) (m := 𝒢 (2 ^ m - (j + 1)))
          (f := fun β' => dyadicSnellRecY (mB := mB) PB 𝒢 Y B m j (ω, β')) (ih ω)] with β h1 h2
      refine abs_le.mpr ⟨?_, ?_⟩
      · exact le_max_iff.mpr (Or.inl (abs_le.mp h1).1)
      · exact max_le (abs_le.mp h1).2 (abs_le.mp h2).2

/-- **The dyadic Snell recursion is bounded pointwise** when the conditional
expectation is bounded pointwise, which is the form the stability estimate
supplies. -/
theorem abs_dyadicSnellRecY_le_of_condExp_le {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (𝒢 : ℕ → MeasurableSpace ΩB)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (B : ℝ≥0 → ΩB → ℝ) (m : ℕ) {M : ℝ}
    (hYb : ∀ z ω, |Y z ω| ≤ M)
    (hcond : ∀ (k : ℕ) (V : contNoiseSpace × ΩB → ℝ) (ω : contNoiseSpace),
      (∀ β, |V (ω, β)| ≤ M) →
      ∀ β, |PB[fun β' => V (ω, β') | 𝒢 k] β| ≤ M) :
    ∀ j ω β, |dyadicSnellRecY (mB := mB) PB 𝒢 Y B m j (ω, β)| ≤ M := by
  intro j
  induction j with
  | zero =>
    intro ω β
    simpa [dyadicSnellRecY, dyadicRewardY, abs_neg] using hYb _ ω
  | succ j ih =>
    intro ω β
    rw [show dyadicSnellRecY (mB := mB) PB 𝒢 Y B m (j + 1) =
        dyadicSnellStep (mB := mB) PB (𝒢 (2 ^ m - (j + 1)))
          (dyadicRewardY Y B m (2 ^ m - (j + 1)))
          (dyadicSnellRecY (mB := mB) PB 𝒢 Y B m j) from rfl]
    simp only [dyadicSnellStep]
    refine abs_le.mpr ⟨?_, ?_⟩
    · exact le_max_iff.mpr (Or.inl (abs_le.mp (by simpa [dyadicRewardY, abs_neg] using hYb _ ω)).1)
    · exact max_le (abs_le.mp (by simpa [dyadicRewardY, abs_neg] using hYb _ ω)).2
        (abs_le.mp (hcond (2 ^ m - (j + 1)) (dyadicSnellRecY (mB := mB) PB 𝒢 Y B m j) ω (fun β => ih ω β) β)).2

/-- **The dyadic Snell recursion is bounded pointwise, uniformly in the depth**,
when the conditional expectation is bounded pointwise. -/
theorem abs_dyadicSnellY_le_of_condExp_le {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (𝒢 : ℕ → MeasurableSpace ΩB)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (B : ℝ≥0 → ΩB → ℝ) (m : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hYb : ∀ z ω, |Y z ω| ≤ M)
    (hcond : ∀ (k : ℕ) (V : contNoiseSpace × ΩB → ℝ) (ω : contNoiseSpace),
      (∀ β, |V (ω, β)| ≤ M) →
      ∀ β, |PB[fun β' => V (ω, β') | 𝒢 k] β| ≤ M) :
    ∀ k ω β, |dyadicSnellY (mB := mB) PB 𝒢 Y B m k (ω, β)| ≤ M := by
  intro k ω β
  by_cases hk : k ≤ 2 ^ m
  · simp only [dyadicSnellY, if_pos hk]
    exact abs_dyadicSnellRecY_le_of_condExp_le PB 𝒢 Y B m hYb hcond (2 ^ m - k) ω β
  · simp only [dyadicSnellY, if_neg hk, abs_zero]
    exact hM

/-- **The Brownian average of the dyadic Snell recursion is bounded pointwise**
from a pointwise bound on the recursion. -/
theorem abs_integral_dyadicSnellY_le_of_pointwise {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (𝒢 : ℕ → MeasurableSpace ΩB)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (B : ℝ≥0 → ΩB → ℝ) (m : ℕ) {M : ℝ}
    (hbdd : ∀ ω β, |dyadicSnellY (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β)| ≤ M)
    (hint : ∀ ω, Integrable (fun β => dyadicSnellY (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β)) PB) :
    ∀ ω, |∫ β, dyadicSnellY (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β) ∂PB| ≤ M := by
  intro ω
  have h1 : |∫ β, dyadicSnellY (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β) ∂PB|
      ≤ ∫ β, |dyadicSnellY (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β)| ∂PB :=
    abs_integral_le_integral_abs
  refine le_trans h1 ?_
  have h2 : ∫ β, |dyadicSnellY (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β)| ∂PB
      ≤ ∫ _β : ΩB, M ∂PB :=
    integral_mono (hint ω).abs (integrable_const M) (fun β => hbdd ω β)
  rw [integral_const, probReal_univ] at h2
  simpa using h2

/-- **The Brownian average of the dyadic Snell recursion is bounded by the
uniform bound on the reward.**  The average of a function bounded by `M` almost
everywhere on a probability space is bounded by `M`. -/
theorem abs_integral_dyadicSnellY_le {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (𝒢 : ℕ → MeasurableSpace ΩB)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (B : ℝ≥0 → ΩB → ℝ) (m : ℕ) {M : ℝ}
    (hbdd : ∀ ω, ∀ᵐ β ∂PB, |dyadicSnellY (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β)| ≤ M)
    (hint : ∀ ω, Integrable (fun β => dyadicSnellY (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β)) PB) :
    ∀ ω, |∫ β, dyadicSnellY (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β) ∂PB| ≤ M := by
  intro ω
  have h1 : |∫ β, dyadicSnellY (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β) ∂PB|
      ≤ ∫ β, |dyadicSnellY (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β)| ∂PB :=
    abs_integral_le_integral_abs
  refine le_trans h1 ?_
  have h2 : ∫ β, |dyadicSnellY (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β)| ∂PB
      ≤ ∫ _β : ΩB, M ∂PB :=
    integral_mono_ae (hint ω).abs (integrable_const M) (hbdd ω)
  rw [integral_const, probReal_univ] at h2
  simpa using h2

/-- **The Brownian average of the dyadic Snell recursion is measurable in the
noise.**  The value `U(T)` is a function of the noise alone: the recursion is
jointly measurable in `(noise, Brownian path)` and the Brownian average of a
jointly measurable function is measurable in the noise. -/
theorem measurable_integral_dyadicSnellY {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsFiniteMeasure PB] (𝒢 : ℕ → MeasurableSpace ΩB)
    (hJoint : ∀ (k : ℕ) (r : contNoiseSpace × ΩB → ℝ),
      @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ r →
      (∀ ω, Integrable (fun β => r (ω, β)) PB) →
      @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _
        (fun p : contNoiseSpace × ΩB => PB[fun β => r (p.1, β) | 𝒢 k] p.2))
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin 2 → ℝ) × contNoiseSpace => Y p.1 p.2)
    (B : ℝ≥0 → ΩB → ℝ) (hB : Measurable fun p : ℝ≥0 × ΩB => B p.1 p.2) (m : ℕ)
    (hintY : ∀ k, ∀ ω, Integrable (fun β => dyadicRewardY Y B m k (ω, β)) PB) :
    Measurable fun ω : contNoiseSpace =>
      ∫ β, dyadicSnellY (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β) ∂PB := by
  have hjoint : Measurable fun p : contNoiseSpace × ΩB =>
      dyadicSnellY (mB := mB) PB 𝒢 Y B m (2 ^ m) p :=
    measurable_dyadicSnellY PB 𝒢 hJoint Y hY B hB m hintY (2 ^ m)
  exact (hjoint.stronglyMeasurable.integral_prod_right').measurable

/-- The dyadic Snell recursion at dyadic time `k/2^m`, with `E` in place of the
conditional expectation. -/
def dyadicSnellYE {ΩB : Type*} (E : (contNoiseSpace × ΩB → ℝ) → contNoiseSpace × ΩB → ℝ)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ) (B : ℝ≥0 → ΩB → ℝ) (m k : ℕ) :
    contNoiseSpace × ΩB → ℝ :=
  if k ≤ 2 ^ m then dyadicSnellRecE (ΩB := ΩB) E Y B m (2 ^ m - k) else fun _ => 0

/-- **The recursion with a jointly measurable representative is measurable at
every dyadic time.** -/
theorem measurable_dyadicSnellYE {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (E : (contNoiseSpace × ΩB → ℝ) → contNoiseSpace × ΩB → ℝ)
    (hE : ∀ r, @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ r →
        @Measurable (contNoiseSpace × ΩB) ℝ
          (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ (E r))
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin 2 → ℝ) × contNoiseSpace => Y p.1 p.2)
    (B : ℝ≥0 → ΩB → ℝ) (hB : Measurable fun p : ℝ≥0 × ΩB => B p.1 p.2) (m : ℕ) :
    ∀ k, @Measurable (contNoiseSpace × ΩB) ℝ
      (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _
      (dyadicSnellYE (ΩB := ΩB) E Y B m k) := by
  intro k
  unfold dyadicSnellYE
  by_cases hk : k ≤ 2 ^ m
  · simp only [hk, ↓reduceIte]
    exact measurable_dyadicSnellRecE E hE Y hY B hB m (2 ^ m - k)
  · simp only [hk, ↓reduceIte]
    exact measurable_const

/-- **The Brownian average of the recursion with a jointly measurable
representative is measurable in the noise.** -/
theorem measurable_integral_dyadicSnellYE {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsFiniteMeasure PB]
    (E : (contNoiseSpace × ΩB → ℝ) → contNoiseSpace × ΩB → ℝ)
    (hE : ∀ r, @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ r →
        @Measurable (contNoiseSpace × ΩB) ℝ
          (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ (E r))
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin 2 → ℝ) × contNoiseSpace => Y p.1 p.2)
    (B : ℝ≥0 → ΩB → ℝ) (hB : Measurable fun p : ℝ≥0 × ΩB => B p.1 p.2) (m : ℕ) :
    Measurable fun ω : contNoiseSpace =>
      ∫ β, dyadicSnellYE (ΩB := ΩB) E Y B m (2 ^ m) (ω, β) ∂PB := by
  have hjoint : Measurable fun p : contNoiseSpace × ΩB =>
      dyadicSnellYE (ΩB := ΩB) E Y B m (2 ^ m) p :=
    measurable_dyadicSnellYE E hE Y hY B hB m (2 ^ m)
  exact (hjoint.stronglyMeasurable.integral_prod_right').measurable

/-- **The spatial dyadic Snell recursion**: the reward is read from a jointly
continuous modification of the spatial white noise at the rescaled site of a
`d`-dimensional Brownian path. -/
def dyadicRewardSpatial {d : ℕ} {ΩB : Type*} (Y : (Fin d → ℝ) → contNoiseSpace → ℝ)
    (B : ℝ≥0 → ΩB → Fin d → ℝ) (m k : ℕ) : contNoiseSpace × ΩB → ℝ :=
  fun p => -Y (B (Real.toNNReal ((k : ℝ) / 2 ^ m)) p.2) p.1

def condExpParamRep {ΩB : Type*} [mB : MeasurableSpace ΩB] [StandardBorelSpace ΩB]
    (PB : Measure ΩB) [IsFiniteMeasure PB] (𝒢 : MeasurableSpace ΩB) (h𝒢 : 𝒢 ≤ mB)
    (r : contNoiseSpace × ΩB → ℝ)
    (_hr : @Measurable (contNoiseSpace × ΩB) ℝ
      (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ r)
    (hint : ∀ ω, Integrable (fun β => r (ω, β)) PB) : contNoiseSpace × ΩB → ℝ :=
  Classical.choose (LatticeProb.exists_measurable_condExp_param
    (Ω := contNoiseSpace) (ΩB := ΩB) (mΩ := inferInstance) (mB := mB) PB 𝒢 h𝒢 r _hr hint)

noncomputable def condExpParamOp {ΩB : Type*} [mB : MeasurableSpace ΩB] [StandardBorelSpace ΩB]
    (PB : Measure ΩB) [IsFiniteMeasure PB] (𝒢 : MeasurableSpace ΩB) (h𝒢 : 𝒢 ≤ mB) :
    (contNoiseSpace × ΩB → ℝ) → contNoiseSpace × ΩB → ℝ :=
  fun r => by
  classical
  exact if h : (∃ (hr : @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ r),
        ∀ ω, Integrable (fun β => r (ω, β)) PB) then
      condExpParamRep (mB := mB) PB 𝒢 h𝒢 r h.1 h.2
    else 0

theorem measurable_condExpParamOp_all {ΩB : Type*} [mB : MeasurableSpace ΩB] [StandardBorelSpace ΩB]
    (PB : Measure ΩB) [IsFiniteMeasure PB] (𝒢 : MeasurableSpace ΩB) (h𝒢 : 𝒢 ≤ mB)
    (r : contNoiseSpace × ΩB → ℝ)
    (_hr : @Measurable (contNoiseSpace × ΩB) ℝ
      (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ r) :
    @Measurable (contNoiseSpace × ΩB) ℝ
      (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _
      (condExpParamOp (mB := mB) PB 𝒢 h𝒢 r) := by
  classical
  unfold condExpParamOp
  by_cases h : (∃ (hr : @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ r),
        ∀ ω, Integrable (fun β => r (ω, β)) PB)
  · simp only [dif_pos h]
    exact (Classical.choose_spec (LatticeProb.exists_measurable_condExp_param
      (Ω := contNoiseSpace) (ΩB := ΩB) (mΩ := inferInstance) (mB := mB) PB 𝒢 h𝒢 r h.1 h.2)).1
  · simp only [dif_neg h]
    exact measurable_const

/-- **The Brownian average of the dyadic Snell recursion is measurable in the
noise, with the conditional expectation replaced by the library's jointly
measurable representative.** -/
theorem measurable_integral_dyadicSnellYE_of_library {ΩB : Type*} [mB : MeasurableSpace ΩB]
    [StandardBorelSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (𝒢 : MeasurableSpace ΩB) (h𝒢 : 𝒢 ≤ mB)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin 2 → ℝ) × contNoiseSpace => Y p.1 p.2)
    (B : ℝ≥0 → ΩB → ℝ)
    (hB : @Measurable (ℝ≥0 × ΩB) ℝ
      (@Prod.instMeasurableSpace ℝ≥0 ΩB NNReal.measurableSpace mB) _ fun p => B p.1 p.2) (m : ℕ) :
    Measurable fun ω : contNoiseSpace =>
      ∫ β, dyadicSnellYE (ΩB := ΩB)
        (condExpParamOp (mB := mB) PB 𝒢 h𝒢) Y B m (2 ^ m) (ω, β) ∂PB :=
  measurable_integral_dyadicSnellYE (mB := mB) PB (condExpParamOp (mB := mB) PB 𝒢 h𝒢)
    (fun r hr => measurable_condExpParamOp_all (mB := mB) PB 𝒢 h𝒢 r hr) Y hY B hB m


/-- **The continuum stopping value is measurable in the noise**, from the
library's jointly measurable representative of the conditional expectation and
the convergence of the dyadic recursion to the value. -/
theorem measurable_contStopValue_of_library {ΩB : Type*} [mB : MeasurableSpace ΩB]
    [StandardBorelSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (𝒢 : MeasurableSpace ΩB) (h𝒢 : 𝒢 ≤ mB)
    (Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin 2 → ℝ) × contNoiseSpace => Y p.1 p.2)
    (B : ℝ≥0 → ΩB → ℝ)
    (hB : @Measurable (ℝ≥0 × ΩB) ℝ
      (@Prod.instMeasurableSpace ℝ≥0 ΩB NNReal.measurableSpace mB) _ fun p => B p.1 p.2)
    (v T : ℝ)
    (hlim : ∀ ω, Tendsto (fun m => ∫ β, dyadicSnellYE (ΩB := ΩB)
        (condExpParamOp (mB := mB) PB 𝒢 h𝒢) Y B m (2 ^ m) (ω, β) ∂PB)
      atTop (𝓝 (@contStopValue ΩB mB B PB v T ω))) :
    Measurable fun ω => @contStopValue ΩB mB B PB v T ω :=
  measurable_of_tendsto_metrizable
    (fun m => measurable_integral_dyadicSnellYE_of_library (mB := mB) PB 𝒢 h𝒢 Y hY B hB m)
    (tendsto_pi_nhds.mpr hlim)


/-- **One backward step with a jointly measurable representative preserves
measurability.** -/
theorem measurable_dyadicSnellStepE {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (E : (contNoiseSpace × ΩB → ℝ) → contNoiseSpace × ΩB → ℝ)
    (hE : ∀ r, @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ r →
      @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ (E r))
    (G V : contNoiseSpace × ΩB → ℝ)
    (hG : @Measurable (contNoiseSpace × ΩB) ℝ
      (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ G)
    (hV : @Measurable (contNoiseSpace × ΩB) ℝ
      (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ V) :
    @Measurable (contNoiseSpace × ΩB) ℝ
      (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _
      (dyadicSnellStepE E G V) := by
  unfold dyadicSnellStepE
  exact hG.max (hE V hV)

end Parking
