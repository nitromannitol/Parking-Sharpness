/-
The spatial analogue of the dyadic Snell recursion of
`prop:spatial-scaling` (`parking.tex:1679-1737`).

The reward is read from a jointly continuous modification `Y` of the spatial
white noise at the rescaled site of a `d`-dimensional Brownian path, and the
recursion is the same backward Snell step as in the oriented case.  The
measurability of the recursion is the same induction, with the joint
measurability of the conditional expectation in the noise parameter as an
explicit hypothesis (available from
`LatticeProb.exists_measurable_condExp_param`).
-/
import Parking.Support.ScalDyadicSnell

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- The spatial reward: `-Y(B_{k/2^m})` read from the modification `Y` of the
spatial white noise at the rescaled Brownian site. -/
def dyadicRewardSp {d : ℕ} {ΩB : Type*} (Y : (Fin d → ℝ) → contNoiseSpace → ℝ)
    (B : ℝ≥0 → ΩB → Fin d → ℝ) (m k : ℕ) : contNoiseSpace × ΩB → ℝ :=
  fun p => -Y (B (Real.toNNReal ((k : ℝ) / 2 ^ m)) p.2) p.1

/-- The spatial dyadic Snell recursion. -/
def dyadicSnellRecSp {d : ℕ} {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (PB : Measure ΩB) (𝒢 : ℕ → MeasurableSpace ΩB)
    (Y : (Fin d → ℝ) → contNoiseSpace → ℝ)
    (B : ℝ≥0 → ΩB → Fin d → ℝ) (m : ℕ) : ℕ → contNoiseSpace × ΩB → ℝ :=
  Nat.rec (dyadicRewardSp Y B m (2 ^ m))
    (fun j ih => dyadicSnellStep (mB := mB) PB (𝒢 (2 ^ m - (j + 1)))
      (dyadicRewardSp Y B m (2 ^ m - (j + 1))) ih)

/-- The spatial recursion read at the dyadic time `k`. -/
def dyadicSnellSp {d : ℕ} {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (PB : Measure ΩB) (𝒢 : ℕ → MeasurableSpace ΩB)
    (Y : (Fin d → ℝ) → contNoiseSpace → ℝ)
    (B : ℝ≥0 → ΩB → Fin d → ℝ) (m k : ℕ) : contNoiseSpace × ΩB → ℝ :=
  if k ≤ 2 ^ m then dyadicSnellRecSp (mB := mB) PB 𝒢 Y B m (2 ^ m - k) else fun _ => 0

/-- **The spatial reward is jointly measurable.** -/
theorem measurable_dyadicRewardSp {d : ℕ} {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (Y : (Fin d → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin d → ℝ) × contNoiseSpace => Y p.1 p.2)
    (B : ℝ≥0 → ΩB → Fin d → ℝ)
    (hB : Measurable fun p : ℝ≥0 × ΩB => B p.1 p.2) (m k : ℕ) :
    Measurable (dyadicRewardSp (d := d) (ΩB := ΩB) Y B m k) := by
  unfold dyadicRewardSp
  exact (hY.comp (Measurable.prodMk (hB.comp (Measurable.prodMk measurable_const measurable_snd)) measurable_fst)).neg

/-- **The spatial dyadic Snell recursion is jointly measurable** from the joint
measurability of the conditional expectation in the noise parameter. -/
theorem measurable_dyadicSnellRecSp {d : ℕ} {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsFiniteMeasure PB] (𝒢 : ℕ → MeasurableSpace ΩB)
    (hJoint : ∀ (k : ℕ) (r : contNoiseSpace × ΩB → ℝ),
      @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ r →
      (∀ ω, Integrable (fun β => r (ω, β)) PB) →
      @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _
        (fun p : contNoiseSpace × ΩB => PB[fun β => r (p.1, β) | 𝒢 k] p.2))
    (Y : (Fin d → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin d → ℝ) × contNoiseSpace => Y p.1 p.2)
    (B : ℝ≥0 → ΩB → Fin d → ℝ)
    (hB : Measurable fun p : ℝ≥0 × ΩB => B p.1 p.2) (m : ℕ)
    (_hintY : ∀ k, ∀ ω, Integrable (fun β => dyadicRewardSp (d := d) Y B m k (ω, β)) PB)
    (hintV : ∀ j, ∀ ω, Integrable (fun β => dyadicSnellRecSp (mB := mB) PB 𝒢 Y B m j (ω, β)) PB) :
    ∀ j, Measurable (dyadicSnellRecSp (mB := mB) PB 𝒢 Y B m j) := by
  intro j
  induction j with
  | zero =>
      simpa [dyadicSnellRecSp] using measurable_dyadicRewardSp (d := d) Y hY B hB m (2 ^ m)
  | succ j ih =>
      rw [show dyadicSnellRecSp (mB := mB) PB 𝒢 Y B m (j + 1) =
          dyadicSnellStep (mB := mB) PB (𝒢 (2 ^ m - (j + 1)))
            (dyadicRewardSp Y B m (2 ^ m - (j + 1)))
            (dyadicSnellRecSp (mB := mB) PB 𝒢 Y B m j) from rfl]
      exact measurable_dyadicSnellStep PB (𝒢 (2 ^ m - (j + 1)))
        (hJoint (2 ^ m - (j + 1)))
        (dyadicRewardSp Y B m (2 ^ m - (j + 1)))
        (dyadicSnellRecSp (mB := mB) PB 𝒢 Y B m j)
        (measurable_dyadicRewardSp (d := d) Y hY B hB m (2 ^ m - (j + 1))) ih
        (hintV j)

/-- **The spatial recursion is jointly measurable at every dyadic time.** -/
theorem measurable_dyadicSnellSp {d : ℕ} {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsFiniteMeasure PB] (𝒢 : ℕ → MeasurableSpace ΩB)
    (hJoint : ∀ (k : ℕ) (r : contNoiseSpace × ΩB → ℝ),
      @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ r →
      (∀ ω, Integrable (fun β => r (ω, β)) PB) →
      @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _
        (fun p : contNoiseSpace × ΩB => PB[fun β => r (p.1, β) | 𝒢 k] p.2))
    (Y : (Fin d → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin d → ℝ) × contNoiseSpace => Y p.1 p.2)
    (B : ℝ≥0 → ΩB → Fin d → ℝ)
    (hB : Measurable fun p : ℝ≥0 × ΩB => B p.1 p.2) (m : ℕ)
    (_hintY : ∀ k, ∀ ω, Integrable (fun β => dyadicRewardSp (d := d) Y B m k (ω, β)) PB)
    (hintV : ∀ j, ∀ ω, Integrable (fun β => dyadicSnellRecSp (mB := mB) PB 𝒢 Y B m j (ω, β)) PB) :
    ∀ k, Measurable (dyadicSnellSp (mB := mB) PB 𝒢 Y B m k) := by
  intro k
  by_cases hk : k ≤ 2 ^ m
  · simp only [dyadicSnellSp, if_pos hk]
    exact measurable_dyadicSnellRecSp PB 𝒢 hJoint Y hY B hB m _hintY hintV (2 ^ m - k)
  · simp only [dyadicSnellSp, if_neg hk]
    exact measurable_const



/-- **The spatial dyadic Snell recursion is bounded pointwise, uniformly in the
depth**, when the conditional expectation is bounded pointwise. -/
theorem abs_dyadicSnellSp_le_of_condExp_le {d : ℕ} {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (𝒢 : ℕ → MeasurableSpace ΩB)
    (Y : (Fin d → ℝ) → contNoiseSpace → ℝ)
    (B : ℝ≥0 → ΩB → Fin d → ℝ) (m : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hYb : ∀ z ω, |Y z ω| ≤ M)
    (hcond : ∀ (k : ℕ) (V : contNoiseSpace × ΩB → ℝ) (ω : contNoiseSpace),
      (∀ β, |V (ω, β)| ≤ M) →
      ∀ β, |PB[fun β' => V (ω, β') | 𝒢 k] β| ≤ M) :
    ∀ k ω β, |dyadicSnellSp (mB := mB) PB 𝒢 Y B m k (ω, β)| ≤ M := by
  have hrec : ∀ j ω β, |dyadicSnellRecSp (mB := mB) PB 𝒢 Y B m j (ω, β)| ≤ M := by
    intro j
    induction j with
    | zero => intro ω β; simpa [dyadicSnellRecSp, dyadicRewardSp, abs_neg] using hYb _ ω
    | succ j ih =>
      intro ω β
      rw [show dyadicSnellRecSp (mB := mB) PB 𝒢 Y B m (j + 1) =
        dyadicSnellStep (mB := mB) PB (𝒢 (2 ^ m - (j + 1)))
          (dyadicRewardSp Y B m (2 ^ m - (j + 1)))
          (dyadicSnellRecSp (mB := mB) PB 𝒢 Y B m j) from rfl]
      simp only [dyadicSnellStep]
      refine abs_le.mpr ⟨?_, ?_⟩
      · exact le_max_iff.mpr (Or.inl (abs_le.mp (by simpa [dyadicRewardSp, abs_neg] using hYb _ ω)).1)
      · exact max_le (abs_le.mp (by simpa [dyadicRewardSp, abs_neg] using hYb _ ω)).2
          (abs_le.mp (hcond (2 ^ m - (j + 1)) (dyadicSnellRecSp (mB := mB) PB 𝒢 Y B m j) ω
            (fun β => ih ω β) β)).2
  intro k ω β
  by_cases hk : k ≤ 2 ^ m
  · simp only [dyadicSnellSp, if_pos hk]
    exact hrec (2 ^ m - k) ω β
  · simp only [dyadicSnellSp, if_neg hk, abs_zero]
    exact hM



/-- **The Brownian average of the spatial dyadic Snell recursion is bounded
pointwise** from a pointwise bound on the recursion. -/
theorem abs_integral_dyadicSnellSp_le_of_pointwise {d : ℕ} {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (𝒢 : ℕ → MeasurableSpace ΩB)
    (Y : (Fin d → ℝ) → contNoiseSpace → ℝ)
    (B : ℝ≥0 → ΩB → Fin d → ℝ) (m : ℕ) {M : ℝ}
    (hbdd : ∀ ω β, |dyadicSnellSp (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β)| ≤ M)
    (hint : ∀ ω, Integrable (fun β => dyadicSnellSp (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β)) PB) :
    ∀ ω, |∫ β, dyadicSnellSp (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β) ∂PB| ≤ M := by
  intro ω
  have h1 : |∫ β, dyadicSnellSp (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β) ∂PB| ≤
      ∫ β, |dyadicSnellSp (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β)| ∂PB :=
    abs_integral_le_integral_abs
  have h2 : ∫ β, |dyadicSnellSp (mB := mB) PB 𝒢 Y B m (2 ^ m) (ω, β)| ∂PB ≤
      ∫ β, (fun _ => M) β ∂PB :=
    integral_mono (hint ω).abs (integrable_const M) (fun β => hbdd ω β)
  have h3 : ∫ β, (fun _ => M) β ∂PB = M := by simp
  exact h1.trans (h2.trans (le_of_eq h3))

/-- The spatial dyadic Snell recursion with a jointly measurable representative
`E` of the conditional expectation in place of `condExp`. -/
def dyadicSnellRecSpE {d : ℕ} {ΩB : Type*}
    (E : (contNoiseSpace × ΩB → ℝ) → contNoiseSpace × ΩB → ℝ)
    (Y : (Fin d → ℝ) → contNoiseSpace → ℝ)
    (B : ℝ≥0 → ΩB → Fin d → ℝ) (m : ℕ) : ℕ → contNoiseSpace × ΩB → ℝ :=
  Nat.rec (dyadicRewardSp (d := d) Y B m (2 ^ m))
    (fun j ih => dyadicSnellStepE E (dyadicRewardSp (d := d) Y B m (2 ^ m - (j + 1))) ih)

/-- **The spatial recursion with a jointly measurable representative is jointly
measurable.** -/
theorem measurable_dyadicSnellRecSpE {d : ℕ} {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (E : (contNoiseSpace × ΩB → ℝ) → contNoiseSpace × ΩB → ℝ)
    (hE : ∀ r, @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ r →
      @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ (E r))
    (Y : (Fin d → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin d → ℝ) × contNoiseSpace => Y p.1 p.2)
    (B : ℝ≥0 → ΩB → Fin d → ℝ)
    (hB : Measurable fun p : ℝ≥0 × ΩB => B p.1 p.2) (m : ℕ) :
    ∀ j, Measurable (dyadicSnellRecSpE E Y B m j) := by
  intro j
  induction j with
  | zero => simpa [dyadicSnellRecSpE] using measurable_dyadicRewardSp (d := d) Y hY B hB m (2 ^ m)
  | succ j ih =>
      rw [show dyadicSnellRecSpE E Y B m (j + 1) =
          dyadicSnellStepE E (dyadicRewardSp Y B m (2 ^ m - (j + 1)))
            (dyadicSnellRecSpE E Y B m j) from rfl]
      exact measurable_dyadicSnellStepE E hE (dyadicRewardSp Y B m (2 ^ m - (j + 1)))
        (dyadicSnellRecSpE E Y B m j)
        (measurable_dyadicRewardSp (d := d) Y hY B hB m (2 ^ m - (j + 1))) ih

/-- The spatial recursion at dyadic time `k/2^m`, with `E` in place of the
conditional expectation. -/
def dyadicSnellSpE {d : ℕ} {ΩB : Type*}
    (E : (contNoiseSpace × ΩB → ℝ) → contNoiseSpace × ΩB → ℝ)
    (Y : (Fin d → ℝ) → contNoiseSpace → ℝ)
    (B : ℝ≥0 → ΩB → Fin d → ℝ) (m k : ℕ) : contNoiseSpace × ΩB → ℝ :=
  if k ≤ 2 ^ m then dyadicSnellRecSpE E Y B m (2 ^ m - k) else fun _ => 0

/-- **The spatial recursion with a jointly measurable representative is
measurable at every dyadic time.** -/
theorem measurable_dyadicSnellSpE {d : ℕ} {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (E : (contNoiseSpace × ΩB → ℝ) → contNoiseSpace × ΩB → ℝ)
    (hE : ∀ r, @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ r →
      @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ (E r))
    (Y : (Fin d → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin d → ℝ) × contNoiseSpace => Y p.1 p.2)
    (B : ℝ≥0 → ΩB → Fin d → ℝ)
    (hB : Measurable fun p : ℝ≥0 × ΩB => B p.1 p.2) (m : ℕ) :
    ∀ k, Measurable (dyadicSnellSpE E Y B m k) := by
  intro k
  by_cases hk : k ≤ 2 ^ m
  · simp only [dyadicSnellSpE, if_pos hk]
    exact measurable_dyadicSnellRecSpE E hE Y hY B hB m (2 ^ m - k)
  · simp only [dyadicSnellSpE, if_neg hk]
    exact measurable_const


/-- **The Brownian average of the spatial recursion with a jointly measurable
representative is measurable in the noise.** -/
theorem measurable_integral_dyadicSnellSpE {d : ℕ} {ΩB : Type*} [mB : MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsFiniteMeasure PB]
    (E : (contNoiseSpace × ΩB → ℝ) → contNoiseSpace × ΩB → ℝ)
    (hE : ∀ r, @Measurable (contNoiseSpace × ΩB) ℝ
        (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ r →
        @Measurable (contNoiseSpace × ΩB) ℝ
          (@Prod.instMeasurableSpace contNoiseSpace ΩB _ mB) _ (E r))
    (Y : (Fin d → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin d → ℝ) × contNoiseSpace => Y p.1 p.2)
    (B : ℝ≥0 → ΩB → Fin d → ℝ)
    (hB : Measurable fun p : ℝ≥0 × ΩB => B p.1 p.2) (m : ℕ) :
    Measurable fun ω : contNoiseSpace =>
      ∫ β, dyadicSnellSpE (ΩB := ΩB) E Y B m (2 ^ m) (ω, β) ∂PB := by
  have hjoint : Measurable fun p : contNoiseSpace × ΩB =>
      dyadicSnellSpE (ΩB := ΩB) E Y B m (2 ^ m) p :=
    measurable_dyadicSnellSpE E hE Y hY B hB m (2 ^ m)
  exact (hjoint.stronglyMeasurable.integral_prod_right').measurable

/-- **The Brownian average of the spatial recursion is measurable in the noise,
with the conditional expectation replaced by the library's jointly measurable
representative.** -/
theorem measurable_integral_dyadicSnellSpE_of_library {d : ℕ} {ΩB : Type*}
    [mB : MeasurableSpace ΩB] [StandardBorelSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (𝒢 : MeasurableSpace ΩB) (h𝒢 : 𝒢 ≤ mB)
    (Y : (Fin d → ℝ) → contNoiseSpace → ℝ)
    (hY : Measurable fun p : (Fin d → ℝ) × contNoiseSpace => Y p.1 p.2)
    (B : ℝ≥0 → ΩB → Fin d → ℝ)
    (hB : @Measurable (ℝ≥0 × ΩB) (Fin d → ℝ)
      (@Prod.instMeasurableSpace ℝ≥0 ΩB NNReal.measurableSpace mB) _ fun p => B p.1 p.2)
    (m : ℕ) :
    Measurable fun ω : contNoiseSpace =>
      ∫ β, dyadicSnellSpE (ΩB := ΩB) (condExpParamOp (mB := mB) PB 𝒢 h𝒢) Y B m (2 ^ m) (ω, β) ∂PB :=
  measurable_integral_dyadicSnellSpE (mB := mB) PB (condExpParamOp (mB := mB) PB 𝒢 h𝒢)
    (fun r hr => measurable_condExpParamOp_all (mB := mB) PB 𝒢 h𝒢 r hr) Y hY B hB m

end Parking
