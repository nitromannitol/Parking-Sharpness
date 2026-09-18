/-
The expansion of `S_t` over the values of the configuration at the origin.

`lem:transport` closes with
`S_t = ∑_{m ≥ 1} m P(η(0) = m) P(τ_1 > t | η(0) = m)`, written here with the
joint probabilities so that no null probability is divided by.  It is the
exchangeability of the origin particles summed: a realization with `η(0) = m`
contributes its `m` origin particles, each of which is active with the same
probability as the first.
-/
import Parking.Support.Exchange

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-- The survivor count at the origin is the number of active origin labels. -/
theorem survivorsFrom_eq_tsum (D : Driver d) (t : ℕ) :
    (LatticeProb.survivorsFrom D t 0 : ℝ≥0∞)
      = ∑' i : ℕ, (if (state D t).active (0, i) = true then (1 : ℝ≥0∞) else 0) := by
  classical
  have hz : ∀ i ∉ Finset.range (D.eta 0).toNat,
      (if (state D t).active (0, i) = true then (1 : ℝ≥0∞) else 0) = 0 := by
    intro i hi
    rw [if_neg]
    intro hact
    exact hi (Finset.mem_range.mpr (LatticeProb.lt_toNat_of_active hact))
  rw [tsum_eq_sum hz, Finset.sum_boole]
  rfl

theorem measurableSet_active (t : ℕ) (p : Label d) :
    MeasurableSet {ω : Data d | (state (toDriver ω) t).active p = true} :=
  (measurable_state (d := d) t).1 p (measurableSet_singleton true)

theorem measurableSet_etaEq (m : ℤ) :
    MeasurableSet {ω : Data d | ω.1 0 = m} := by
  have h : {ω : Data d | ω.1 0 = m} = (fun ω : Data d => ω.1 0) ⁻¹' {m} := rfl
  rw [h]
  exact ((measurable_pi_apply (0 : Site d)).comp measurable_fst) (measurableSet_singleton m)

/-- The expected survivor count is the sum over the origin labels of the
probabilities that they are still active. -/
theorem lintegral_survivors (P : Measure (Data d)) (t : ℕ) :
    ∫⁻ ω, (LatticeProb.survivorsFrom (toDriver ω) t 0 : ℝ≥0∞) ∂P
      = ∑' i : ℕ, P {ω : Data d | (state (toDriver ω) t).active (0, i) = true} := by
  classical
  have hrw : ∀ ω : Data d, (LatticeProb.survivorsFrom (toDriver ω) t 0 : ℝ≥0∞)
      = ∑' i : ℕ, Set.indicator {ω : Data d | (state (toDriver ω) t).active (0, i) = true}
          (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    rw [survivorsFrom_eq_tsum]
    refine tsum_congr fun i => ?_
    rw [Set.indicator_apply]
    rfl
  simp only [hrw]
  have hind : ∀ i : ℕ, Measurable (Set.indicator
      {ω : Data d | (state (toDriver ω) t).active (0, i) = true} fun _ => (1 : ℝ≥0∞)) := by
    intro i
    exact Measurable.indicator measurable_const (measurableSet_active t (0, i))
  rw [lintegral_tsum fun i => (hind i).aemeasurable]
  refine tsum_congr fun i => ?_
  rw [lintegral_indicator (measurableSet_active t (0, i))]
  simp

/-- An active origin label has an index below the count at the origin, so the
event splits over the positive values of that count. -/
theorem measure_active_split (P : Measure (Data d)) (t i : ℕ) :
    P {ω : Data d | (state (toDriver ω) t).active (0, i) = true}
      = ∑' m : ℕ, P {ω : Data d | ω.1 0 = (m : ℤ) + 1 ∧
          (state (toDriver ω) t).active (0, i) = true} := by
  classical
  have hcover : {ω : Data d | (state (toDriver ω) t).active (0, i) = true}
      = ⋃ m : ℕ, {ω : Data d | ω.1 0 = (m : ℤ) + 1 ∧
          (state (toDriver ω) t).active (0, i) = true} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hact
      have h1 : i < (ω.1 0).toNat := LatticeProb.lt_toNat_of_active hact
      exact ⟨(ω.1 0).toNat - 1, by omega, hact⟩
    · rintro ⟨m, -, hact⟩
      exact hact
  rw [hcover]
  refine measure_iUnion ?_ ?_
  · intro m m' hmm'
    refine Set.disjoint_left.mpr fun ω hω hω' => hmm' ?_
    have h1 : ω.1 0 = (m : ℤ) + 1 := hω.1
    have h2 : ω.1 0 = (m' : ℤ) + 1 := hω'.1
    omega
  · intro m
    exact (measurableSet_etaEq _).inter (measurableSet_active t (0, i))

/-- Beyond the count at the origin no label is active. -/
theorem measure_active_of_lt (P : Measure (Data d)) (t i m : ℕ) (him : m < i) :
    P {ω : Data d | ω.1 0 = (m : ℤ) + 1 ∧
      (state (toDriver ω) t).active (0, i) = true} = 0 := by
  have hempty : {ω : Data d | ω.1 0 = (m : ℤ) + 1 ∧
      (state (toDriver ω) t).active (0, i) = true} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro heq hact
    have h1 : i < (ω.1 0).toNat := LatticeProb.lt_toNat_of_active hact
    rw [heq] at h1
    omega
  rw [hempty, measure_empty]

/-- **Exchangeability, in the form the expansion needs.**  Given `η(0) = m + 1`,
the origin particle of index `i ≤ m` is active exactly as often as the first
one. -/
theorem measure_active_eq (hd : 1 ≤ d) (μ : Measure (Site d → ℤ))
    [IsProbabilityMeasure μ] (t i m : ℕ) (him : i ≤ m) :
    (dataLaw d μ) {ω : Data d | ω.1 0 = (m : ℤ) + 1 ∧
        (state (toDriver ω) t).active (0, i) = true}
      = (dataLaw d μ) {ω : Data d | ω.1 0 = (m : ℤ) + 1 ∧
        (state (toDriver ω) t).active (0, 0) = true} := by
  classical
  set σ : Equiv.Perm ℕ := Equiv.swap 0 i with hσdef
  have hk : ∀ j, m + 1 ≤ j → σ j = j := by
    intro j hj
    rw [hσdef, Equiv.swap_apply_of_ne_of_ne] <;> omega
  have hE : {ω : Data d | ω.1 0 = ((m + 1 : ℕ) : ℤ)} = {ω : Data d | ω.1 0 = (m : ℤ) + 1} := by
    ext ω; simp [Nat.cast_add, Nat.cast_one]
  have hex := exchangeable_origin hd μ (m + 1) σ hk
  have hT : MeasurableSet {f : ℕ × ℕ → Bool | f (t, 0) = true} := by
    have h : {f : ℕ × ℕ → Bool | f (t, 0) = true}
        = (fun f : ℕ × ℕ → Bool => f (t, 0)) ⁻¹' {true} := rfl
    rw [h]
    exact (measurable_pi_apply ((t, 0) : ℕ × ℕ)) (measurableSet_singleton true)
  have hmσ : Measurable fun ω : Data d => fun q : ℕ × ℕ =>
      (state (toDriver ω) q.1).active (0, σ q.2) :=
    measurable_pi_lambda _ fun q => (measurable_state (d := d) q.1).1 (0, σ q.2)
  have hmid : Measurable fun ω : Data d => fun q : ℕ × ℕ =>
      (state (toDriver ω) q.1).active (0, q.2) :=
    measurable_pi_lambda _ fun q => (measurable_state (d := d) q.1).1 (0, q.2)
  have hval := congrArg (fun ρ : Measure (ℕ × ℕ → Bool) =>
    ρ {f : ℕ × ℕ → Bool | f (t, 0) = true}) hex
  simp only [Measure.map_apply hmσ hT, Measure.map_apply hmid hT] at hval
  have hσ0 : σ 0 = i := by rw [hσdef]; simp
  have hpre1 : (fun ω : Data d => fun q : ℕ × ℕ =>
        (state (toDriver ω) q.1).active (0, σ q.2)) ⁻¹'
        {f : ℕ × ℕ → Bool | f (t, 0) = true}
      = {ω : Data d | (state (toDriver ω) t).active (0, i) = true} := by
    ext ω; simp only [Set.mem_preimage, Set.mem_setOf_eq, hσ0]
  have hpre2 : (fun ω : Data d => fun q : ℕ × ℕ =>
        (state (toDriver ω) q.1).active (0, q.2)) ⁻¹'
        {f : ℕ × ℕ → Bool | f (t, 0) = true}
      = {ω : Data d | (state (toDriver ω) t).active (0, 0) = true} := rfl
  rw [hpre1, hpre2, hE] at hval
  rw [Measure.restrict_apply (measurableSet_active t (0, i)),
    Measure.restrict_apply (measurableSet_active t (0, 0))] at hval
  have hinter1 : {ω : Data d | (state (toDriver ω) t).active (0, i) = true}
      ∩ {ω : Data d | ω.1 0 = (m : ℤ) + 1}
      = {ω : Data d | ω.1 0 = (m : ℤ) + 1 ∧
          (state (toDriver ω) t).active (0, i) = true} := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]; tauto
  have hinter2 : {ω : Data d | (state (toDriver ω) t).active (0, 0) = true}
      ∩ {ω : Data d | ω.1 0 = (m : ℤ) + 1}
      = {ω : Data d | ω.1 0 = (m : ℤ) + 1 ∧
          (state (toDriver ω) t).active (0, 0) = true} := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]; tauto
  rw [hinter1, hinter2] at hval
  exact hval

/-- The expected survivor count expanded over the values of the configuration
at the origin, in `ℝ≥0∞`. -/
theorem lintegral_survivors_expansion (hd : 1 ≤ d) (μ : Measure (Site d → ℤ))
    [IsProbabilityMeasure μ] (t : ℕ) :
    ∫⁻ ω, (LatticeProb.survivorsFrom (toDriver ω) t 0 : ℝ≥0∞) ∂(dataLaw d μ)
      = ∑' m : ℕ, ((m : ℝ≥0∞) + 1) * (dataLaw d μ)
          {ω : Data d | ω.1 0 = (m : ℤ) + 1 ∧
            (state (toDriver ω) t).active (0, 0) = true} := by
  classical
  rw [lintegral_survivors (dataLaw d μ) t]
  have hsplit : ∀ i : ℕ,
      (dataLaw d μ) {ω : Data d | (state (toDriver ω) t).active (0, i) = true}
        = ∑' m : ℕ, (dataLaw d μ) {ω : Data d | ω.1 0 = (m : ℤ) + 1 ∧
            (state (toDriver ω) t).active (0, i) = true} :=
    measure_active_split (dataLaw d μ) t
  simp only [hsplit]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun m => ?_
  have hz : ∀ i ∉ Finset.range (m + 1),
      (dataLaw d μ) {ω : Data d | ω.1 0 = (m : ℤ) + 1 ∧
        (state (toDriver ω) t).active (0, i) = true} = 0 := by
    intro i hi
    exact measure_active_of_lt (dataLaw d μ) t i m (by simpa using hi)
  rw [tsum_eq_sum hz]
  have heq : ∀ i ∈ Finset.range (m + 1),
      (dataLaw d μ) {ω : Data d | ω.1 0 = (m : ℤ) + 1 ∧
        (state (toDriver ω) t).active (0, i) = true}
      = (dataLaw d μ) {ω : Data d | ω.1 0 = (m : ℤ) + 1 ∧
        (state (toDriver ω) t).active (0, 0) = true} := by
    intro i hi
    exact measure_active_eq hd μ t i m (by simpa [Nat.lt_succ_iff] using hi)
  rw [Finset.sum_congr rfl heq, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  congr 1
  push_cast
  ring

/-- **The expansion of `S_t`.**  The last display of `lem:transport`, written
with the joint probabilities. -/
theorem S_expansion (hd : 1 ≤ d) (μ : Measure (Site d → ℤ)) [IsProbabilityMeasure μ]
    (t : ℕ) (hI : Integrable (fun ω : Data d =>
      (LatticeProb.survivorsFrom (toDriver ω) t 0 : ℝ)) (dataLaw d μ)) :
    Summable (fun m : ℕ => ((m : ℝ) + 1) *
        ((dataLaw d μ) {ω : Data d | ω.1 0 = (m : ℤ) + 1 ∧
          (state (toDriver ω) t).active (0, 0) = true}).toReal) ∧
      S (dataLaw d μ) t = ∑' m : ℕ, ((m : ℝ) + 1) *
        ((dataLaw d μ) {ω : Data d | ω.1 0 = (m : ℤ) + 1 ∧
          (state (toDriver ω) t).active (0, 0) = true}).toReal := by
  classical
  haveI : IsProbabilityMeasure (dataLaw d μ) := by
    haveI := stackRankLaw_isProbability (d := d) hd
    unfold dataLaw; infer_instance
  set P := dataLaw d μ with hP
  haveI : IsProbabilityMeasure P := by rw [hP]; infer_instance
  set A : ℕ → Set (Data d) := fun m => {ω : Data d | ω.1 0 = (m : ℤ) + 1 ∧
    (state (toDriver ω) t).active (0, 0) = true} with hA
  set f : ℕ → ℝ≥0∞ := fun m => ((m : ℝ≥0∞) + 1) * P (A m) with hf
  have hterm : ∀ m, f m ≠ ⊤ := by
    intro m
    refine ENNReal.mul_ne_top ?_ ?_
    · exact ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top m, ENNReal.one_ne_top⟩
    · exact measure_ne_top P (A m)
  have hnn : 0 ≤ᵐ[P] fun ω : Data d =>
      (LatticeProb.survivorsFrom (toDriver ω) t 0 : ℝ) :=
    Filter.Eventually.of_forall fun ω => by positivity
  have hmeas : AEStronglyMeasurable (fun ω : Data d =>
      (LatticeProb.survivorsFrom (toDriver ω) t 0 : ℝ)) P :=
    ((measurable_from_countable' fun n : ℕ => (n : ℝ)).comp
      (measurable_survivorsFrom t 0)).aestronglyMeasurable
  have hofReal : ∀ ω : Data d,
      ENNReal.ofReal ((LatticeProb.survivorsFrom (toDriver ω) t 0 : ℕ) : ℝ)
        = (LatticeProb.survivorsFrom (toDriver ω) t 0 : ℝ≥0∞) := by
    intro ω
    exact ENNReal.ofReal_natCast _
  have hlint : ∫⁻ ω, ENNReal.ofReal ((LatticeProb.survivorsFrom (toDriver ω) t 0 : ℕ) : ℝ) ∂P
      = ∑' m : ℕ, f m := by
    simp only [hofReal]
    exact lintegral_survivors_expansion hd μ t
  have hSeq : S P t
      = (∫⁻ ω, ENNReal.ofReal ((LatticeProb.survivorsFrom (toDriver ω) t 0 : ℕ) : ℝ) ∂P).toReal :=
    integral_eq_lintegral_of_nonneg_ae hnn hmeas
  have hfinite : (∑' m : ℕ, f m) ≠ ⊤ := by
    rw [← hlint]
    have hfi := hI.hasFiniteIntegral
    have hrw : ∀ ω : Data d,
        ‖((LatticeProb.survivorsFrom (toDriver ω) t 0 : ℕ) : ℝ)‖ₑ
          = ENNReal.ofReal ((LatticeProb.survivorsFrom (toDriver ω) t 0 : ℕ) : ℝ) := by
      intro ω
      exact Real.enorm_eq_ofReal (by positivity)
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm] at hfi
    simp only [hrw] at hfi
    exact hfi.ne
  have htoReal : ∀ m, (f m).toReal = ((m : ℝ) + 1) * (P (A m)).toReal := by
    intro m
    rw [hf, ENNReal.toReal_mul,
      ENNReal.toReal_add (ENNReal.natCast_ne_top m) ENNReal.one_ne_top,
      ENNReal.toReal_natCast, ENNReal.toReal_one]
  constructor
  · have := ENNReal.summable_toReal hfinite
    simpa only [htoReal] using this
  · rw [hSeq, hlint, ENNReal.tsum_toReal_eq hterm]
    exact tsum_congr htoReal

end Parking

end
