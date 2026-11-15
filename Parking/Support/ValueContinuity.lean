import Parking.Support.ContUc
import Sandpile.Support.ExplBrownianEnvelope
import LatticeProb.Prob.BrownianPathCoords

/-!
# Continuity of the continuum stopping value

Comparison of stopping values at nearby horizons starts by truncating stopping times.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking.Support

/-- Truncating a natural stopping time at a deterministic time preserves admissibility. -/
theorem isNaturalStopping_min_const {Ω E : Type*} [MeasurableSpace E]
    (B : ℝ≥0 → Ω → E) {τ : Ω → ℝ≥0} (hτ : IsNaturalStopping B τ) (c : ℝ≥0) :
    IsNaturalStopping B (fun ω => min (τ ω) c) := by
  intro t
  by_cases h : c ≤ t
  · have heq : {ω | min (τ ω) c ≤ t} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact (min_le_right _ _).trans h
    rw [heq]
    exact MeasurableSet.univ
  · have heq : {ω | min (τ ω) c ≤ t} = {ω | τ ω ≤ t} := by
      ext ω
      simp only [Set.mem_ofPred_eq, min_le_iff, h, or_false]
    rw [heq]
    exact hτ t

/-- The oscillation of a continuous function over pairs at distance at most `r`. -/
private def compactOscillation {α : Type*} [PseudoMetricSpace α]
    (f : C(α, ℝ)) (r : ℝ) : ℝ :=
  sSup {a : ℝ | ∃ x y : α, dist x y ≤ r ∧ a = dist (f x) (f y)}

private theorem bddAbove_compactOscillation {α : Type*} [PseudoMetricSpace α] [CompactSpace α]
    (f : C(α, ℝ)) (r : ℝ) :
    BddAbove {a : ℝ | ∃ x y : α, dist x y ≤ r ∧ a = dist (f x) (f y)} := by
  refine ⟨2 * ‖f‖, ?_⟩
  rintro a ⟨x, y, _, rfl⟩
  exact f.dist_le_two_norm x y

private theorem dist_le_compactOscillation {α : Type*} [PseudoMetricSpace α] [CompactSpace α]
    (f : C(α, ℝ)) {r : ℝ} {x y : α} (hxy : dist x y ≤ r) :
    dist (f x) (f y) ≤ compactOscillation f r :=
  le_csSup (bddAbove_compactOscillation f r) ⟨x, y, hxy, rfl⟩

private theorem compactOscillation_nonneg {α : Type*} [PseudoMetricSpace α] [CompactSpace α]
    [Nonempty α] (f : C(α, ℝ)) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ compactOscillation f r := by
  obtain ⟨x⟩ := ‹Nonempty α›
  simpa only [dist_self] using dist_le_compactOscillation f (x := x) (y := x) (by simpa using hr)

private theorem compactOscillation_le {α : Type*} [PseudoMetricSpace α] [CompactSpace α]
    [Nonempty α] (f : C(α, ℝ)) {r c : ℝ} (hr : 0 ≤ r)
    (hc : ∀ x y, dist x y ≤ r → dist (f x) (f y) ≤ c) :
    compactOscillation f r ≤ c := by
  obtain ⟨x⟩ := ‹Nonempty α›
  refine csSup_le ⟨0, x, x, by simpa using hr, (dist_self _).symm⟩ ?_
  rintro a ⟨x, y, hxy, rfl⟩
  exact hc x y hxy

private theorem compactOscillation_le_add {α : Type*} [PseudoMetricSpace α] [CompactSpace α]
    [Nonempty α] (f g : C(α, ℝ)) {r : ℝ} (hr : 0 ≤ r) :
    compactOscillation f r ≤ compactOscillation g r + 2 * dist f g := by
  apply compactOscillation_le f hr
  intro x y hxy
  have h1 := dist_le_compactOscillation g hxy
  have h2 : dist (dist (f x) (f y)) (dist (g x) (g y)) ≤ 2 * dist f g := by
    calc
      _ ≤ dist (f x) (g x) + dist (f y) (g y) := dist_dist_dist_le _ _ _ _
      _ ≤ dist f g + dist f g := add_le_add (ContinuousMap.dist_apply_le_dist x)
        (ContinuousMap.dist_apply_le_dist y)
      _ = 2 * dist f g := by ring
  rw [Real.dist_eq] at h2
  have h3 := (abs_le.mp h2).2
  linarith

private theorem continuous_compactOscillation {α : Type*} [PseudoMetricSpace α] [CompactSpace α]
    [Nonempty α] {r : ℝ} (hr : 0 ≤ r) :
    Continuous (fun f : C(α, ℝ) => compactOscillation f r) := by
  apply (LipschitzWith.of_dist_le_mul (K := 2) ?_).continuous
  intro f g
  change dist (compactOscillation f r) (compactOscillation g r) ≤ 2 * dist f g
  rw [Real.dist_eq, abs_sub_le_iff]
  constructor
  · have h := compactOscillation_le_add f g hr
    linarith
  · have h := compactOscillation_le_add g f hr
    rw [dist_comm] at h
    linarith

private theorem compactOscillation_eventually_le {α : Type*} [PseudoMetricSpace α]
    [CompactSpace α] [Nonempty α] (f : C(α, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ r, 0 ≤ r → r ≤ δ → compactOscillation f r ≤ ε := by
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff_le.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) ε hε
  refine ⟨δ, hδ, fun r hr hrδ => compactOscillation_le f hr ?_⟩
  intro x y hxy
  exact hδf (hxy.trans hrδ)

private theorem tendsto_integral_compactOscillation {α Ω : Type*} [PseudoMetricSpace α]
    [CompactSpace α] [Nonempty α] [MeasurableSpace Ω] {P : Measure Ω}
    (W : Ω → C(α, ℝ)) (hW : Measurable W) (D : Ω → ℝ) (hD : Integrable D P)
    (hbound : ∀ ω x, ‖W ω x‖ ≤ D ω) :
    Tendsto (fun n : ℕ => ∫ ω, compactOscillation (W ω) ((n : ℝ)⁻¹) ∂P)
      atTop (𝓝 0) := by
  have hlim (ω : Ω) : Tendsto (fun n : ℕ => compactOscillation (W ω) ((n : ℝ)⁻¹))
      atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := compactOscillation_eventually_le (W ω) (half_pos hε)
    have ht := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (Iio_mem_nhds hδ)
    obtain ⟨N, hN⟩ := eventually_atTop.mp ht
    refine ⟨N, fun n hn => ?_⟩
    have hr : 0 ≤ ((n : ℝ)⁻¹) := inv_nonneg.mpr (Nat.cast_nonneg n)
    have hosc := hmod _ hr (hN n hn).le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (compactOscillation_nonneg (W ω) hr)]
    exact hosc.trans_lt (half_lt_self hε)
  have hdom (n : ℕ) : ∀ᵐ ω ∂P, ‖compactOscillation (W ω) ((n : ℝ)⁻¹)‖ ≤ 2 * D ω := by
    filter_upwards with ω
    have hr : 0 ≤ ((n : ℝ)⁻¹) := inv_nonneg.mpr (Nat.cast_nonneg n)
    rw [Real.norm_eq_abs, abs_of_nonneg (compactOscillation_nonneg (W ω) hr)]
    apply compactOscillation_le (W ω) hr
    intro x y _
    calc dist (W ω x) (W ω y) ≤ ‖W ω x‖ + ‖W ω y‖ := dist_le_norm_add_norm _ _
      _ ≤ D ω + D ω := add_le_add (hbound ω x) (hbound ω y)
      _ = 2 * D ω := by ring
  have h := tendsto_integral_of_dominated_convergence (fun ω => 2 * D ω)
    (fun n => ((continuous_compactOscillation (inv_nonneg.mpr (Nat.cast_nonneg n))).measurable.comp
      hW).aestronglyMeasurable) (hD.const_mul 2) hdom (Filter.Eventually.of_forall hlim)
  simpa only [integral_zero, Function.comp_apply] using h

private theorem integrable_compactOscillation {α Ω : Type*} [PseudoMetricSpace α]
    [CompactSpace α] [Nonempty α] [MeasurableSpace Ω] {P : Measure Ω}
    (W : Ω → C(α, ℝ)) (hW : Measurable W) (D : Ω → ℝ) (hD : Integrable D P)
    (hbound : ∀ ω x, ‖W ω x‖ ≤ D ω) {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun ω => compactOscillation (W ω) r) P := by
  apply (hD.const_mul 2).mono'
    ((continuous_compactOscillation hr).measurable.comp hW).aestronglyMeasurable
  filter_upwards with ω
  change ‖compactOscillation (W ω) r‖ ≤ 2 * D ω
  rw [Real.norm_eq_abs, abs_of_nonneg (compactOscillation_nonneg (W ω) hr)]
  apply compactOscillation_le (W ω) hr
  intro x y _
  calc dist (W ω x) (W ω y) ≤ ‖W ω x‖ + ‖W ω y‖ := dist_le_norm_add_norm _ _
    _ ≤ D ω + D ω := add_le_add (hbound ω x) (hbound ω y)
    _ = 2 * D ω := by ring

private def rewardBox (d : ℕ) (A : ℝ≥0) (R : ℝ) : Set (ℝ × (Fin d → ℝ) × ℝ≥0) :=
  {p | p.1 ∈ Set.Icc 0 (A : ℝ) ∧ p.2.1 ∈ Metric.closedBall 0 R ∧ (p.2.2 : ℝ) ≤ p.1}

private theorem isCompact_rewardBox (d : ℕ) (A : ℝ≥0) (R : ℝ) :
    IsCompact (rewardBox d A R) := by
  have hc : IsClosed (rewardBox d A R) := by
    unfold rewardBox
    exact (isClosed_Icc.preimage continuous_fst).inter
      ((Metric.isClosed_closedBall.preimage (continuous_fst.comp continuous_snd)).inter
        (isClosed_le (NNReal.continuous_coe.comp (continuous_snd.comp continuous_snd))
          continuous_fst))
  have hk : IsCompact (Set.Icc (0 : ℝ) (A : ℝ) ×ˢ
      Metric.closedBall (0 : Fin d → ℝ) R ×ˢ Set.Icc (0 : ℝ≥0) A) :=
    isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)
  apply hk.of_isClosed_subset hc
  rintro ⟨t, x, s⟩ ⟨ht, hx, hs⟩
  exact ⟨ht, hx, zero_le, NNReal.coe_le_coe.mp (hs.trans ht.2)⟩

private theorem rewardBox_nonempty (d : ℕ) (A : ℝ≥0) {R : ℝ} (hR : 0 ≤ R) :
    (rewardBox d A R).Nonempty := by
  refine ⟨(0, 0, 0), ⟨le_rfl, A.coe_nonneg⟩, ?_, le_rfl⟩
  simpa only [Metric.mem_closedBall, dist_self] using hR

private def stoppedRewardField {d : ℕ} {Ω : Type*} (A : ℝ≥0) (R : ℝ)
    (C : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hCc : ∀ ω, Continuous fun t => C t ω)
    (Z : ℝ → (Fin d → ℝ) → ℝ) (hZ : Continuous fun p : ℝ × (Fin d → ℝ) => Z p.1 p.2)
    (ω : Ω) : C(rewardBox d A R, ℝ) := by
  refine ⟨fun p => Z (p.1.1 - p.1.2.2) (p.1.2.1 + ofBrownianSpace C p.1.2.2 ω), ?_⟩
  have ht : Continuous fun p : rewardBox d A R => p.1.1 := continuous_fst.comp continuous_subtype_val
  have hx : Continuous fun p : rewardBox d A R => p.1.2.1 :=
    (continuous_fst.comp continuous_snd).comp continuous_subtype_val
  have hs : Continuous fun p : rewardBox d A R => p.1.2.2 :=
    (continuous_snd.comp continuous_snd).comp continuous_subtype_val
  have hb : Continuous fun p : rewardBox d A R => ofBrownianSpace C p.1.2.2 ω :=
    ((EuclideanSpace.equiv (Fin d) ℝ).continuous.comp (hCc ω)).comp hs
  exact hZ.comp ((ht.sub (NNReal.continuous_coe.comp hs)).prodMk (hx.add hb))

private theorem measurable_stoppedRewardField {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (A : ℝ≥0) (R : ℝ) (C : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hCm : ∀ t, Measurable (C t)) (hCc : ∀ ω, Continuous fun t => C t ω)
    (Z : ℝ → (Fin d → ℝ) → ℝ) (hZ : Continuous fun p : ℝ × (Fin d → ℝ) => Z p.1 p.2) :
    Measurable (stoppedRewardField A R C hCc Z hZ) := by
  let : CompactSpace (rewardBox d A R) := isCompact_iff_compactSpace.mp (isCompact_rewardBox d A R)
  apply ContinuousMap.measurable_iff_eval.mpr
  intro p
  exact hZ.measurable.comp (measurable_const.prodMk
    (measurable_const.add (measurable_ofBrownianSpace (hCm p.1.2.2))))

private theorem one_add_add_le_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 + a + b ≤ (1 + a) * (1 + b) := by
  calc
    1 + a + b ≤ (1 + a + b) + a * b := le_add_of_nonneg_right (mul_nonneg ha hb)
    _ = (1 + a) * (1 + b) := by ring

private theorem exists_stoppedRewardField_envelope {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (A : ℝ≥0) {R : ℝ} (hR : 0 ≤ R)
    (C : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hC : Sandpile.Continuum.IsBrownian d 0 C P) (hCm : ∀ t, Measurable (C t))
    (hCc : ∀ ω, Continuous fun t => C t ω)
    (Z : ℝ → (Fin d → ℝ) → ℝ) (hZ : Continuous fun p : ℝ × (Fin d → ℝ) => Z p.1 p.2)
    (hZg : ∀ T, 0 < T → ∃ C k : ℝ,
      ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Fin d → ℝ)),
        |Z p.1 p.2| ≤ C * (1 + ‖p.2‖) ^ k) :
    ∃ D : Ω → ℝ, Integrable D P ∧
      ∀ ω p, ‖stoppedRewardField A R C hCc Z hZ ω p‖ ≤ D ω := by
  obtain ⟨C₀, k, hk⟩ := hZg ((A : ℝ) + 1) (by positivity)
  let m : ℕ := ⌈k⌉₊
  let c : ℝ := max C₀ 0 * (1 + R) ^ m
  refine ⟨fun ω => c * (1 + Sandpile.Support.brownianPathRadius C 0 A ω) ^ m,
    (Sandpile.Support.integrable_brownian_pathRadius_pow hC hCm hCc A m).const_mul c, ?_⟩
  intro ω p
  have hpath := Sandpile.Support.norm_le_pathRadius C hCc 0 A ω
    (s := p.1.2.2) (NNReal.coe_le_coe.mp (p.2.2.2.trans p.2.1.2))
  simp only [sub_zero] at hpath
  have hrad : 0 ≤ Sandpile.Support.brownianPathRadius C 0 A ω :=
    (norm_nonneg _).trans hpath
  have hx : ‖p.1.2.1‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using p.2.2.1
  have hb : ‖ofBrownianSpace C p.1.2.2 ω‖ ≤ ‖C p.1.2.2 ω‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro i
    exact PiLp.norm_apply_le _ i
  have hsum : ‖p.1.2.1 + ofBrownianSpace C p.1.2.2 ω‖ ≤
      R + Sandpile.Support.brownianPathRadius C 0 A ω :=
    (norm_add_le _ _).trans (add_le_add hx (hb.trans hpath))
  have hbase : 1 ≤ 1 + ‖p.1.2.1 + ofBrownianSpace C p.1.2.2 ω‖ :=
    le_add_of_nonneg_right (norm_nonneg _)
  have hprod : 1 + ‖p.1.2.1 + ofBrownianSpace C p.1.2.2 ω‖ ≤
      (1 + R) * (1 + Sandpile.Support.brownianPathRadius C 0 A ω) := by
    have hmul := one_add_add_le_mul hR hrad
    linarith
  have hpow : (1 + ‖p.1.2.1 + ofBrownianSpace C p.1.2.2 ω‖) ^ k ≤
      (1 + ‖p.1.2.1 + ofBrownianSpace C p.1.2.2 ω‖) ^ m := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hbase (Nat.le_ceil k)
  have htime : p.1.1 - (p.1.2.2 : ℝ) ∈ Set.Icc (0 : ℝ) ((A : ℝ) + 1) := by
    constructor
    · exact sub_nonneg.mpr p.2.2.2
    · exact (sub_le_self _ p.1.2.2.coe_nonneg).trans
        (p.2.1.2.trans (le_add_of_nonneg_right zero_le_one))
  have hgrowth := hk (p.1.1 - (p.1.2.2 : ℝ), p.1.2.1 + ofBrownianSpace C p.1.2.2 ω)
    ⟨htime, Set.mem_univ _⟩
  change ‖Z (p.1.1 - p.1.2.2) (p.1.2.1 + ofBrownianSpace C p.1.2.2 ω)‖ ≤ _
  calc
    _ = |Z (p.1.1 - p.1.2.2) (p.1.2.1 + ofBrownianSpace C p.1.2.2 ω)| := Real.norm_eq_abs _
    _ ≤ C₀ * (1 + ‖p.1.2.1 + ofBrownianSpace C p.1.2.2 ω‖) ^ k := hgrowth
    _ ≤ max C₀ 0 * (1 + ‖p.1.2.1 + ofBrownianSpace C p.1.2.2 ω‖) ^ k :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C₀ 0 * (1 + ‖p.1.2.1 + ofBrownianSpace C p.1.2.2 ω‖) ^ m :=
      mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
    _ ≤ max C₀ 0 * ((1 + R) * (1 + Sandpile.Support.brownianPathRadius C 0 A ω)) ^ m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hprod _) (le_max_right _ _)
    _ = c * (1 + Sandpile.Support.brownianPathRadius C 0 A ω) ^ m := by
      dsimp [c]
      rw [mul_pow, mul_assoc]

/-- A natural stopping time is almost everywhere measurable when the process has almost
    everywhere measurable time slices. -/
private theorem aemeasurable_naturalStopping {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] {P : Measure Ω} {B : ℝ≥0 → Ω → E} {τ : Ω → ℝ≥0}
    (hB : ∀ s, AEMeasurable (B s) P) (hτ : IsNaturalStopping B τ) : AEMeasurable τ P := by
  have hle : ∀ t, pathSigma B t ≤ (inferInstance : MeasurableSpace (NullMeasurableSpace Ω P)) :=
    fun t => iSup₂_le fun s _ => Measurable.comap_le (hB s).nullMeasurable
  have hτm : @Measurable (NullMeasurableSpace Ω P) ℝ≥0 _ _ τ :=
    measurable_of_Iic fun t => hle t _ (hτ t)
  exact NullMeasurable.aemeasurable hτm

/-- A Brownian motion has a measurable continuous version agreeing along almost every path. -/
private theorem exists_measurableBrownianVersion {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hB : LatticeProb.IsBrownianSpace d 0 B P) :
    ∃ C : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d), (∀ t, Measurable (C t)) ∧
      (∀ ω, Continuous fun t => C t ω) ∧ ∀ᵐ ω ∂P, ∀ t, B t ω = C t ω := by
  obtain ⟨C, hCm, hCc, -, hCae, -, -⟩ := hB.exists_continuousVersion
  refine ⟨fun t ω => (Real.sqrt d)⁻¹ • C t ω, ?_, ?_, ?_⟩
  · intro t
    change Measurable (fun ω => (Real.sqrt (d : ℝ))⁻¹ • C t ω)
    exact (hCm t).const_smul ((Real.sqrt (d : ℝ))⁻¹)
  · intro ω
    change Continuous (fun t => (Real.sqrt (d : ℝ))⁻¹ • C t ω)
    exact (hCc ω).const_smul ((Real.sqrt (d : ℝ))⁻¹)
  · filter_upwards [hCae] with ω hω t
    rw [hω t, sub_zero, smul_smul]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact Subsingleton.elim _ _
    · rw [inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)), one_smul]

/-- An indistinguishable version of a Brownian motion has the same Brownian law. -/
private theorem isBrownian_of_ae_eq {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B C : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hB : LatticeProb.IsBrownianSpace d 0 B P)
    (hBC : ∀ᵐ ω ∂P, ∀ t, B t ω = C t ω) :
    Sandpile.Continuum.IsBrownian d 0 C P where
  start := by
    filter_upwards [hB.start, hBC] with ω h0 hω
    rw [← hω 0, h0]
  coord i :=
    { toIsPreBrownianReal := (hB.coord i).toIsPreBrownianReal.congr fun t => by
        filter_upwards [hBC] with ω hω
        rw [hω t]
      cont := by
        filter_upwards [(hB.coord i).cont, hBC] with ω hcont hω
        simpa only [hω] using hcont }
  indep := by
    refine (ProbabilityTheory.iIndepFun_congr fun i => ?_).mp hB.indep
    filter_upwards [hBC] with ω hω
    funext t
    rw [hω t]

/-- A continuous stopped reward is integrable if it has an integrable envelope. -/
private theorem integrable_stoppedReward_of_envelope {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B C : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hCm : ∀ t, Measurable (C t)) (hCc : ∀ ω, Continuous fun t => C t ω)
    (hBC : ∀ᵐ ω ∂P, ∀ t, B t ω = C t ω)
    {Z : ℝ → (Fin d → ℝ) → ℝ} (hZ : Continuous fun p : ℝ × (Fin d → ℝ) => Z p.1 p.2)
    (T : ℝ) (x : Fin d → ℝ) {τ : Ω → ℝ≥0}
    (hτ : IsNaturalStopping (ofBrownianSpace B) τ) (D : Ω → ℝ) (hD : Integrable D P)
    (hdom : ∀ᵐ ω ∂P, ‖-Z (T - τ ω) (x + ofBrownianSpace C (τ ω) ω)‖ ≤ D ω) :
    Integrable (fun ω => -Z (T - τ ω) (x + ofBrownianSpace B (τ ω) ω)) P := by
  have hτm : AEMeasurable τ P := by
    refine aemeasurable_naturalStopping (fun s => ?_) hτ
    refine ⟨ofBrownianSpace C s, measurable_ofBrownianSpace (hCm s), ?_⟩
    filter_upwards [hBC] with ω hω
    simp only [ofBrownianSpace, hω s]
  have hpay : (fun ω => -Z (T - τ ω) (x + ofBrownianSpace B (τ ω) ω)) =ᵐ[P]
      fun ω => -Z (T - τ ω) (x + ofBrownianSpace C (τ ω) ω) := by
    filter_upwards [hBC] with ω hω
    simp only [ofBrownianSpace, hω]
  have hCj : Measurable (Function.uncurry C) :=
    measurable_uncurry_of_continuous_of_measurable hCc hCm
  have hcont : Continuous fun q : ℝ≥0 × EuclideanSpace ℝ (Fin d) =>
      -Z (T - q.1) (x + EuclideanSpace.equiv (Fin d) ℝ q.2) := by
    have hin : Continuous fun q : ℝ≥0 × EuclideanSpace ℝ (Fin d) =>
        ((T - q.1 : ℝ), x + EuclideanSpace.equiv (Fin d) ℝ q.2) := by
      fun_prop
    exact (hZ.comp hin).neg
  have hmeas : AEStronglyMeasurable
      (fun ω => -Z (T - τ ω) (x + ofBrownianSpace C (τ ω) ω)) P :=
    ((hcont.measurable.comp (measurable_fst.prodMk hCj)).comp_aemeasurable
      (hτm.prodMk aemeasurable_id)).aestronglyMeasurable
  exact (hD.mono' hmeas hdom).congr hpay.symm

private theorem integrable_stoppedReward_on_box {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (A : ℝ≥0) (R : ℝ)
    {B C : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hCm : ∀ t, Measurable (C t)) (hCc : ∀ ω, Continuous fun t => C t ω)
    (hBC : ∀ᵐ ω ∂P, ∀ t, B t ω = C t ω)
    (Z : ℝ → (Fin d → ℝ) → ℝ) (hZ : Continuous fun p : ℝ × (Fin d → ℝ) => Z p.1 p.2)
    (D : Ω → ℝ) (hD : Integrable D P)
    (hbound : ∀ ω p, ‖stoppedRewardField A R C hCc Z hZ ω p‖ ≤ D ω)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (A : ℝ)) {x : Fin d → ℝ}
    (hx : x ∈ Metric.closedBall 0 R) {τ : Ω → ℝ≥0}
    (hτ : IsNaturalStopping (ofBrownianSpace B) τ) (hτt : ∀ ω, (τ ω : ℝ) ≤ t) :
    Integrable (fun ω => -Z (t - τ ω) (x + ofBrownianSpace B (τ ω) ω)) P := by
  apply integrable_stoppedReward_of_envelope hCm hCc hBC hZ t x hτ D hD
  filter_upwards with ω
  let p : rewardBox d A R := ⟨(t, x, τ ω), ht, hx, hτt ω⟩
  rw [norm_neg]
  exact hbound ω p

/-- An integrable envelope for stopped rewards bounds the set of attainable payoffs. -/
theorem bddAbove_spatialContPayoffs_of_envelope {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (B : ℝ≥0 → Ω → (Fin d → ℝ)) (P : Measure Ω)
    (G : ℝ → (Fin d → ℝ) → ℝ) (T : ℝ) (D : Ω → ℝ) (hD : Integrable D P)
    (hdom : ∀ τ : Ω → ℝ≥0, IsSpatialContStopping B τ →
      (∀ ω, (τ ω : ℝ) ≤ T) → ∀ᵐ ω ∂P, G (τ ω) (B (τ ω) ω) ≤ D ω) :
    BddAbove (spatialContPayoffs B P G T) := by
  refine ⟨∫ ω, D ω ∂P, ?_⟩
  rintro a ⟨τ, hτ, hτT, hi, rfl⟩
  exact integral_mono_ae hi hD (hdom τ hτ hτT)

private theorem bddAbove_stoppedReward_on_box {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (A : ℝ≥0) (R : ℝ)
    {B C : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hCc : ∀ ω, Continuous fun t => C t ω)
    (hBC : ∀ᵐ ω ∂P, ∀ t, B t ω = C t ω)
    (Z : ℝ → (Fin d → ℝ) → ℝ) (hZ : Continuous fun p : ℝ × (Fin d → ℝ) => Z p.1 p.2)
    (D : Ω → ℝ) (hD : Integrable D P)
    (hbound : ∀ ω p, ‖stoppedRewardField A R C hCc Z hZ ω p‖ ≤ D ω)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (A : ℝ)) {x : Fin d → ℝ}
    (hx : x ∈ Metric.closedBall 0 R) :
    BddAbove (spatialContPayoffs (ofBrownianSpace B) P (fun s y => -Z (t - s) (x + y)) t) := by
  apply bddAbove_spatialContPayoffs_of_envelope _ _ _ _ D hD
  intro τ _ hτt
  filter_upwards [hBC] with ω hω
  let p : rewardBox d A R := ⟨(t, x, τ ω), ht, hx, hτt ω⟩
  have hb : ‖Z (t - τ ω) (x + ofBrownianSpace C (τ ω) ω)‖ ≤ D ω := hbound ω p
  change -Z (t - τ ω) (x + ofBrownianSpace B (τ ω) ω) ≤ D ω
  simp only [ofBrownianSpace, hω]
  have hneg : -Z (t - τ ω) (x + ofBrownianSpace C (τ ω) ω) ≤
      ‖Z (t - τ ω) (x + ofBrownianSpace C (τ ω) ω)‖ := by
    rw [Real.norm_eq_abs]
    exact neg_le_abs _
  simpa only [ofBrownianSpace] using hneg.trans hb

private theorem dist_min_toNNReal_le {t s : ℝ} (hs : 0 ≤ s) {a : ℝ≥0}
    (ha : (a : ℝ) ≤ t) : dist a (min a s.toNNReal) ≤ dist t s := by
  by_cases h : a ≤ s.toNNReal
  · rw [min_eq_left h, dist_self]
    exact dist_nonneg
  · rw [min_eq_right (le_of_not_ge h), NNReal.dist_eq, Real.coe_toNNReal s hs, Real.dist_eq]
    have hsa : s ≤ (a : ℝ) := by
      have h' := NNReal.coe_le_coe.mpr (le_of_not_ge h)
      simpa only [Real.coe_toNNReal s hs] using h'
    rw [abs_of_nonneg (sub_nonneg.mpr hsa), abs_of_nonneg (sub_nonneg.mpr (hsa.trans ha))]
    exact sub_le_sub_right ha s

/-- A uniform comparison of stopped payoffs compares their stopping values, even when the
horizons differ. -/
theorem spatialContValue_le_of_stopped_payoff_le {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (B : ℝ≥0 → Ω → (Fin d → ℝ)) (P : Measure Ω)
    (G H : ℝ → (Fin d → ℝ) → ℝ) (T S c : ℝ) (hS : 0 ≤ S)
    (hne : (spatialContPayoffs B P G T).Nonempty)
    (hb : BddAbove (spatialContPayoffs B P H S))
    (hcompare : ∀ τ : Ω → ℝ≥0, IsSpatialContStopping B τ →
      (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => G (τ ω) (B (τ ω) ω)) P →
      Integrable (fun ω => H (min (τ ω) S.toNNReal) (B (min (τ ω) S.toNNReal) ω)) P ∧
      (∫ ω, G (τ ω) (B (τ ω) ω) ∂P) ≤
        (∫ ω, H (min (τ ω) S.toNNReal) (B (min (τ ω) S.toNNReal) ω) ∂P) + c) :
    spatialContValue B P G T ≤ spatialContValue B P H S + c := by
  apply csSup_le hne
  rintro a ⟨τ, hτ, hτT, hi, rfl⟩
  obtain ⟨hi', hgap⟩ := hcompare τ hτ hτT hi
  have hmem : (∫ ω, H (min (τ ω) S.toNNReal) (B (min (τ ω) S.toNNReal) ω) ∂P) ∈
      spatialContPayoffs B P H S := by
    refine ⟨fun ω => min (τ ω) S.toNNReal, isNaturalStopping_min_const B hτ _, ?_, hi', rfl⟩
    intro ω
    have ht : min (τ ω) S.toNNReal ≤ S.toNNReal := min_le_right _ _
    have ht' : ((min (τ ω) S.toNNReal : ℝ≥0) : ℝ) ≤ (S.toNNReal : ℝ) := by exact_mod_cast ht
    simpa only [Real.coe_toNNReal S hS] using ht'
  have hsup := le_csSup hb hmem
  change _ ≤ spatialContValue B P H S at hsup
  linarith


private theorem stoppedValue_le_add_integral_oscillation {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (A : ℝ≥0) {R : ℝ} (hR : 0 ≤ R)
    {B C : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hCm : ∀ t, Measurable (C t)) (hCc : ∀ ω, Continuous fun t => C t ω)
    (hBC : ∀ᵐ ω ∂P, ∀ t, B t ω = C t ω)
    (Z : ℝ → (Fin d → ℝ) → ℝ) (hZ : Continuous fun p : ℝ × (Fin d → ℝ) => Z p.1 p.2)
    (D : Ω → ℝ) (hD : Integrable D P)
    (hbound : ∀ ω p, ‖stoppedRewardField A R C hCc Z hZ ω p‖ ≤ D ω)
    {t s r : ℝ} {x y : Fin d → ℝ} (ht : t ∈ Set.Icc 0 (A : ℝ))
    (hs : s ∈ Set.Icc 0 (A : ℝ)) (hx : x ∈ Metric.closedBall 0 R)
    (hy : y ∈ Metric.closedBall 0 R) (hr : 0 ≤ r) (hclose : dist (t, x) (s, y) ≤ r) :
    spatialContValue (ofBrownianSpace B) P (fun u z => -Z (t - u) (x + z)) t ≤
      spatialContValue (ofBrownianSpace B) P (fun u z => -Z (s - u) (y + z)) s +
        ∫ ω, compactOscillation (stoppedRewardField A R C hCc Z hZ ω) r ∂P := by
  let : CompactSpace (rewardBox d A R) := isCompact_iff_compactSpace.mp (isCompact_rewardBox d A R)
  let : Nonempty (rewardBox d A R) := (rewardBox_nonempty d A hR).to_subtype
  let W := stoppedRewardField A R C hCc Z hZ
  have hW : Measurable W := measurable_stoppedRewardField A R C hCm hCc Z hZ
  have hWi : Integrable (fun ω => compactOscillation (W ω) r) P :=
    integrable_compactOscillation W hW D hD hbound hr
  have hne : (spatialContPayoffs (ofBrownianSpace B) P (fun u z => -Z (t - u) (x + z)) t).Nonempty := by
    have hi := integrable_stoppedReward_on_box A R hCm hCc hBC Z hZ D hD hbound ht hx
      (τ := fun _ => 0) (isNaturalStopping_const _ 0) (fun _ => by simpa using ht.1)
    refine ⟨_, zero_mem_spatialContPayoffs _ _ _ ht.1 ?_⟩
    simpa only [NNReal.coe_zero] using hi
  have hb := bddAbove_stoppedReward_on_box A R hCc hBC Z hZ D hD hbound hs hy
  apply spatialContValue_le_of_stopped_payoff_le _ _ _ _ t s _ hs.1 hne hb
  intro τ hτ hτt hi
  have hτs (ω : Ω) : ((min (τ ω) s.toNNReal : ℝ≥0) : ℝ) ≤ s := by
    have h : min (τ ω) s.toNNReal ≤ s.toNNReal := min_le_right _ _
    have h' : ((min (τ ω) s.toNNReal : ℝ≥0) : ℝ) ≤ (s.toNNReal : ℝ) := by exact_mod_cast h
    simpa only [Real.coe_toNNReal s hs.1] using h'
  have hi' := integrable_stoppedReward_on_box A R hCm hCc hBC Z hZ D hD hbound hs hy
    (isNaturalStopping_min_const _ hτ _) hτs
  refine ⟨hi', ?_⟩
  have htd : dist t s ≤ r := (le_max_left _ _).trans (by simpa only [Prod.dist_eq] using hclose)
  have hxd : dist x y ≤ r := (le_max_right _ _).trans (by simpa only [Prod.dist_eq] using hclose)
  have hdiff : ∀ᵐ ω ∂P,
      |(-Z (t - τ ω) (x + ofBrownianSpace B (τ ω) ω)) -
        (-Z (s - min (τ ω) s.toNNReal) (y + ofBrownianSpace B (min (τ ω) s.toNNReal) ω))|
        ≤ compactOscillation (W ω) r := by
    filter_upwards [hBC] with ω hω
    let p : rewardBox d A R := ⟨(t, x, τ ω), ht, hx, hτt ω⟩
    let q : rewardBox d A R := ⟨(s, y, min (τ ω) s.toNNReal), hs, hy, hτs ω⟩
    have hpq : dist p q ≤ r := by
      change max (dist t s) (max (dist x y) (dist (τ ω) (min (τ ω) s.toNNReal))) ≤ r
      exact max_le htd (max_le hxd ((dist_min_toNNReal_le hs.1 (hτt ω)).trans htd))
    have hosc := dist_le_compactOscillation (W ω) hpq
    change dist (Z (t - τ ω) (x + ofBrownianSpace C (τ ω) ω))
      (Z (s - min (τ ω) s.toNNReal) (y + ofBrownianSpace C (min (τ ω) s.toNNReal) ω)) ≤ _ at hosc
    rw [Real.dist_eq] at hosc
    have heq : (-Z (t - τ ω) (x + ofBrownianSpace B (τ ω) ω)) -
        (-Z (s - min (τ ω) s.toNNReal) (y + ofBrownianSpace B (min (τ ω) s.toNNReal) ω)) =
        -(Z (t - τ ω) (x + ofBrownianSpace B (τ ω) ω) -
          Z (s - min (τ ω) s.toNNReal) (y + ofBrownianSpace B (min (τ ω) s.toNNReal) ω)) := by ring
    rw [heq, abs_neg]
    simpa only [ofBrownianSpace, hω] using hosc
  have hmono := integral_mono_ae (hi.sub hi').abs hWi hdiff
  have habs := abs_integral_le_integral_abs (μ := P) (f := fun ω =>
    -Z (t - τ ω) (x + ofBrownianSpace B (τ ω) ω) -
      -Z (s - min (τ ω) s.toNNReal) (y + ofBrownianSpace B (min (τ ω) s.toNNReal) ω))
  rw [integral_sub hi hi'] at habs
  have hle := (abs_le.mp (habs.trans hmono)).2
  simpa only [W, NNReal.coe_min, add_comm] using (sub_le_iff_le_add.mp hle)


/-- The continuum Brownian stopping value is jointly continuous in time and space. -/
theorem valueContinuity :
    ∀ (d : ℕ) (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
      (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)),
      LatticeProb.IsBrownianSpace d 0 B PB → (∀ β, Continuous fun s => B s β) →
      ∀ (Ω : Type) (Z : Ω → ℝ → (Fin d → ℝ) → ℝ) (ω : Ω),
        Continuous (fun p : ℝ × (Fin d → ℝ) => Z ω p.1 p.2) → (∀ x, Z ω 0 x = 0) →
        (∀ T, 0 < T → ∃ C k : ℝ, ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Fin d → ℝ)),
          |Z ω p.1 p.2| ≤ C * (1 + ‖p.2‖) ^ k) →
        ContinuousOn (fun p : ℝ × (Fin d → ℝ) =>
            Parking.contUc (Parking.ofBrownianSpace B) PB Z ω p.1 p.2)
          (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Fin d → ℝ))) := by
  intro d ΩB _ PB _ B hB _ Ω Z ω hZ _ hZg
  obtain ⟨C, hCm, hCc, hBC⟩ := exists_measurableBrownianVersion hB
  have hC := isBrownian_of_ae_eq hB hBC
  have hV : ContinuousOn (fun p : ℝ × (Fin d → ℝ) =>
      spatialContValue (ofBrownianSpace B) PB (fun u z => -Z ω (p.1 - u) (p.2 + z)) p.1)
      (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Fin d → ℝ))) := by
    apply Metric.continuousOn_iff.mpr
    intro p hp ε hε
    have hp0 : (0 : ℝ) ≤ p.1 := hp.1
    let A : ℝ≥0 := ⟨p.1 + 1, by linarith⟩
    let R : ℝ := ‖p.2‖ + 1
    have hR : 0 ≤ R := by dsimp [R]; positivity
    let : CompactSpace (rewardBox d A R) := isCompact_iff_compactSpace.mp (isCompact_rewardBox d A R)
    let : Nonempty (rewardBox d A R) := (rewardBox_nonempty d A hR).to_subtype
    obtain ⟨D, hD, hbound⟩ := exists_stoppedRewardField_envelope A hR C hC hCm hCc
      (Z ω) hZ hZg
    let W := stoppedRewardField A R C hCc (Z ω) hZ
    have hW : Measurable W := measurable_stoppedRewardField A R C hCm hCc (Z ω) hZ
    have hlim := tendsto_integral_compactOscillation W hW D hD hbound
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hε))
    let n : ℕ := N + 1
    let r : ℝ := (n : ℝ)⁻¹
    have hn : 0 < n := by dsimp [n]; omega
    have hr : 0 < r := by dsimp [r]; positivity
    have hint : (∫ β, compactOscillation (W β) r ∂PB) < ε := hN n (by dsimp [n]; omega)
    refine ⟨min 1 r, lt_min zero_lt_one hr, ?_⟩
    intro q hq hqp
    have hq1 : dist q.1 p.1 < 1 := by
      have h := (le_max_left (dist q.1 p.1) (dist q.2 p.2)).trans_lt (by
        simpa only [Prod.dist_eq] using hqp)
      exact h.trans_le (min_le_left _ _)
    have hq2 : dist q.2 p.2 < 1 := by
      have h := (le_max_right (dist q.1 p.1) (dist q.2 p.2)).trans_lt (by
        simpa only [Prod.dist_eq] using hqp)
      exact h.trans_le (min_le_left _ _)
    have ht : q.1 ∈ Set.Icc (0 : ℝ) (A : ℝ) := by
      refine ⟨hq.1, ?_⟩
      have h := (abs_sub_lt_iff.mp (by simpa only [Real.dist_eq] using hq1)).1
      change q.1 ≤ p.1 + 1
      linarith
    have hs : p.1 ∈ Set.Icc (0 : ℝ) (A : ℝ) := by
      exact ⟨hp.1, by change p.1 ≤ p.1 + 1; linarith⟩
    have hx : q.2 ∈ Metric.closedBall (0 : Fin d → ℝ) R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h := norm_sub_norm_le q.2 p.2
      rw [← dist_eq_norm] at h
      dsimp [R]
      linarith
    have hy : p.2 ∈ Metric.closedBall (0 : Fin d → ℝ) R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      dsimp [R]
      linarith
    have hclose : dist q p ≤ r := (le_of_lt hqp).trans (min_le_right _ _)
    have h1 := stoppedValue_le_add_integral_oscillation A hR hCm hCc hBC (Z ω) hZ
      D hD hbound ht hs hx hy hr.le hclose
    have h2 := stoppedValue_le_add_integral_oscillation A hR hCm hCc hBC (Z ω) hZ
      D hD hbound hs ht hy hx hr.le (by simpa only [dist_comm] using hclose)
    rw [Real.dist_eq, abs_sub_lt_iff]
    dsimp only [W] at hint
    constructor <;> linarith
  have hsum := hZ.continuousOn.add hV
  convert hsum using 1
  funext p
  rfl

end Parking.Support
