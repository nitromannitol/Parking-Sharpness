import Parking.Support.ContUc
import Sandpile.Support.ExplBrownianEnvelope
import LatticeProb.Prob.BrownianPathCoords

/-!
# The Parking Brownian value as a sandpile Brownian value

`Parking.contUc` is built from `Parking.spatialContValue`: a supremum over the stopping times of
the natural filtration of the driving process, read in `Fin d → ℝ` coordinates, in which a rule
counts only when its payoff is integrable. `Sandpile.Continuum.brownianValue` is a supremum over
the stopping times of the natural filtration of a motion on `Sandpile.Continuum.Space d`, in
which every rule counts.

For a Brownian motion `B` started at the origin and a continuous reward of polynomial growth on
time strips, the two values agree, the sandpile value being taken for the motion `x + B` started
at `x`:

* translating by `x` and changing coordinates keeps the natural filtration, so the two classes of
  stopping times coincide (`Parking.Support.isBrownianStopping_add_iff`);
* the payoff of every stopping time bounded by the horizon is integrable, since along a
  measurable continuous version of the motion the reward is dominated by an integrable envelope
  (`Parking.Support.integrable_stoppingPayoff`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace Parking.Support

variable {d : ℕ} {ΩB : Type*} [MeasurableSpace ΩB]

/-- A Brownian motion started at the origin, translated by `x`, is a sandpile Brownian motion
started at `x`. -/
theorem isBrownian_add_of_isBrownianSpace {P : Measure ΩB}
    {B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)} (hB : LatticeProb.IsBrownianSpace d 0 B P)
    (x : Sandpile.Continuum.Space d) :
    Sandpile.Continuum.IsBrownian d x (fun s β => x + B s β) P where
  start := by
    filter_upwards [hB.start] with β hβ
    rw [hβ, add_zero]
  coord i := by
    have hfun : (fun (t : ℝ≥0) (β : ΩB) => Real.sqrt d * ((x + B t β) i - x i)) =
        fun t β => Real.sqrt d * (B t β i - (0 : EuclideanSpace ℝ (Fin d)) i) := by
      funext t β
      simp
    rw [hfun]
    exact hB.coord i
  indep := by
    have h := hB.indep.comp (fun i (v : ℝ≥0 → ℝ) => fun t => x i + v t) (fun i => by fun_prop)
    refine (iIndepFun_congr fun i => ?_).mp h
    filter_upwards with β
    funext t
    simp

/-- A sandpile Brownian motion stays one when it is changed on a null set of paths. -/
theorem isBrownian_congr {x : Sandpile.Continuum.Space d} {P : Measure ΩB}
    {B C : ℝ≥0 → ΩB → Sandpile.Continuum.Space d} (hB : Sandpile.Continuum.IsBrownian d x B P)
    (h : ∀ᵐ β ∂P, ∀ t, B t β = C t β) : Sandpile.Continuum.IsBrownian d x C P where
  start := by
    filter_upwards [hB.start, h] with β h1 h2
    rw [← h2 0, h1]
  coord i :=
    { toIsPreBrownianReal := (hB.coord i).toIsPreBrownianReal.congr fun t => by
        filter_upwards [h] with β hβ
        rw [hβ t]
      cont := by
        filter_upwards [(hB.coord i).cont, h] with β h1 h2
        simpa only [h2] using h1 }
  indep := by
    refine (iIndepFun_congr fun i => ?_).mp hB.indep
    filter_upwards [h] with β hβ
    funext t
    rw [hβ t]

/-- A Brownian motion started at the origin has a version with measurable values and continuous
paths which agrees with it along almost every path. -/
theorem exists_measurable_version {P : Measure ΩB} {B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)}
    (hB : LatticeProb.IsBrownianSpace d 0 B P) :
    ∃ C : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d), (∀ t, Measurable (C t)) ∧
      (∀ β, Continuous fun t => C t β) ∧ ∀ᵐ β ∂P, ∀ t, B t β = C t β := by
  obtain ⟨C, hCm, hCc, -, hCae, -, -⟩ := hB.exists_continuousVersion
  refine ⟨fun t β => (Real.sqrt d)⁻¹ • C t β, fun t => (hCm t).const_smul (Real.sqrt d)⁻¹,
    fun β => (continuous_const_smul (Real.sqrt d)⁻¹).comp (hCc β), ?_⟩
  filter_upwards [hCae] with β hβ t
  rw [hβ t, sub_zero, smul_smul]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Subsingleton.elim _ _
  · rw [inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)), one_smul]

omit [MeasurableSpace ΩB] in
/-- Translating by `x` and reading the motion in `Fin d → ℝ` coordinates keeps the natural
filtration. -/
theorem brownianFiltration_add_eq (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d))
    (x : Sandpile.Continuum.Space d) (t : ℝ≥0) :
    Sandpile.Continuum.brownianFiltration (fun s β => x + B s β) t =
      pathSigma (ofBrownianSpace B) t := by
  have h1 : ∀ s, MeasurableSpace.comap (fun β => x + B s β)
      (inferInstance : MeasurableSpace (Sandpile.Continuum.Space d)) =
        MeasurableSpace.comap (B s) inferInstance := by
    intro s
    have he : MeasurableSpace.comap
        (fun y : Sandpile.Continuum.Space d => (x + y : Sandpile.Continuum.Space d))
        (inferInstance : MeasurableSpace (Sandpile.Continuum.Space d)) =
          (inferInstance : MeasurableSpace (Sandpile.Continuum.Space d)) :=
      (MeasurableEquiv.addLeft x).measurableEmbedding.comap_eq
    rw [show (fun β => x + B s β) = (fun y => x + y) ∘ B s from rfl,
      ← MeasurableSpace.comap_comp, he]
  have h2 : ∀ s, MeasurableSpace.comap (ofBrownianSpace B s)
      (inferInstance : MeasurableSpace (Fin d → ℝ)) =
        MeasurableSpace.comap (B s) inferInstance := by
    intro s
    have he : MeasurableSpace.comap (EuclideanSpace.equiv (Fin d) ℝ)
        (inferInstance : MeasurableSpace (Fin d → ℝ)) =
          (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin d))) :=
      (EuclideanSpace.equiv (Fin d) ℝ).toHomeomorph.toMeasurableEquiv.measurableEmbedding.comap_eq
    rw [show ofBrownianSpace B s = (EuclideanSpace.equiv (Fin d) ℝ) ∘ B s from rfl,
      ← MeasurableSpace.comap_comp, he]
  show (⨆ s ≤ t, MeasurableSpace.comap (fun β => x + B s β) _) =
    ⨆ s ≤ t, MeasurableSpace.comap (ofBrownianSpace B s) _
  simp only [h1, h2]

omit [MeasurableSpace ΩB] in
/-- The stopping times of the natural filtration of `x + B` are those of `B` read in
`Fin d → ℝ` coordinates. -/
theorem isBrownianStopping_add_iff (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d))
    (x : Sandpile.Continuum.Space d) (τ : ΩB → ℝ≥0) :
    Sandpile.Continuum.IsBrownianStopping (fun s β => x + B s β) τ ↔
      IsNaturalStopping (ofBrownianSpace B) τ := by
  unfold Sandpile.Continuum.IsBrownianStopping IsStoppingTime IsNaturalStopping
  refine forall_congr' fun t => ?_
  rw [brownianFiltration_add_eq]
  have hset : {ω | ((τ ω : ℝ≥0∞) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} = {ω | τ ω ≤ t} :=
    Set.ext fun ω => WithTop.coe_le_coe
  change MeasurableSet[pathSigma (ofBrownianSpace B) t]
      {ω | ((τ ω : ℝ≥0∞) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} ↔ _
  rw [hset]

/-- A stopping time of the natural filtration of a process with almost everywhere measurable
values is almost everywhere measurable. -/
theorem aemeasurable_of_isNaturalStopping {P : Measure ΩB} {E : Type*} [MeasurableSpace E]
    {X : ℝ≥0 → ΩB → E} (hX : ∀ s, AEMeasurable (X s) P) {τ : ΩB → ℝ≥0}
    (hτ : IsNaturalStopping X τ) : AEMeasurable τ P := by
  have hle : ∀ t, pathSigma X t ≤ (inferInstance : MeasurableSpace (NullMeasurableSpace ΩB P)) :=
    fun t => iSup₂_le fun s _ => Measurable.comap_le (hX s).nullMeasurable
  have hτm : @Measurable (NullMeasurableSpace ΩB P) ℝ≥0 _ _ τ :=
    measurable_of_Iic fun t => hle t _ (hτ t)
  exact NullMeasurable.aemeasurable hτm

/-- Polynomial growth on a time strip gives the growth bound of the sandpile envelope, about the
starting point of the translated motion. -/
theorem exists_growth_bound {Z : ℝ → (Fin d → ℝ) → ℝ} {T C k : ℝ}
    (hZ : ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Fin d → ℝ)),
      |Z p.1 p.2| ≤ C * (1 + ‖p.2‖) ^ k) (x : Fin d → ℝ) :
    ∃ (C' : ℝ) (p : ℕ), 0 ≤ C' ∧ ∀ v : ℝ, 0 ≤ v → v ≤ T → ∀ y : Sandpile.Continuum.Space d,
      ‖Z v (WithLp.ofLp y)‖ ≤ C' * (1 + ‖y - WithLp.toLp 2 x‖) ^ p := by
  refine ⟨max C 0 * (1 + ‖x‖) ^ ⌈k⌉₊, ⌈k⌉₊, by positivity, fun v hv0 hvT y => ?_⟩
  have hy : ‖WithLp.ofLp y‖ ≤ ‖x‖ + ‖y - WithLp.toLp 2 x‖ := by
    have hw : WithLp.ofLp y = x + WithLp.ofLp (y - WithLp.toLp 2 x) := by
      simp
    have hsup : ‖WithLp.ofLp (y - WithLp.toLp 2 x)‖ ≤ ‖y - WithLp.toLp 2 x‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => PiLp.norm_apply_le _ i
    rw [hw]
    exact (norm_add_le _ _).trans (by linarith)
  have hbase : 1 ≤ 1 + ‖WithLp.ofLp y‖ := le_add_of_nonneg_right (norm_nonneg _)
  have hprod : 1 + ‖WithLp.ofLp y‖ ≤ (1 + ‖x‖) * (1 + ‖y - WithLp.toLp 2 x‖) := by
    have hab := mul_nonneg (norm_nonneg x) (norm_nonneg (y - WithLp.toLp 2 x))
    calc 1 + ‖WithLp.ofLp y‖ ≤ 1 + ‖x‖ + ‖y - WithLp.toLp 2 x‖ := by linarith
      _ ≤ 1 + ‖x‖ + ‖y - WithLp.toLp 2 x‖ + ‖x‖ * ‖y - WithLp.toLp 2 x‖ := by linarith
      _ = (1 + ‖x‖) * (1 + ‖y - WithLp.toLp 2 x‖) := by ring
  have hpow : (1 + ‖WithLp.ofLp y‖) ^ k ≤ (1 + ‖WithLp.ofLp y‖) ^ ⌈k⌉₊ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hbase (Nat.le_ceil k)
  calc ‖Z v (WithLp.ofLp y)‖ = |Z (v, WithLp.ofLp y).1 (v, WithLp.ofLp y).2| := rfl
    _ ≤ C * (1 + ‖WithLp.ofLp y‖) ^ k := hZ _ ⟨⟨hv0, hvT⟩, Set.mem_univ _⟩
    _ ≤ max C 0 * (1 + ‖WithLp.ofLp y‖) ^ k :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (1 + ‖WithLp.ofLp y‖) ^ ⌈k⌉₊ :=
        mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
    _ ≤ max C 0 * ((1 + ‖x‖) * (1 + ‖y - WithLp.toLp 2 x‖)) ^ ⌈k⌉₊ :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hprod _) (le_max_right _ _)
    _ = max C 0 * (1 + ‖x‖) ^ ⌈k⌉₊ * (1 + ‖y - WithLp.toLp 2 x‖) ^ ⌈k⌉₊ := by
        rw [mul_pow, mul_assoc]

/-- **Every bounded stopping payoff is integrable.** For a Brownian motion started at the origin
and a continuous reward of polynomial growth on time strips, the payoff of a stopping time of the
natural filtration bounded by the horizon is integrable. -/
theorem integrable_stoppingPayoff {PB : Measure ΩB} [IsProbabilityMeasure PB]
    {B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)} (hB : LatticeProb.IsBrownianSpace d 0 B PB)
    {Z : ℝ → (Fin d → ℝ) → ℝ} (hZc : Continuous fun p : ℝ × (Fin d → ℝ) => Z p.1 p.2)
    (hZg : ∀ T, 0 < T → ∃ C k : ℝ, ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Fin d → ℝ)),
      |Z p.1 p.2| ≤ C * (1 + ‖p.2‖) ^ k)
    {T : ℝ} (hT : 0 ≤ T) (x : Fin d → ℝ) {τ : ΩB → ℝ≥0}
    (hτ : IsNaturalStopping (ofBrownianSpace B) τ) (hτT : ∀ β, (τ β : ℝ) ≤ T) :
    Integrable (fun β => -Z (T - τ β) (x + ofBrownianSpace B (τ β) β)) PB := by
  obtain ⟨C, hCm, hCc, hBC⟩ := exists_measurable_version hB
  have hτm : AEMeasurable τ PB := by
    refine aemeasurable_of_isNaturalStopping (fun s => ?_) hτ
    refine ⟨ofBrownianSpace C s, measurable_ofBrownianSpace (hCm s), ?_⟩
    filter_upwards [hBC] with β hβ
    simp only [ofBrownianSpace, hβ s]
  have hpay : (fun β => -Z (T - τ β) (x + ofBrownianSpace B (τ β) β)) =ᵐ[PB]
      fun β => -Z (T - τ β) (x + ofBrownianSpace C (τ β) β) := by
    filter_upwards [hBC] with β hβ
    simp only [ofBrownianSpace, hβ]
  have hCj : Measurable (Function.uncurry C) :=
    measurable_uncurry_of_continuous_of_measurable hCc hCm
  have hcont : Continuous fun q : ℝ≥0 × EuclideanSpace ℝ (Fin d) =>
      -Z (T - q.1) (x + EuclideanSpace.equiv (Fin d) ℝ q.2) := by
    have hin : Continuous fun q : ℝ≥0 × EuclideanSpace ℝ (Fin d) =>
        ((T - q.1 : ℝ), x + EuclideanSpace.equiv (Fin d) ℝ q.2) := by
      fun_prop
    exact (hZc.comp hin).neg
  have hmeas : AEStronglyMeasurable
      (fun β => -Z (T - τ β) (x + ofBrownianSpace C (τ β) β)) PB :=
    ((hcont.measurable.comp (measurable_fst.prodMk hCj)).comp_aemeasurable
      (hτm.prodMk aemeasurable_id)).aestronglyMeasurable
  obtain ⟨C₀, k, hk⟩ := hZg (T + 1) (by linarith)
  obtain ⟨C', p, hC', hg⟩ := exists_growth_bound hk x
  have hBx : Sandpile.Continuum.IsBrownian d (WithLp.toLp 2 x)
      (fun s β => WithLp.toLp 2 x + C s β) PB :=
    isBrownian_congr (isBrownian_add_of_isBrownianSpace hB _) (by
      filter_upwards [hBC] with β hβ t
      rw [hβ t])
  obtain ⟨D, hD, hDle⟩ := Sandpile.Support.exists_brownian_envelope_of_polynomial_growth hBx
    (fun s => (hCm s).const_add _) (fun β => continuous_const.add (hCc β))
    (fun t y => Z t (WithLp.ofLp y)) ⟨T, hT⟩ C' hC' p (fun v hv y =>
      hg v v.2 (le_trans (NNReal.coe_le_coe.2 hv) (le_add_of_nonneg_right zero_le_one)) y)
  refine (Integrable.mono' hD hmeas (Filter.Eventually.of_forall fun β => ?_)).congr hpay.symm
  have hτT' : τ β ≤ (⟨T, hT⟩ : ℝ≥0) := NNReal.coe_le_coe.1 (hτT β)
  have h := hDle β ⟨T - τ β, sub_nonneg.2 (hτT β)⟩
    (NNReal.coe_le_coe.1 (sub_le_self _ (τ β).2)) (τ β) hτT'
  rw [norm_neg]
  exact h

/-- **The Parking Brownian value is the sandpile Brownian value.** For a Brownian motion `B`
started at the origin with continuous paths, a continuous reward `Z ω` of polynomial growth on
time strips, a horizon `T ≥ 0` and a point `x`, the continuum spatial value `Parking.contUc` is
the sandpile value `Sandpile.Continuum.brownianValue` of the motion `x + B`. -/
theorem valueBridge : ∀ (d : ℕ) (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB)
    [IsProbabilityMeasure PB] (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)),
    LatticeProb.IsBrownianSpace d 0 B PB → (∀ β, Continuous fun s => B s β) →
    ∀ (Ω : Type) (Z : Ω → ℝ → (Fin d → ℝ) → ℝ) (ω : Ω),
      Continuous (fun p : ℝ × (Fin d → ℝ) => Z ω p.1 p.2) →
      (∀ T, 0 < T → ∃ C k : ℝ, ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Fin d → ℝ)),
        |Z ω p.1 p.2| ≤ C * (1 + ‖p.2‖) ^ k) →
      ∀ (T : ℝ) (x : Fin d → ℝ), 0 ≤ T →
        Parking.contUc (Parking.ofBrownianSpace B) PB Z ω T x =
          Sandpile.Continuum.brownianValue
            (fun s β => (WithLp.toLp 2 x : Sandpile.Continuum.Space d) + B s β) PB
            (fun t y => Z ω t (WithLp.ofLp y)) T (WithLp.toLp 2 x) := by
  intro d ΩB _ PB _ B hB _ Ω Z ω hZc hZg T x hT
  unfold Parking.contUc Sandpile.Continuum.brownianValue Sandpile.Continuum.brownianDiscount
    spatialContValue spatialContPayoffs
  congr 2
  ext a
  constructor
  · rintro ⟨τ, hτ, hτT, -, rfl⟩
    exact ⟨τ, (isBrownianStopping_add_iff B _ τ).2 hτ, hτT, rfl⟩
  · rintro ⟨τ, hτ, hτT, rfl⟩
    have hτ' := (isBrownianStopping_add_iff B _ τ).1 hτ
    exact ⟨τ, hτ', hτT, integrable_stoppingPayoff hB hZc hZg hT x hτ' hτT, rfl⟩

end Parking.Support
