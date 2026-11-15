import Parking.Support.ValueBridge
import Sandpile.Frozen.BrownianValueMonotone
import Sandpile.Support.MainExplContValueMeas
import Sandpile.Support.ContValueScaling

/-!
# Regularity of the Brownian value field

For a continuous field `Z` that agrees almost surely with the Gaussian heat potential at every
nonnegative time, `Parking.contUc` is, after a modification of `Z` on a null event, a
space-time value field with the four regularity clauses of
`Parking.External.SpatialOdometerScaling`: zero initial value, joint continuity, monotonicity in
time and coordinatewise measurability.

The argument combines the value bridge `Parking.Support.valueBridge` with three inputs.

* For each rational horizon `q > 0`, the Brownian value of the Gaussian heat potential is
  nondecreasing on `[0, q]` almost surely (`Sandpile.Frozen.brownian_value_mono_horizon`). The
  exceptional sets of the rational horizons form a countable union. Joint continuity of the value
  in the horizon then upgrades monotonicity from `[0, q]` to all of `[0, ∞)`, since every time `t`
  is the limit of rational horizons above it.
* For each fixed point, the value is almost everywhere equal to a measurable function of the
  sample (`Sandpile.Support.aemeasurable_brownianValue_of_growth`). Choosing a measurable null
  set that contains the exceptional sets over a countable dense set of points, and using joint
  continuity of the modified value, gives measurability at every point.
* On the null set the field is replaced by zero, whose value is zero.

Joint continuity of the value of a continuous reward of polynomial growth is a hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Parking.Support

variable {d : ℕ}

/-- **Polynomial growth transfers to the Euclidean norm.** A growth bound for a field on a time
strip, in the sup norm of `Fin d → ℝ`, gives a growth bound for the field read through
`WithLp.ofLp` in the Euclidean norm of `Sandpile.Continuum.Space d`. -/
theorem exists_euclidean_growth {Z : ℝ → (Fin d → ℝ) → ℝ} {T C k : ℝ}
    (hZ : ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Fin d → ℝ)),
      |Z p.1 p.2| ≤ C * (1 + ‖p.2‖) ^ k) :
    ∃ C' k' : ℝ, ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
      |Z q.1 (WithLp.ofLp q.2)| ≤ C' * (1 + ‖q.2‖) ^ k' := by
  refine ⟨max C 0, max k 0, fun q hq => ?_⟩
  have hy : ‖WithLp.ofLp q.2‖ ≤ ‖q.2‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => PiLp.norm_apply_le _ i
  have hbase : 1 ≤ 1 + ‖WithLp.ofLp q.2‖ := le_add_of_nonneg_right (norm_nonneg _)
  calc |Z q.1 (WithLp.ofLp q.2)| = |Z (q.1, WithLp.ofLp q.2).1 (q.1, WithLp.ofLp q.2).2| := rfl
    _ ≤ C * (1 + ‖WithLp.ofLp q.2‖) ^ k := hZ _ ⟨hq.1, Set.mem_univ _⟩
    _ ≤ max C 0 * (1 + ‖WithLp.ofLp q.2‖) ^ k :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (1 + ‖WithLp.ofLp q.2‖) ^ (max k 0) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hbase (le_max_left _ _)) (le_max_right _ _)
    _ ≤ max C 0 * (1 + ‖q.2‖) ^ (max k 0) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) (by linarith) (le_max_right _ _))
          (le_max_right _ _)

/-- **The value of the zero reward is zero** at every nonnegative horizon. -/
theorem spatialContValue_zero_reward {ΩB : Type*} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → (Fin d → ℝ)) (PB : Measure ΩB) [IsProbabilityMeasure PB] {T : ℝ} (hT : 0 ≤ T) :
    Parking.spatialContValue B PB (fun _ _ => (0 : ℝ)) T = 0 := by
  unfold Parking.spatialContValue
  have hset : Parking.spatialContPayoffs B PB (fun _ _ => (0 : ℝ)) T = {0} := by
    ext a
    simp only [Parking.spatialContPayoffs, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨τ, -, -, -, rfl⟩
      simp
    · intro ha
      exact ⟨fun _ => 0, Parking.isNaturalStopping_const B 0, fun _ => by simpa using hT,
        integrable_const _, by simp [ha]⟩
  rw [hset, csSup_singleton]

/-- **The Parking value at a nonnegative horizon is the sandpile value of any field that
agrees with the Parking field at nonnegative times.** -/
theorem contUc_eq_brownianValue_of_eqOn {ΩB : Type} [MeasurableSpace ΩB] {PB : Measure ΩB}
    [IsProbabilityMeasure PB] {B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)}
    (hB : LatticeProb.IsBrownianSpace d 0 B PB) (hBc : ∀ β, Continuous fun s => B s β)
    {Ω : Type} {Z : Ω → ℝ → (Fin d → ℝ) → ℝ} {ω : Ω}
    (hZc : Continuous fun p : ℝ × (Fin d → ℝ) => Z ω p.1 p.2)
    (hZg : ∀ T, 0 < T → ∃ C k : ℝ, ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Fin d → ℝ)),
      |Z ω p.1 p.2| ≤ C * (1 + ‖p.2‖) ^ k)
    {G : ℝ → Sandpile.Continuum.Space d → ℝ}
    (hG : ∀ t, 0 ≤ t → ∀ y, G t y = Z ω t (WithLp.ofLp y)) {T : ℝ} (hT : 0 ≤ T)
    (x : Fin d → ℝ) :
    Parking.contUc (Parking.ofBrownianSpace B) PB Z ω T x =
      Sandpile.Continuum.brownianValue
        (fun s β => (WithLp.toLp 2 x : Sandpile.Continuum.Space d) + B s β) PB G T
        (WithLp.toLp 2 x) := by
  rw [valueBridge d ΩB PB B hB hBc Ω Z ω hZc hZg T x hT]
  unfold Sandpile.Continuum.brownianValue
  rw [hG T hT]
  congr 1
  exact Sandpile.Support.brownianDiscount_congr d _ PB _ _ T
    fun r hr0 _ z => (hG r hr0 z).symm

/-- **Regularity of the Brownian value field from joint continuity of the value.** Given joint
continuity of the Brownian value of a continuous reward of zero initial value and polynomial
growth, the value field of a continuous field that agrees almost surely with the Gaussian
potential at nonnegative times is, after the field is set to zero on a null event, zero at time
zero, jointly continuous, nondecreasing in time and coordinatewise measurable at every sample
point. -/
theorem ucRegularity_of_valueContinuity
    (hVC : ∀ (d : ℕ) (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
      (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)),
      LatticeProb.IsBrownianSpace d 0 B PB → (∀ β, Continuous fun s => B s β) →
      ∀ (Ω : Type) (Z : Ω → ℝ → (Fin d → ℝ) → ℝ) (ω : Ω),
        Continuous (fun p : ℝ × (Fin d → ℝ) => Z ω p.1 p.2) → (∀ x, Z ω 0 x = 0) →
        (∀ T, 0 < T → ∃ C k : ℝ, ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Fin d → ℝ)),
          |Z ω p.1 p.2| ≤ C * (1 + ‖p.2‖) ^ k) →
        ContinuousOn (fun p : ℝ × (Fin d → ℝ) =>
            Parking.contUc (Parking.ofBrownianSpace B) PB Z ω p.1 p.2)
          (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Fin d → ℝ)))) :
    ∀ (d : ℕ), 1 ≤ d → d ≤ 3 → ∀ v : ℝ, 0 < v →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (Q' : Measure Ω') [IsProbabilityMeasure Q']
        (WD : (Sandpile.Continuum.Space d → ℝ) → Ω' → ℝ) (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ),
        Sandpile.Continuum.IsWhiteNoise d WD Q' →
        (∀ t x, 0 ≤ t → (fun ω' => Z ω' t x) =ᵐ[Q']
          fun ω' => Sandpile.Continuum.gaussianPotential d v WD t (WithLp.toLp 2 x) ω') →
        (∀ ω', Continuous fun p : ℝ × (Fin d → ℝ) => Z ω' p.1 p.2) →
        (∀ ω' T, 0 < T → ∃ C k : ℝ, ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Fin d → ℝ)),
          |Z ω' p.1 p.2| ≤ C * (1 + ‖p.2‖) ^ k) →
        (∀ ω' x, Z ω' 0 x = 0) →
        (∀ r x, Measurable fun ω' => Z ω' r x) →
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)),
        LatticeProb.IsBrownianSpace d 0 B PB → (∀ β, Continuous fun s => B s β) →
        (∀ s, Measurable (B s)) →
      ∃ N : Set Ω', MeasurableSet N ∧ Q' N = 0 ∧
        ∀ (Z' : Ω' → ℝ → (Fin d → ℝ) → ℝ) (Uc : Ω' → ℝ → (Fin d → ℝ) → ℝ),
          (∀ ω' t x, Z' ω' t x = Set.indicator Nᶜ (fun ω'' => Z ω'' t x) ω') →
          (∀ ω' T x, Uc ω' T x =
            Parking.contUc (Parking.ofBrownianSpace B) PB Z' ω' (max T 0) x) →
          (∀ ω' x, Uc ω' 0 x = 0) ∧
          (∀ ω', Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω' p.1 p.2) ∧
          (∀ ω' x, Monotone fun s => Uc ω' s x) ∧
          (∀ s x, Measurable fun ω' => Uc ω' s x) ∧
          (∀ ω' T x, 0 ≤ T →
            Uc ω' T x = Parking.contUc (Parking.ofBrownianSpace B) PB Z' ω' T x) := by
  intro d hd1 hd3 v hv Ω' _ Q' _ WD Z hWD hZae hZc hZg hZ0 hZm ΩB _ PB _ B hB hBc hBm
  -- the field read at negative times through the Gaussian potential
  obtain ⟨Zs, hZs_nonneg, hZs_neg⟩ : ∃ Zs : ℝ → Sandpile.Continuum.Space d → Ω' → ℝ,
      (∀ t, 0 ≤ t → ∀ y ω, Zs t y ω = Z ω t (WithLp.ofLp y)) ∧
      (∀ t, t < 0 → ∀ y ω, Zs t y ω = Sandpile.Continuum.gaussianPotential d v WD t y ω) :=
    ⟨fun t y ω => if 0 ≤ t then Z ω t (WithLp.ofLp y)
        else Sandpile.Continuum.gaussianPotential d v WD t y ω,
      fun t ht y ω => by simp [ht], fun t ht y ω => by simp [not_le.2 ht]⟩
  -- the translated motions
  have hBr : ∀ y : Sandpile.Continuum.Space d,
      Sandpile.Continuum.IsBrownian d y (fun s β => y + B s β) PB :=
    fun y => isBrownian_add_of_isBrownianSpace hB y
  have hBcy : ∀ (y : Sandpile.Continuum.Space d) (β : ΩB),
      Continuous fun s : ℝ≥0 => y + B s β :=
    fun y β => continuous_const.add (hBc β)
  have hBmy : ∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), Measurable fun β => y + B t β :=
    fun y t => (hBm t).const_add y
  -- the sandpile field has the right law and is continuous on every strip
  have hZsae : ∀ (t : ℝ) (y : Sandpile.Continuum.Space d), Zs t y =ᵐ[Q']
      fun ω => Sandpile.Continuum.gaussianPotential d v WD t y ω := by
    intro t y
    by_cases ht : 0 ≤ t
    · have h := hZae t (WithLp.ofLp y) ht
      simp only [WithLp.toLp_ofLp] at h
      filter_upwards [h] with ω hω
      rw [hZs_nonneg t ht y ω]
      exact hω
    · exact Filter.Eventually.of_forall fun ω => hZs_neg t (not_le.1 ht) y ω
  have hZsc : ∀ (T : ℝ) (ω : Ω'), ContinuousOn
      (fun p : ℝ × Sandpile.Continuum.Space d => Zs p.1 p.2 ω)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))) := by
    intro T ω
    have hc : Continuous fun p : ℝ × Sandpile.Continuum.Space d =>
        Z ω p.1 (WithLp.ofLp p.2) :=
      (hZc ω).comp (continuous_fst.prodMk ((PiLp.continuous_ofLp 2 _).comp continuous_snd))
    exact hc.continuousOn.congr fun p hp => hZs_nonneg p.1 hp.1.1 p.2 ω
  have hbridge : ∀ (ω : Ω') (x : Fin d → ℝ) (T : ℝ), 0 ≤ T →
      Parking.contUc (Parking.ofBrownianSpace B) PB Z ω T x =
        Sandpile.Continuum.brownianValue
          (fun s β => (WithLp.toLp 2 x : Sandpile.Continuum.Space d) + B s β) PB
          (fun t y => Zs t y ω) T (WithLp.toLp 2 x) :=
    fun ω x T hT => contUc_eq_brownianValue_of_eqOn hB hBc (hZc ω) (hZg ω)
      (fun t ht y => hZs_nonneg t ht y ω) hT x
  -- monotonicity at each rational horizon
  have hmono : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂Q', ∀ x : Fin d → ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      Parking.contUc (Parking.ofBrownianSpace B) PB Z ω s x ≤
        Parking.contUc (Parking.ofBrownianSpace B) PB Z ω T x := by
    intro T hT
    filter_upwards [Sandpile.Frozen.brownian_value_mono_horizon d (by omega) Ω' Q' WD hWD v
      hv.le ΩB PB (fun y s β => y + B s β) hBr hBcy (fun y t => (hBmy y t).stronglyMeasurable)
      Zs hZsae (fun T' _ => Filter.Eventually.of_forall (hZsc T')) T hT] with ω hω x s hs
    rw [hbridge ω x s hs.1, hbridge ω x T hT.le]
    exact hω (WithLp.toLp 2 x) s hs
  -- almost everywhere measurability of the value at each point
  have hae : ∀ p : ℝ × (Fin d → ℝ), AEMeasurable
      (fun ω => Parking.contUc (Parking.ofBrownianSpace B) PB Z ω (max p.1 0) p.2) Q' := by
    intro p
    rcases le_or_gt p.1 0 with h | h
    · have hfun : (fun ω => Parking.contUc (Parking.ofBrownianSpace B) PB Z ω (max p.1 0) p.2) =
          fun _ => (0 : ℝ) := by
        funext ω
        rw [max_eq_right h]
        exact Parking.contUc_zero _ PB Z hZ0 ω p.2
      rw [hfun]
      exact aemeasurable_const
    · have hfun : (fun ω => Parking.contUc (Parking.ofBrownianSpace B) PB Z ω (max p.1 0) p.2) =
          fun ω => Sandpile.Continuum.brownianValue
            (fun s β => (WithLp.toLp 2 p.2 : Sandpile.Continuum.Space d) + B s β) PB
            (fun t y => Zs t y ω) p.1 (WithLp.toLp 2 p.2) := by
        funext ω
        rw [max_eq_left h.le]
        exact hbridge ω p.2 p.1 h.le
      rw [hfun]
      refine Sandpile.Support.aemeasurable_brownianValue_of_growth
        (fun s β => (WithLp.toLp 2 p.2 : Sandpile.Continuum.Space d) + B s β) PB
        (WithLp.toLp 2 p.2) (hBr _) (fun t => hBmy _ t) (fun β => hBcy _ β) Q' Zs p.1 h
        (fun q hq => ?_) (Filter.Eventually.of_forall fun ω => hZsc p.1 ω)
        (Filter.Eventually.of_forall fun ω => ?_)
      · have hq0 : Zs q.1 q.2 = fun ω => Z ω q.1 (WithLp.ofLp q.2) :=
          funext fun ω => hZs_nonneg q.1 hq.1.1 q.2 ω
        rw [hq0]
        exact (hZm q.1 (WithLp.ofLp q.2)).aemeasurable
      · obtain ⟨C, k, hk⟩ := hZg ω p.1 h
        obtain ⟨C', k', hk'⟩ := exists_euclidean_growth hk
        exact ⟨C', k', fun q hq => by rw [hZs_nonneg q.1 hq.1.1 q.2 ω]; exact hk' q hq⟩
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (ℝ × (Fin d → ℝ))
  obtain ⟨g, hgm, hgae⟩ : ∃ g : (ℝ × (Fin d → ℝ)) → Ω' → ℝ, (∀ p, Measurable (g p)) ∧
      ∀ p, (fun ω => Parking.contUc (Parking.ofBrownianSpace B) PB Z ω (max p.1 0) p.2) =ᵐ[Q']
        g p :=
    ⟨fun p => (hae p).mk _, fun p => (hae p).measurable_mk, fun p => (hae p).ae_eq_mk⟩
  -- the exceptional event
  have hP : ∀ᵐ ω ∂Q', (∀ q : ℚ, 0 < (q : ℝ) → ∀ x : Fin d → ℝ, ∀ s ∈ Set.Icc (0 : ℝ) (q : ℝ),
        Parking.contUc (Parking.ofBrownianSpace B) PB Z ω s x ≤
          Parking.contUc (Parking.ofBrownianSpace B) PB Z ω (q : ℝ) x) ∧
      ∀ p ∈ D, Parking.contUc (Parking.ofBrownianSpace B) PB Z ω (max p.1 0) p.2 = g p ω := by
    refine Filter.Eventually.and (ae_all_iff.2 fun q => ?_) ((ae_ball_iff hDc).2 fun p _ => hgae p)
    by_cases hq : 0 < (q : ℝ)
    · filter_upwards [hmono (q : ℝ) hq] with ω hω _ using hω
    · exact Filter.Eventually.of_forall fun ω hq' => absurd hq' hq
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hP)
  have hgood : ∀ ω ∉ N,
      (∀ q : ℚ, 0 < (q : ℝ) → ∀ x : Fin d → ℝ, ∀ s ∈ Set.Icc (0 : ℝ) (q : ℝ),
        Parking.contUc (Parking.ofBrownianSpace B) PB Z ω s x ≤
          Parking.contUc (Parking.ofBrownianSpace B) PB Z ω (q : ℝ) x) ∧
      ∀ p ∈ D, Parking.contUc (Parking.ofBrownianSpace B) PB Z ω (max p.1 0) p.2 = g p ω :=
    fun ω hω => by
      by_contra h
      exact hω (hNsub h)
  refine ⟨N, hNm, hN0, fun Z' Uc hZ' hUc => ?_⟩
  -- the modified field
  have hZ'N : ∀ ω' ∈ N, ∀ t x, Z' ω' t x = 0 := fun ω' h t x => by
    rw [hZ' ω' t x]
    exact Set.indicator_of_notMem (by simpa using h) _
  have hZ'out : ∀ ω' ∉ N, ∀ t x, Z' ω' t x = Z ω' t x := fun ω' h t x => by
    rw [hZ' ω' t x]
    exact Set.indicator_of_mem (Set.mem_compl h) _
  have hZ'prop : ∀ ω', (Continuous fun p : ℝ × (Fin d → ℝ) => Z' ω' p.1 p.2) ∧
      (∀ x, Z' ω' 0 x = 0) ∧
      ∀ T, 0 < T → ∃ C k : ℝ, ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Fin d → ℝ)),
        |Z' ω' p.1 p.2| ≤ C * (1 + ‖p.2‖) ^ k := by
    intro ω'
    by_cases h : ω' ∈ N
    · refine ⟨?_, fun x => hZ'N ω' h 0 x, fun T _ => ⟨0, 0, fun p _ => ?_⟩⟩
      · simp only [hZ'N ω' h]
        exact continuous_const
      · simp [hZ'N ω' h]
    · simp only [hZ'out ω' h]
      exact ⟨hZc ω', hZ0 ω', hZg ω'⟩
  have hVC' : ∀ ω', ContinuousOn (fun p : ℝ × (Fin d → ℝ) =>
      Parking.contUc (Parking.ofBrownianSpace B) PB Z' ω' p.1 p.2)
        (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set (Fin d → ℝ))) := fun ω' =>
    hVC d ΩB PB B hB hBc Ω' Z' ω' (hZ'prop ω').1 (hZ'prop ω').2.1 (hZ'prop ω').2.2
  have hUN : ∀ ω' ∈ N, ∀ (T : ℝ) (x : Fin d → ℝ), 0 ≤ T →
      Parking.contUc (Parking.ofBrownianSpace B) PB Z' ω' T x = 0 := by
    intro ω' h T x hT
    unfold Parking.contUc
    simp only [hZ'N ω' h, neg_zero, zero_add]
    exact spatialContValue_zero_reward _ PB hT
  have hcongr : ∀ ω' ∉ N, ∀ (T : ℝ) (x : Fin d → ℝ),
      Parking.contUc (Parking.ofBrownianSpace B) PB Z' ω' T x =
        Parking.contUc (Parking.ofBrownianSpace B) PB Z ω' T x := by
    intro ω' h T x
    unfold Parking.contUc
    simp only [hZ'out ω' h]
  have hUcN : ∀ ω' ∈ N, ∀ s x, Uc ω' s x = 0 := fun ω' h s x => by
    rw [hUc]
    exact hUN ω' h _ x (le_max_right _ _)
  have hUcout : ∀ ω' ∉ N, ∀ s x, Uc ω' s x =
      Parking.contUc (Parking.ofBrownianSpace B) PB Z ω' (max s 0) x := fun ω' h s x => by
    rw [hUc]
    exact hcongr ω' h _ x
  have hUccont : ∀ ω', Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω' p.1 p.2 := by
    intro ω'
    have hc : Continuous fun p : ℝ × (Fin d → ℝ) => (max p.1 0, p.2) := by fun_prop
    exact ((hVC' ω').comp_continuous hc fun p => Set.mk_mem_prod (Set.mem_Ici.2 (le_max_right _ _)) (Set.mem_univ _)).congr
      fun p => (hUc ω' p.1 p.2).symm
  refine ⟨?_, hUccont, ?_, ?_, ?_⟩
  · intro ω' x
    rw [hUc, max_self]
    exact Parking.contUc_zero _ PB Z' (fun ω'' x' => (hZ'prop ω'').2.1 x') ω' x
  · intro ω' x
    by_cases hω : ω' ∈ N
    · intro s t _
      dsimp only
      rw [hUcN ω' hω s x, hUcN ω' hω t x]
    · obtain ⟨hP1, -⟩ := hgood ω' hω
      have hcont : ContinuousOn
          (fun T : ℝ => Parking.contUc (Parking.ofBrownianSpace B) PB Z ω' T x) (Set.Ici 0) :=
        (hVC d ΩB PB B hB hBc Ω' Z ω' (hZc ω') (hZ0 ω') (hZg ω')).comp
          (by fun_prop : Continuous fun T : ℝ => (T, x)).continuousOn
          fun T hT => ⟨hT, Set.mem_univ _⟩
      have hVmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
          Parking.contUc (Parking.ofBrownianSpace B) PB Z ω' a x ≤
            Parking.contUc (Parking.ofBrownianSpace B) PB Z ω' b x := by
        intro a b ha hab
        have hb : 0 ≤ b := ha.trans hab
        have hseq : ∀ n : ℕ, ∃ q : ℚ, b < q ∧ (q : ℝ) < b + 1 / ((n : ℝ) + 1) := fun n =>
          exists_rat_btwn (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                              linarith)
        choose q hq1 hq2 using hseq
        have hlim : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 b) := by
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
            (?_ : Tendsto (fun n : ℕ => b + 1 / ((n : ℝ) + 1)) atTop (𝓝 b))
            (fun n => (hq1 n).le) (fun n => (hq2 n).le)
          simpa using (tendsto_const_nhds (x := b)).add tendsto_one_div_add_atTop_nhds_zero_nat
        have hVlim : Tendsto (fun n => Parking.contUc (Parking.ofBrownianSpace B) PB Z ω'
            (q n : ℝ) x) atTop
            (𝓝 (Parking.contUc (Parking.ofBrownianSpace B) PB Z ω' b x)) :=
          (hcont b hb).tendsto.comp (tendsto_nhdsWithin_iff.2
            ⟨hlim, Filter.Eventually.of_forall fun n => hb.trans (hq1 n).le⟩)
        exact ge_of_tendsto hVlim (Filter.Eventually.of_forall fun n =>
          hP1 (q n) (by linarith [hq1 n]) x a ⟨ha, by linarith [hq1 n]⟩)
      intro s t hst
      dsimp only
      rw [hUcout ω' hω s x, hUcout ω' hω t x]
      exact hVmono _ _ (le_max_right _ _) (max_le_max hst le_rfl)
  · intro s x
    have hm : ∀ p ∈ D, Measurable fun ω' => Uc ω' p.1 p.2 := by
      intro p hp
      have hfun : (fun ω' => Uc ω' p.1 p.2) = Set.indicator Nᶜ (g p) := by
        funext ω'
        by_cases h : ω' ∈ N
        · rw [hUcN ω' h, Set.indicator_of_notMem (by simpa using h)]
        · rw [hUcout ω' h, Set.indicator_of_mem (Set.mem_compl h)]
          exact (hgood ω' h).2 p hp
      rw [hfun]
      exact (hgm p).indicator hNm.compl
    obtain ⟨u, hu, hulim⟩ := mem_closure_iff_seq_limit.1 (hDd (s, x))
    exact measurable_of_tendsto_metrizable (fun n => hm (u n) (hu n))
      (tendsto_pi_nhds.2 fun ω' => ((hUccont ω').continuousAt.tendsto).comp hulim)
  · intro ω' T x hT
    rw [hUc, max_eq_left hT]

end Parking.Support
