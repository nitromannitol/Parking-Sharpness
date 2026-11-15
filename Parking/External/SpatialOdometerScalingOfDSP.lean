import Parking.External.SpatialOdometerScaling
import Parking.Support.SandpileContinuousGreen
import Parking.Support.UcRegularity
import Parking.Support.SandpileLawBridge
import Parking.Support.UpperTarget
import Sandpile.Support.MainExplWeak
import Sandpile.Support.Stationary
import Sandpile.External.ContStoppingStability

/-!
# The spatial odometer scaling limit from a space-time coupling

`Parking.External.spatialOdometerScaling_of_coupling` derives
`Parking.External.SpatialOdometerScaling` from the continuum stopping stability of the
divisible-sandpile development and a space-time coupling statement: for the real image of a
critical integer law, beyond a scale, the rescaled lattice odometer and finitely many rescaled
scenery pairings can be coupled with the Brownian stopping value of a version of the Gaussian
heat potential and the pairings of its white noise, uniformly on a compact set of positive times
and points, up to a prescribed accuracy outside an event of prescribed probability.

The limit objects are built from the sandpile white noise: the noise read through
`WithLp.ofLp` and scaled by the standard deviation, a continuous version of the Gaussian heat
potential set to zero on a null event, and the value field `Parking.contUc` of that version at
the horizon `max T 0`, for a continuous Brownian motion started at the origin.

* `Parking.Support.LatticeCoupling` records the coupling property in the lattice coordinates
  of a mass field.
* `Parking.Support.tendsto_integral_of_latticeCoupling`: couplings give convergence of the
  integrals of bounded continuous functions of finitely many scenery pairings and odometer
  values.
* `Parking.Support.lattice_oscillation_le_of_latticeCoupling`: couplings and continuity of the
  limit field give the space-time equicontinuity in probability of the lattice odometer.
* The parking law is carried to the centred sandpile mass law by `Parking.law_map_mass`; the
  rescaled parking odometer and scenery pairings are the lattice fields of the mass field.
-/

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped NNReal ENNReal

namespace Parking.Support

variable {d : ℕ}

/-- The rescaled odometer `R^{d/2-2} u_{⌊sR²⌋}(⌊Rx⌋)` of the scenery of a mass field `σ`, at a
space-time point `(s, x)`. -/
noncomputable def latticeOdometerField (d : ℕ) (R : ℝ) (σ : Sandpile.Site d → ℝ)
    (p : ℝ × (Fin d → ℝ)) : ℝ :=
  R ^ (-(2 - (d : ℝ) / 2)) *
    Sandpile.odometerOf (Sandpile.scenery d σ) ⌊p.1 * R ^ 2⌋₊ (fun i => ⌊R * p.2 i⌋)

/-- The rescaled pairing `R^{-d/2} ∑_y η(y) φ(y/R)` of the scenery `η` of a mass field `σ`. -/
noncomputable def latticeSceneryPair (d : ℕ) (R : ℝ) (σ : Sandpile.Site d → ℝ)
    (φ : (Fin d → ℝ) → ℝ) : ℝ :=
  R ^ (-(d : ℝ) / 2) *
    ∑' y : Sandpile.Site d, Sandpile.scenery d σ y * φ (fun j => (y j : ℝ) / R)

theorem measurable_scenery_field :
    Measurable (fun σ : Sandpile.Site d → ℝ => Sandpile.scenery d σ) :=
  measurable_pi_iff.mpr fun y =>
    ((measurable_pi_apply y).sub measurable_const).div_const _

theorem measurable_latticeOdometerField (R : ℝ) (p : ℝ × (Fin d → ℝ)) :
    Measurable fun σ : Sandpile.Site d → ℝ => latticeOdometerField d R σ p :=
  measurable_const.mul ((Sandpile.measurable_odometerOf _ _).comp measurable_scenery_field)

theorem measurable_latticeSceneryPair (R : ℝ) (φ : (Fin d → ℝ) → ℝ) :
    Measurable fun σ : Sandpile.Site d → ℝ => latticeSceneryPair d R σ φ :=
  measurable_const.mul (Measurable.tsum fun y =>
    ((measurable_pi_apply y).comp measurable_scenery_field).mul_const _)

/-- The scenery pairing of the mass field `1 + 2dη` of a parking sample is its scenery
pairing. -/
theorem latticeSceneryPair_mass (hd : 1 ≤ d) (w : Parking.Data d) (R : ℝ)
    (φ : (Fin d → ℝ) → ℝ) :
    latticeSceneryPair d R (fun y => 1 + 2 * (d : ℝ) * (w.1 y : ℝ)) φ =
      Parking.scenePair w R φ := by
  have hd0 : (2 * (d : ℝ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (by omega))
  have hs : ∀ y, Sandpile.scenery d (fun y => 1 + 2 * (d : ℝ) * (w.1 y : ℝ)) y =
      (w.1 y : ℝ) := by
    intro y
    simp only [Sandpile.scenery]
    field_simp
    ring
  simp only [latticeSceneryPair, hs, Parking.scenePair]

/-- The lattice odometer of the mass field `1 + 2dη` of a parking sample is its rescaled
divisible odometer. -/
theorem latticeOdometerField_mass (hd : 1 ≤ d) (w : Parking.Data d) (R : ℝ)
    (p : ℝ × (Fin d → ℝ)) :
    latticeOdometerField d R (fun y => 1 + 2 * (d : ℝ) * (w.1 y : ℝ)) p =
      Parking.barDivisible w R p.1 p.2 := by
  unfold latticeOdometerField Parking.barDivisible Parking.latticePoint
  rw [Parking.uOf_eq_sandpile_odometer d hd, Sandpile.odometer_eq_odometerOf,
    show (-(2 - (d : ℝ) / 2)) = (d : ℝ) / 2 - 2 by ring]

/-- Couplings of the lattice fields of mass fields of law `μ` with a limiting field `U` and a
noise `W` on a probability space with law `Q`: on every compact set of positive times and
points, jointly with finitely many test pairings, at every accuracy and probability, beyond a
scale. -/
def LatticeCoupling (d : ℕ) (μ : Measure (Sandpile.Site d → ℝ)) {Ω : Type*}
    [MeasurableSpace Ω] (Q : Measure Ω) (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ)
    (U : Ω → ℝ → (Fin d → ℝ) → ℝ) : Prop :=
  ∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K → (∀ p ∈ K, 0 < p.1) →
  ∀ (m : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ), (∀ i, Parking.IsTestFun (φ i)) →
  ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
    ∃ P : Measure ((Sandpile.Site d → ℝ) × Ω), IsProbabilityMeasure P ∧
      P.map Prod.fst = μ ∧ P.map Prod.snd = Q ∧
      P {p | (∃ q ∈ K, ε < |latticeOdometerField d R p.1 q - U p.2 q.1 q.2|) ∨
          ∃ i, ε < |latticeSceneryPair d R p.1 (φ i) - W (φ i) p.2|} ≤ ENNReal.ofReal δ

/-- A compact set of positive times lies in a strip `[T₀, T₁]` with `T₀ > 0`. -/
theorem exists_time_bounds {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K)
    (hpos : ∀ p ∈ K, 0 < p.1) :
    ∃ T₀ T₁ : ℝ, 0 < T₀ ∧ T₀ ≤ T₁ ∧ ∀ p ∈ K, T₀ ≤ p.1 ∧ p.1 ≤ T₁ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 1, one_pos, le_rfl, fun p hp => hp.elim⟩
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne continuous_fst.continuousOn
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hne continuous_fst.continuousOn
  exact ⟨a.1, b.1, hpos a ha, isMinOn_iff.1 hmin b hb,
    fun p hp => ⟨isMinOn_iff.1 hmin p hp, isMaxOn_iff.1 hmax p hp⟩⟩

/-- A real number below an iterated supremum over pairs of close points of a set is below one
of its terms. -/
theorem exists_lt_of_lt_iSup_dist {α : Type*} [PseudoMetricSpace α] {K : Set α} {δ ε : ℝ}
    (hε : 0 ≤ ε) {f : α → α → ℝ}
    (h : ε < ⨆ p ∈ K, ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ, f p q) :
    ∃ p ∈ K, ∃ q ∈ K, dist p q ≤ δ ∧ ε < f p q := by
  by_contra hne
  push Not at hne
  exact (not_le.mpr h) (Real.iSup_le (fun p => Real.iSup_le (fun hp => Real.iSup_le
    (fun q => Real.iSup_le (fun hq => Real.iSup_le (fun hpq => hne p hp q hq hpq) hε) hε)
    hε) hε) hε)

/-- **Oscillation of a continuous random field on a compact set.** For a random field with
continuous paths and measurable coordinates, there is a scale `δ` and a measurable event of
small probability containing every sample whose oscillation over pairs of points of the
compact set at distance at most `δ` exceeds `ε`. -/
theorem exists_oscillation_set {α Ω : Type*} [PseudoMetricSpace α] [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q] (f : Ω → α → ℝ) (hc : ∀ ω, Continuous (f ω))
    (hm : ∀ a, Measurable fun ω => f ω a) {K : Set α} (hK : IsCompact K) {ε ε' : ℝ}
    (hε : 0 < ε) (hε' : 0 < ε') :
    ∃ δ : ℝ, 0 < δ ∧ ∃ A : Set Ω, MeasurableSet A ∧ Q A ≤ ENNReal.ofReal ε' ∧
      ∀ ω, ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ δ → ε < |f ω p - f ω q| → ω ∈ A := by
  obtain ⟨D, hDK, hDc, hKD⟩ := hK.isSeparable.exists_countable_dense_subset
  let A : ℕ → Set Ω := fun n => ⋃ p ∈ D, ⋃ q ∈ D,
    ⋃ (_ : dist p q < 2 / ((n : ℝ) + 1)), {ω | ε < |f ω p - f ω q|}
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    MeasurableSet.biUnion hDc fun p _ => MeasurableSet.biUnion hDc fun q _ =>
      MeasurableSet.iUnion fun _ => measurableSet_lt measurable_const ((hm p).sub (hm q)).abs
  have hAanti : Antitone A := by
    intro n k hnk ω hω
    simp only [A, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hω ⊢
    obtain ⟨p, hp, q, hq, hpq, h⟩ := hω
    refine ⟨p, hp, q, hq, lt_of_lt_of_le hpq ?_, h⟩
    have hnk' : (n : ℝ) ≤ k := by exact_mod_cast hnk
    gcongr
  have hinter : (⋂ n, A n) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨η, hη, hU⟩ := Metric.uniformContinuousOn_iff.1
      (hK.uniformContinuousOn_of_continuous (hc ω).continuousOn) ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (2 / η)
    refine ⟨n, fun hω => ?_⟩
    simp only [A, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hω
    obtain ⟨p, hp, q, hq, hpq, h⟩ := hω
    have hlt : 2 / ((n : ℝ) + 1) < η := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hη] at hn
      nlinarith
    have := hU p (hDK hp) q (hDK hq) (hpq.trans hlt)
    rw [Real.dist_eq] at this
    linarith
  have htend := tendsto_measure_iInter_atTop (fun n => (hAm n).nullMeasurableSet) hAanti
    ⟨0, measure_ne_top Q _⟩
  rw [hinter, measure_empty] at htend
  obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε'))).exists
  refine ⟨1 / ((n : ℝ) + 1), by positivity, A n, hAm n, hn.le, ?_⟩
  intro ω p hp q hq hpq h
  have hg : 0 < |f ω p - f ω q| - ε := by linarith
  obtain ⟨η₁, hη₁, hp'⟩ := Metric.continuous_iff.1 (hc ω) p _ (half_pos hg)
  obtain ⟨η₂, hη₂, hq'⟩ := Metric.continuous_iff.1 (hc ω) q _ (half_pos hg)
  have hr : 0 < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  obtain ⟨p', hp'D, hpp'⟩ := Metric.mem_closure_iff.1 (hKD hp) _ (lt_min hη₁ hr)
  obtain ⟨q', hq'D, hqq'⟩ := Metric.mem_closure_iff.1 (hKD hq) _ (lt_min hη₂ hr)
  have h1 := hp' p' (by rw [dist_comm]; exact hpp'.trans_le (min_le_left _ _))
  have h2 := hq' q' (by rw [dist_comm]; exact hqq'.trans_le (min_le_left _ _))
  rw [Real.dist_eq] at h1 h2
  simp only [A, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  refine ⟨p', hp'D, q', hq'D, ?_, ?_⟩
  · have e1 := hpp'.trans_le (min_le_right _ _)
    have e2 := hqq'.trans_le (min_le_right _ _)
    have htri : dist p' q' ≤ dist p p' + dist p q + dist q q' := by
      have := dist_triangle4 p' p q q'
      rw [dist_comm p' p] at this
      linarith
    have hsum : 1 / (2 * ((n : ℝ) + 1)) + 1 / ((n : ℝ) + 1) + 1 / (2 * ((n : ℝ) + 1)) =
        2 / ((n : ℝ) + 1) := by
      field_simp
      ring
    linarith
  · have k1 := abs_sub_le (f ω p) (f ω p') (f ω q)
    have k2 := abs_sub_le (f ω p') (f ω q') (f ω q)
    rw [abs_sub_comm (f ω p) (f ω p')] at k1
    linarith

/-- The set of mass fields whose lattice odometer oscillates by more than `ε` over pairs of
points of a set at distance at most `δ` is measurable: the odometer at a space-time point
depends on the point only through a countable index. -/
theorem measurableSet_lattice_oscillation (R δ ε : ℝ) (K : Set (ℝ × (Fin d → ℝ))) :
    MeasurableSet {σ : Sandpile.Site d → ℝ | ∃ p ∈ K, ∃ q ∈ K, dist p q ≤ δ ∧
      ε < |latticeOdometerField d R σ p - latticeOdometerField d R σ q|} := by
  let key : ℝ × (Fin d → ℝ) → ℕ × Sandpile.Site d :=
    fun p => (⌊p.1 * R ^ 2⌋₊, fun i => ⌊R * p.2 i⌋)
  let g : ℕ × Sandpile.Site d → (Sandpile.Site d → ℝ) → ℝ := fun a σ =>
    R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometerOf (Sandpile.scenery d σ) a.1 a.2
  have hset : {σ : Sandpile.Site d → ℝ | ∃ p ∈ K, ∃ q ∈ K, dist p q ≤ δ ∧
      ε < |latticeOdometerField d R σ p - latticeOdometerField d R σ q|} =
      ⋃ a : ℕ × Sandpile.Site d, ⋃ b : ℕ × Sandpile.Site d,
        ⋃ (_ : ∃ p ∈ K, ∃ q ∈ K, dist p q ≤ δ ∧ key p = a ∧ key q = b),
          {σ | ε < |g a σ - g b σ|} := by
    ext σ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨p, hp, q, hq, hpq, h⟩
      exact ⟨key p, key q, ⟨p, hp, q, hq, hpq, rfl, rfl⟩, h⟩
    · rintro ⟨a, b, ⟨p, hp, q, hq, hpq, rfl, rfl⟩, h⟩
      exact ⟨p, hp, q, hq, hpq, h⟩
  rw [hset]
  have hgm : ∀ a, Measurable (g a) := fun a =>
    measurable_const.mul ((Sandpile.measurable_odometerOf _ _).comp measurable_scenery_field)
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b => MeasurableSet.iUnion
    fun _ => measurableSet_lt measurable_const ((hgm a).sub (hgm b)).abs

theorem measurable_latticeVector (R : ℝ) {m p' : ℕ} (φ : Fin m → (Fin d → ℝ) → ℝ)
    (sp : Fin p' → ℝ × (Fin d → ℝ)) :
    Measurable fun σ : Sandpile.Site d → ℝ =>
      ((fun i => latticeSceneryPair d R σ (φ i)), fun j => latticeOdometerField d R σ (sp j)) :=
  (measurable_pi_iff.mpr fun i => measurable_latticeSceneryPair R (φ i)).prodMk
    (measurable_pi_iff.mpr fun j => measurable_latticeOdometerField R (sp j))

/-- **Finite-dimensional convergence from couplings.** Couplings of the lattice fields with a
limiting field and noise give convergence of the integrals of every bounded continuous function
of finitely many scenery pairings and odometer values at positive times. -/
theorem tendsto_integral_of_latticeCoupling {μ : Measure (Sandpile.Site d → ℝ)}
    [IsProbabilityMeasure μ] {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {W : ((Fin d → ℝ) → ℝ) → Ω → ℝ} {U : Ω → ℝ → (Fin d → ℝ) → ℝ}
    (hc : LatticeCoupling d μ Q W U) (hWm : ∀ φ, Parking.IsTestFun φ → Measurable (W φ))
    (hUm : ∀ s x, Measurable fun ω => U ω s x)
    {m p' : ℕ} (φ : Fin m → (Fin d → ℝ) → ℝ) (sp : Fin p' → ℝ × (Fin d → ℝ))
    (hφ : ∀ i, Parking.IsTestFun (φ i)) (hsp : ∀ j, 0 < (sp j).1)
    (F : BoundedContinuousFunction ((Fin m → ℝ) × (Fin p' → ℝ)) ℝ) :
    Tendsto (fun R : ℝ => ∫ σ, F ((fun i => latticeSceneryPair d R σ (φ i)),
        fun j => latticeOdometerField d R σ (sp j)) ∂μ) atTop
      (𝓝 (∫ ω, F ((fun i => W (φ i) ω), fun j => U ω (sp j).1 (sp j).2) ∂Q)) := by
  let X : ℝ → (Sandpile.Site d → ℝ) → (Fin m → ℝ) × (Fin p' → ℝ) := fun R σ =>
    ((fun i => latticeSceneryPair d R σ (φ i)), fun j => latticeOdometerField d R σ (sp j))
  let Y : Ω → (Fin m → ℝ) × (Fin p' → ℝ) := fun ω =>
    ((fun i => W (φ i) ω), fun j => U ω (sp j).1 (sp j).2)
  have hX : ∀ R, Measurable (X R) := fun R => measurable_latticeVector R φ sp
  have hY : Measurable Y :=
    (measurable_pi_iff.mpr fun i => hWm _ (hφ i)).prodMk
      (measurable_pi_iff.mpr fun j => hUm _ _)
  have hdist : TendstoInDistribution X atTop Y (fun _ => μ) Q := by
    refine Sandpile.Continuum.tendstoInDistribution_of_coupling μ Q X Y
      (fun R => (hX R).aemeasurable) hY.aemeasurable fun ε δ hε hδ => ?_
    obtain ⟨R₀, hR₀⟩ := hc (Set.range sp) (Set.finite_range sp).isCompact
      (by rintro _ ⟨j, rfl⟩; exact hsp j) m φ hφ ε δ hε hδ
    refine ⟨R₀, fun R hR => ?_⟩
    obtain ⟨P, hP, hf, hs, hbad⟩ := hR₀ R hR
    refine ⟨P, hP, hf, hs, le_trans (measure_mono fun p hp => ?_) hbad⟩
    simp only [Set.mem_ofPred_eq] at hp ⊢
    by_contra hno
    push Not at hno
    obtain ⟨h1, h2⟩ := hno
    refine (not_le.mpr hp) ?_
    rw [Prod.dist_eq]
    refine max_le ((dist_pi_le_iff hε.le).2 fun i => ?_) ((dist_pi_le_iff hε.le).2 fun j => ?_)
    · rw [Real.dist_eq]
      exact h2 i
    · rw [Real.dist_eq]
      exact h1 (sp j) ⟨j, rfl⟩
  exact (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    (fun R => (hX R).aemeasurable) hY.aemeasurable).1 hdist F

/-- **Equicontinuity in probability from couplings.** Couplings of the lattice fields with a
limiting field with continuous paths give, on a compact set of positive times and points, a
scale below which the lattice odometer oscillates by more than `ε` with probability at most
`ε'`, beyond a scale. -/
theorem lattice_oscillation_le_of_latticeCoupling {μ : Measure (Sandpile.Site d → ℝ)}
    [IsProbabilityMeasure μ] {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {W : ((Fin d → ℝ) → ℝ) → Ω → ℝ} {U : Ω → ℝ → (Fin d → ℝ) → ℝ}
    (hc : LatticeCoupling d μ Q W U)
    (hUc : ∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => U ω p.1 p.2)
    (hUm : ∀ s x, Measurable fun ω => U ω s x)
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K) (hpos : ∀ p ∈ K, 0 < p.1)
    {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε') :
    ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      μ {σ | ∃ p ∈ K, ∃ q ∈ K, dist p q ≤ δ ∧
        ε < |latticeOdometerField d R σ p - latticeOdometerField d R σ q|}
        ≤ ENNReal.ofReal ε' := by
  obtain ⟨δ, hδ, A, hAm, hA, hAmem⟩ := exists_oscillation_set Q
    (fun ω (p : ℝ × (Fin d → ℝ)) => U ω p.1 p.2) hUc (fun p => hUm p.1 p.2) hK
    (ε := ε / 3) (ε' := ε' / 2) (by positivity) (by positivity)
  obtain ⟨R₀, hR₀⟩ := hc K hK hpos 0 Fin.elim0 (fun i => i.elim0) (ε / 3) (ε' / 2)
    (by positivity) (by positivity)
  refine ⟨δ, hδ, R₀, fun R hR => ?_⟩
  obtain ⟨P, -, hf, hs, hbad⟩ := hR₀ R hR
  have hbad' : P {p : (Sandpile.Site d → ℝ) × Ω |
      ∃ q ∈ K, ε / 3 < |latticeOdometerField d R p.1 q - U p.2 q.1 q.2|}
      ≤ ENNReal.ofReal (ε' / 2) :=
    (measure_mono fun p hp => Or.inl hp).trans hbad
  rw [← hf, Measure.map_apply measurable_fst (measurableSet_lattice_oscillation R δ ε K)]
  calc P (Prod.fst ⁻¹' {σ | ∃ p ∈ K, ∃ q ∈ K, dist p q ≤ δ ∧
        ε < |latticeOdometerField d R σ p - latticeOdometerField d R σ q|})
      ≤ P ({p : (Sandpile.Site d → ℝ) × Ω |
          ∃ q ∈ K, ε / 3 < |latticeOdometerField d R p.1 q - U p.2 q.1 q.2|} ∪
          Prod.snd ⁻¹' A) := by
        refine measure_mono fun p hp => ?_
        obtain ⟨p₀, hp₀, q₀, hq₀, hpq, h⟩ := hp
        by_cases h1 : ε / 3 < |latticeOdometerField d R p.1 p₀ - U p.2 p₀.1 p₀.2|
        · exact Or.inl ⟨p₀, hp₀, h1⟩
        by_cases h2 : ε / 3 < |latticeOdometerField d R p.1 q₀ - U p.2 q₀.1 q₀.2|
        · exact Or.inl ⟨q₀, hq₀, h2⟩
        refine Or.inr (hAmem p.2 p₀ hp₀ q₀ hq₀ hpq ?_)
        push Not at h1 h2
        have k1 := abs_sub_le (latticeOdometerField d R p.1 p₀) (U p.2 p₀.1 p₀.2)
          (latticeOdometerField d R p.1 q₀)
        have k2 := abs_sub_le (U p.2 p₀.1 p₀.2) (U p.2 q₀.1 q₀.2)
          (latticeOdometerField d R p.1 q₀)
        rw [abs_sub_comm (U p.2 q₀.1 q₀.2)] at k2
        show ε / 3 < |U p.2 p₀.1 p₀.2 - U p.2 q₀.1 q₀.2|
        linarith
    _ ≤ P {p : (Sandpile.Site d → ℝ) × Ω |
          ∃ q ∈ K, ε / 3 < |latticeOdometerField d R p.1 q - U p.2 q.1 q.2|} +
          P (Prod.snd ⁻¹' A) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε' / 2) + ENNReal.ofReal (ε' / 2) := by
        refine add_le_add hbad' ?_
        rw [← Measure.map_apply measurable_snd hAm, hs]
        exact hA
    _ = ENNReal.ofReal ε' := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

end Parking.Support

open Parking.Support in
/-- **The spatial odometer scaling limit from a space-time coupling.** The continuum stopping
stability and the space-time coupling of the lattice odometer and scenery pairings with the
Brownian stopping value and the white noise, for the real image of a critical integer law,
give `Parking.External.SpatialOdometerScaling`. -/
theorem Parking.External.spatialOdometerScaling_of_coupling
    (hST :
      Sandpile.External.ContinuumStoppingStability.{0} →
      ∀ (d : ℕ), 1 ≤ d → d ≤ 3 →
      ∀ (νZ : Measure ℤ) [IsProbabilityMeasure (Parking.law d νZ)], Parking.CriticalLaw νZ →
      ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], ν = νZ.map (fun k : ℤ => (k : ℝ)) → ∫ z, z ∂ν = 0 →
        0 < evariance id ν → evariance id ν < ⊤ →
        ∀ θ₀ : ℝ, 0 < θ₀ → Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
      ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
        (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W PW →
      ∀ Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ,
        (∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
          Z t x =ᵐ[PW] fun ω => Sandpile.Continuum.gaussianPotential d (variance id ν) W t x ω) →
        (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
          ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => Z p.1 p.2 ω)
            (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)))) →
        (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW, ∃ C k : ℝ,
          ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
            |Z p.1 p.2 ω| ≤ C * (1 + ‖p.2‖) ^ k) →
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d),
        (∀ y, Sandpile.Continuum.IsBrownian d y (B y) PB) →
        (∀ y ω, Continuous fun s => B y s ω) → (∀ y t, StronglyMeasurable (B y t)) →
      ∀ (K : Set (Sandpile.Continuum.Space d)), IsCompact K →
      ∀ T₀ T₁ : ℝ, 0 < T₀ → T₀ ≤ T₁ →
      ∀ (m : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ), (∀ i, Parking.IsTestFun (φ i)) →
      ∀ ε δ : ℝ, 0 < ε → 0 < δ →
        ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
          ∃ P : Measure ((Sandpile.Site d → ℝ) × ΩW), IsProbabilityMeasure P ∧
            P.map Prod.fst = Sandpile.centeredMassLaw d ν ∧ P.map Prod.snd = PW ∧
            P {p | (∃ T ∈ Set.Icc T₀ T₁, ∃ u ∈ K,
                  ε < |R ^ (-(2 - (d : ℝ) / 2)) *
                        Sandpile.odometerOf (Sandpile.scenery d p.1) ⌊T * R ^ 2⌋₊
                          (fun i => ⌊R * u i⌋)
                      - Sandpile.Continuum.brownianValue (B u) PB (fun t y => Z t y p.2) T u|) ∨
                ∃ i, ε < |R ^ (-(d : ℝ) / 2) *
                      ∑' y : Sandpile.Site d, Sandpile.scenery d p.1 y * φ i (fun j => (y j : ℝ) / R)
                    - Real.sqrt (variance id ν) * W (fun z => φ i (WithLp.ofLp z)) p.2|}
              ≤ ENNReal.ofReal δ
    )
    (hStab : Sandpile.External.ContinuumStoppingStability.{0}) :
    Parking.External.SpatialOdometerScaling := by
  intro d hd hd3 νZ hν
  have hνp : IsProbabilityMeasure νZ := hν.prob
  have hlaw : IsProbabilityMeasure (Parking.law d νZ) := Parking.law_isProb hd νZ
  obtain ⟨hνprob, hmean, hevpos, hevtop, ⟨θ₀, hθ₀, hexp⟩, hvar⟩ :=
    Parking.criticalLaw_moments νZ hν
  set ν : Measure ℝ := νZ.map (fun k : ℤ => (k : ℝ))
  have hv : 0 < variance id ν := ENNReal.toReal_pos hevpos.ne' hevtop.ne
  obtain ⟨Ω, mΩ, Q, hQ, WD, -, Z, hWD, -, hZmod, hZc, hZg, -, -, -, hZ0, hZm, -, -⟩ :=
    Parking.exists_continuous_green_field d hd hd3 (variance id ν) hv
  obtain ⟨ΩB, mB, PB, B₀, hB₀, hB₀m, hB₀c⟩ := LatticeProb.exists_isBrownianSpace_cont d 0
  have hPB : IsProbabilityMeasure PB := hB₀.isProbabilityMeasure
  obtain ⟨N, -, hN0, hreg⟩ := Parking.Support.ucRegularity d hd hd3 (variance id ν) hv Ω Q
    WD Z hWD hZmod hZc hZg hZ0 hZm ΩB PB B₀ hB₀ hB₀c (fun s => (hB₀m s).measurable)
  let Z' : Ω → ℝ → (Fin d → ℝ) → ℝ := fun ω t x => Set.indicator Nᶜ (fun ω'' => Z ω'' t x) ω
  let Uc : Ω → ℝ → (Fin d → ℝ) → ℝ := fun ω T x =>
    Parking.contUc (Parking.ofBrownianSpace B₀) PB Z' ω (max T 0) x
  obtain ⟨hUc0, hUcc, hUcmono, hUcm, hUceq⟩ := hreg Z' Uc (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  have hZ'eq : ∀ ω, ω ∉ N → ∀ t x, Z' ω t x = Z ω t x := fun ω hω _ _ =>
    Set.indicator_of_mem (Set.mem_compl hω) _
  have hZ'zero : ∀ ω, ω ∈ N → ∀ t x, Z' ω t x = 0 := fun ω hω _ _ =>
    Set.indicator_of_notMem (fun h => (Set.mem_compl_iff N ω).1 h hω) _
  have hZ'c : ∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Z' ω p.1 p.2 := by
    intro ω
    by_cases hω : ω ∈ N
    · simp only [hZ'zero ω hω]
      exact continuous_const
    · simp only [hZ'eq ω hω]
      exact hZc ω
  have hZ'g : ∀ ω T, 0 < T → ∃ C k : ℝ,
      ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Fin d → ℝ)),
        |Z' ω p.1 p.2| ≤ C * (1 + ‖p.2‖) ^ k := by
    intro ω T hT
    by_cases hω : ω ∈ N
    · refine ⟨0, 0, fun p _ => ?_⟩
      simp only [hZ'zero ω hω, abs_zero, zero_mul, le_refl]
    · obtain ⟨C, k, h⟩ := hZg ω T hT
      exact ⟨C, k, fun p hp => by simpa only [hZ'eq ω hω] using h p hp⟩
  have hNae : ∀ᵐ ω ∂Q, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  have hZ'mod : ∀ t x, 0 ≤ t → (fun ω => Z' ω t x) =ᵐ[Q]
      fun ω => Sandpile.Continuum.gaussianPotential d (variance id ν) WD t
        (WithLp.toLp 2 x) ω := by
    intro t x ht
    filter_upwards [hZmod t x ht, hNae] with ω h1 h2
    rw [hZ'eq ω h2]
    exact h1
  obtain ⟨hWN, hWm, hGP⟩ := Parking.parking_noise_of_sandpile hd hd3 hWD (variance id ν) hv.le
  let W' : ((Fin d → ℝ) → ℝ) → Ω → ℝ := fun φ ω =>
    Real.sqrt (variance id ν) * WD (fun y => φ (WithLp.ofLp y)) ω
  let Zs : ℝ → Sandpile.Continuum.Space d → Ω → ℝ := fun t x ω =>
    if 0 ≤ t then Z' ω t (WithLp.ofLp x)
    else Sandpile.Continuum.gaussianPotential d (variance id ν) WD t x ω
  let B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d :=
    fun y s β => y + B₀ s β
  have hval : ∀ ω (q : ℝ × (Fin d → ℝ)), 0 ≤ q.1 →
      Sandpile.Continuum.brownianValue (B (WithLp.toLp 2 q.2)) PB (fun t y => Zs t y ω) q.1
        (WithLp.toLp 2 q.2) = Uc ω q.1 q.2 := by
    intro ω q hq
    rw [hUceq ω q.1 q.2 hq]
    exact (Parking.Support.contUc_eq_brownianValue_of_eqOn hB₀ hB₀c (hZ'c ω) (hZ'g ω)
      (G := fun t y => Zs t y ω) (fun t ht y => ite_eq_left ht) hq q.2).symm
  have hZsver : ∀ (t : ℝ) (x : Sandpile.Continuum.Space d), Zs t x =ᵐ[Q]
      fun ω => Sandpile.Continuum.gaussianPotential d (variance id ν) WD t x ω := by
    intro t x
    by_cases ht : 0 ≤ t
    · have h := hZ'mod t (WithLp.ofLp x) ht
      simp only [WithLp.toLp_ofLp] at h
      filter_upwards [h] with ω hω
      simp only [Zs, ite_eq_left ht]
      exact hω
    · exact Filter.Eventually.of_forall fun ω => by simp only [Zs, ite_eq_right ht]
  have hZscont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂Q,
      ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => Zs p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))) := by
    intro T _
    refine Filter.Eventually.of_forall fun ω => ?_
    have hc : Continuous fun p : ℝ × Sandpile.Continuum.Space d =>
        Z' ω p.1 (WithLp.ofLp p.2) :=
      (hZ'c ω).comp (continuous_fst.prodMk ((PiLp.continuous_ofLp 2 _).comp continuous_snd))
    refine hc.continuousOn.congr fun p hp => ?_
    simp only [Zs, ite_eq_left hp.1.1]
  have hZsgrowth : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂Q, ∃ C k : ℝ,
      ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
        |Zs p.1 p.2 ω| ≤ C * (1 + ‖p.2‖) ^ k := by
    intro T hT
    refine Filter.Eventually.of_forall fun ω => ?_
    obtain ⟨C, k, hCk⟩ := hZ'g ω T hT
    obtain ⟨C', k', h'⟩ := Parking.Support.exists_euclidean_growth (Z := Z' ω) hCk
    refine ⟨C', k', fun p hp => ?_⟩
    simp only [Zs, ite_eq_left hp.1.1]
    exact h' p hp
  have hc : LatticeCoupling d (Sandpile.centeredMassLaw d ν) Q W' Uc := by
    intro K hK hpos m φ hφ ε δ hε hδ
    obtain ⟨T₀, T₁, hT₀, hT₀₁, hT⟩ := exists_time_bounds hK hpos
    obtain ⟨R₀, -, hR₀⟩ := hST hStab d hd hd3 νZ hν ν rfl hmean hevpos hevtop θ₀ hθ₀ hexp Ω Q
      WD hWD Zs hZsver hZscont hZsgrowth ΩB PB B
      (fun y => Parking.Support.isBrownian_add_of_isBrownianSpace hB₀ y)
      (fun y β => continuous_const.add (hB₀c β)) (fun y t => (hB₀m t).const_add y)
      ((fun p : ℝ × (Fin d → ℝ) => (WithLp.toLp 2 p.2 : Sandpile.Continuum.Space d)) '' K)
      (hK.image ((PiLp.continuous_toLp 2 _).comp continuous_snd))
      T₀ T₁ hT₀ hT₀₁ m φ hφ ε δ hε hδ
    refine ⟨R₀, fun R hR => ?_⟩
    obtain ⟨P, hP, hf, hs, hbad⟩ := hR₀ R hR
    refine ⟨P, hP, hf, hs, le_trans (measure_mono ?_) hbad⟩
    rintro p (⟨q, hq, h⟩ | ⟨i, h⟩)
    · left
      refine ⟨q.1, ⟨(hT q hq).1, (hT q hq).2⟩, WithLp.toLp 2 q.2, ⟨q, hq, rfl⟩, ?_⟩
      rw [hval p.2 q (hT₀.le.trans (hT q hq).1)]
      exact h
    · exact Or.inr ⟨i, h⟩
  have hμ : (Parking.law d νZ).map
      (fun w : Parking.Data d => fun y => 1 + 2 * (d : ℝ) * (w.1 y : ℝ)) =
      Sandpile.centeredMassLaw d ν := Parking.law_map_mass d hd νZ
  have hTm : Measurable
      (fun w : Parking.Data d => fun y : Sandpile.Site d => 1 + 2 * (d : ℝ) * (w.1 y : ℝ)) :=
    Measurable.of_eval fun y => measurable_const.add
      (measurable_const.mul ((measurable_pi_apply y).comp Parking.measurable_confReal))
  rw [← hvar]
  refine ⟨Ω, mΩ, Q, hQ, W', Z', Uc, hWN, hWm, hGP Z' hZ'mod, hZ'c, hUc0, hUcc, hUcmono, hUcm,
    ⟨ΩB, mB, PB, B₀, hB₀, fun ω T x hT => hUceq ω T x hT⟩, ?_, ?_⟩
  · intro m p' φ sp hφ hsp F
    refine (tendsto_integral_of_latticeCoupling hc hWm hUcm φ sp hφ hsp F).congr fun R => ?_
    have hFm : Measurable fun σ : Sandpile.Site d → ℝ =>
        F ((fun i => latticeSceneryPair d R σ (φ i)), fun j => latticeOdometerField d R σ (sp j)) :=
      F.continuous.measurable.comp (measurable_latticeVector R φ sp)
    rw [← hμ, integral_map hTm.aemeasurable hFm.aestronglyMeasurable]
    simp only [latticeSceneryPair_mass hd, latticeOdometerField_mass hd]
  · intro K hK hpos ε hε ε' hε'
    obtain ⟨δ, hδ, R₀, hR₀⟩ := lattice_oscillation_le_of_latticeCoupling hc hUcc hUcm hK hpos
      hε hε'
    refine ⟨δ, hδ, R₀, fun R hR => ENNReal.toReal_le_of_le_ofReal hε'.le ?_⟩
    refine le_trans ?_ (hR₀ R hR)
    rw [← hμ]
    refine le_trans (measure_mono fun w hw => ?_) (Measure.le_map_apply hTm.aemeasurable _)
    rw [Set.mem_ofPred_eq] at hw
    obtain ⟨p, hp, q, hq, hpq, h⟩ := exists_lt_of_lt_iSup_dist hε.le hw
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, latticeOdometerField_mass hd]
    exact ⟨p, hp, q, hq, hpq, h⟩
