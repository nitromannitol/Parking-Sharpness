import Parking.Support.SpaceTimeCoupling
import Parking.Support.SceneryCovarianceLimit
import Parking.Support.LinearFieldFdd

/-!
# Space-time coupling with retained scenery for integer critical laws

For an integer critical law `νZ`, the rescaled odometer, the Brownian value and the scenery
pairings with finitely many test functions are coupled simultaneously with the Gaussian
potential version and the white noise. The finite-dimensional convergence of the joint vector
of interpolated sandpile field values and scenery pairings is the joint limit of
`jointLinearFdd_of_sceneryCovarianceLimit`, transported from `Parking.law d νZ` to the
sandpile mass law by `law_map_massField`, `scenery_massField` and `linHatInterpBridge`. The
coupling of the joint vector on the compact index space `K ⊕ Finset.range m` is
`Sandpile.Continuum.exists_field_coupling_on_compact`, and
`dlt4_scaling_of_coupling_uniform` assembles it with the stopping-value comparison.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Parking.Support

open Parking

attribute [local instance] Metric.metricSpaceSum

/-- Convergence in distribution on a pushed-forward law, from the convergence of the composites
with the push-forward map under the original law. -/
theorem tendstoInDistribution_of_comp_map_eq {ι Ω₀ Ω Ω' E : Type*} [MeasurableSpace Ω₀]
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] {l : Filter ι} {X : ι → Ω → E} {Z : Ω' → E}
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {T : Ω₀ → Ω} (hT : Measurable T)
    (hmap : μ₀.map T = μ) (hX : ∀ i, AEMeasurable (X i) μ)
    (h : TendstoInDistribution (fun i ω => X i (T ω)) l Z (fun _ => μ₀) μ') :
    TendstoInDistribution X l Z (fun _ => μ) μ' := by
  subst hmap
  refine ⟨hX, h.aemeasurable_limit, ?_⟩
  refine h.tendsto.congr fun i => ?_
  apply ProbabilityMeasure.toMeasure_injective
  exact (AEMeasurable.map_map_of_aemeasurable (hX i) hT.aemeasurable).symm

/-- Two natural numbers at real distance less than one are equal. -/
theorem eq_of_abs_natCast_sub_lt_one {a b : ℕ} (h : |(a : ℝ) - (b : ℝ)| < 1) : a = b := by
  rw [abs_sub_lt_iff] at h
  have h1 : a < b + 1 := by exact_mod_cast (by linarith [h.1] : (a : ℝ) < b + 1)
  have h2 : b < a + 1 := by exact_mod_cast (by linarith [h.2] : (b : ℝ) < a + 1)
  omega

/-- **Coupling of the interpolated sandpile field and finitely many scenery pairings with the
Gaussian potential version and the white noise.**  The rescaled mass field of the one-site law
`ν = νZ.map (↑)` and the Gaussian potential version `Z` are close on a compact subset `K` of the
strip, and simultaneously the scenery pairings with the test functions `φ i` are close to the
corresponding white-noise values, except on an event of small probability. -/
theorem exists_scenery_field_coupling
    {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (νZ : Measure ℤ) [IsProbabilityMeasure (Parking.law d νZ)] (hν : Parking.CriticalLaw νZ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hνZ : ν = νZ.map (fun k : ℤ => (k : ℝ)))
    (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
      Z t x =ᵐ[PW] fun ω =>
        Sandpile.Continuum.gaussianPotential d (variance id ν) W t x ω)
    (T : ℝ) (hT : 0 < T)
    (hZcont : ∀ᵐ ω ∂PW, ContinuousOn (fun q : ℝ × Sandpile.Continuum.Space d =>
        Z q.1 q.2 ω)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (hmeasLin : ∀ (R t : ℝ) (y : Sandpile.Continuum.Space d), t ∈ Set.Icc (0 : ℝ) T →
      AEMeasurable (fun σ : Sandpile.Site d → ℝ =>
        Sandpile.Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) t y)
        (Sandpile.centeredMassLaw d ν))
    (hosc : ∀ K : Set (ℝ × Sandpile.Continuum.Space d), IsCompact K →
      K ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)) →
      ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 1 ≤ R →
        (Sandpile.centeredMassLaw d ν)
          {σ | ∃ p ∈ K, ∃ q ∈ K, dist p q < δ ∧
            η < |Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
                (Sandpile.scenery d σ) p.1 p.2 -
              Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
                (Sandpile.scenery d σ) q.1 q.2|} ≤ ENNReal.ofReal ε)
    (K : Set (ℝ × Sandpile.Continuum.Space d)) (hK : IsCompact K)
    (hKT : K ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)))
    (m : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (hφ : ∀ i, Parking.IsTestFun (φ i))
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∃ P : Measure ((Sandpile.Site d → ℝ) × ΩW), IsProbabilityMeasure P ∧
        P.map Prod.fst = Sandpile.centeredMassLaw d ν ∧
        P.map Prod.snd = PW ∧
        P {p | (∃ q ∈ K,
              ε < |Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
                    (Sandpile.scenery d p.1) q.1 q.2 - Z q.1 q.2 p.2|) ∨
            ∃ i, ε < |R ^ (-(d : ℝ) / 2) *
                  ∑' y : Sandpile.Site d, Sandpile.scenery d p.1 y *
                    φ i (fun j => (y j : ℝ) / R)
                - Real.sqrt (variance id ν) * W (fun z => φ i (WithLp.ofLp z)) p.2|}
          ≤ ENNReal.ofReal δ := by
  classical
  subst hνZ
  have := hν.prob
  have hvid : variance id (νZ.map (fun k : ℤ => (k : ℝ))) =
      variance (fun k : ℤ => (k : ℝ)) νZ :=
    variance_id_map measurable_intCastReal.aemeasurable
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : CompactSpace (K ⊕ Finset.range m) := inferInstance
  set f : ℝ → (Sandpile.Site d → ℝ) → K ⊕ Finset.range m → ℝ := fun R σ => Sum.elim
    (fun q : K => Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
      (Sandpile.scenery d σ) q.1.1 q.1.2)
    (fun k : Finset.range m => R ^ (-(d : ℝ) / 2) * ∑' y : Sandpile.Site d,
      Sandpile.scenery d σ y * φ ⟨k.1, Finset.mem_range.1 k.2⟩ (fun j => (y j : ℝ) / R))
    with hfdef
  set g : ΩW → K ⊕ Finset.range m → ℝ := fun ω => Sum.elim
    (fun q : K => Z q.1.1 q.1.2 ω)
    (fun k : Finset.range m => Real.sqrt (variance id (νZ.map (fun k : ℤ => (k : ℝ)))) *
      W (fun z => φ ⟨k.1, Finset.mem_range.1 k.2⟩ (WithLp.ofLp z)) ω) with hgdef
  have hpair : ∀ (R : ℝ) (i : Fin m), Measurable (fun σ : Sandpile.Site d → ℝ =>
      R ^ (-(d : ℝ) / 2) * ∑' y : Sandpile.Site d,
        Sandpile.scenery d σ y * φ i (fun j => (y j : ℝ) / R)) := by
    intro R i
    refine Measurable.const_mul (Measurable.tsum fun y => ?_) _
    exact (((measurable_pi_apply y).sub_const 1).div_const _).mul_const _
  have hgaussmeas : ∀ (t : ℝ) (x : Sandpile.Continuum.Space d), 0 ≤ t →
      Measurable (fun ω => Sandpile.Continuum.gaussianPotential d
        (variance id (νZ.map (fun k : ℤ => (k : ℝ)))) W t x ω) := by
    intro t x ht
    exact measurable_const.mul (hW.meas _ (Sandpile.Support.memLp_greenTimeBM hd hd3 ht x))
  have hfd : ∀ (m' : ℕ) (x : Fin m' → K ⊕ Finset.range m), TendstoInDistribution
      (fun R σ k => f R σ (x k)) atTop (fun ω k => g ω (x k))
      (fun _ => Sandpile.centeredMassLaw d (νZ.map (fun k : ℤ => (k : ℝ)))) PW := by
    intro m' x
    set sp : Fin m' → ℝ × (Fin d → ℝ) := fun j =>
      Sum.elim (fun q : K => (q.1.1, WithLp.ofLp q.1.2))
        (fun _ => ((0 : ℝ), (0 : Fin d → ℝ))) (x j) with hspdef
    have hspT : ∀ j, (sp j).1 ∈ Set.Icc (0 : ℝ) T := by
      intro j
      rcases hxj : x j with q | i
      · simpa only [hspdef, hxj, Sum.elim_inl] using (hKT q.property).1
      · simp only [hspdef, hxj, Sum.elim_inr]
        exact ⟨le_refl _, hT.le⟩
    have hjoint := jointLinearFdd_of_sceneryCovarianceLimit Parking.sceneryCovarianceLimit d hd
      hd3 νZ hν ΩW PW W hW m m' φ sp hφ (fun j => (hspT j).1)
    set X : ℝ → (Sandpile.Site d → ℝ) → (Fin m → ℝ) × (Fin m' → ℝ) := fun R σ =>
      ((fun i => R ^ (-(d : ℝ) / 2) * ∑' y : Sandpile.Site d,
          Sandpile.scenery d σ y * φ i (fun j => (y j : ℝ) / R)),
        (fun j => Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
          (Sandpile.scenery d σ) (sp j).1 (WithLp.toLp 2 (sp j).2))) with hXdef
    have hXm : ∀ R, AEMeasurable (X R)
        (Sandpile.centeredMassLaw d (νZ.map (fun k : ℤ => (k : ℝ)))) := fun R =>
      AEMeasurable.prodMk (aemeasurable_pi_iff.mpr fun i => (hpair R i).aemeasurable)
        (aemeasurable_pi_iff.mpr fun j => hmeasLin R _ _ (hspT j))
    have hmap := law_map_massField hd νZ
    have hXT : ∀ᶠ R : ℝ in atTop,
        (fun w : Data d => X R (fun y => 1 + 2 * (d : ℝ) * (w.1 y : ℝ))) =
          fun w => ((fun i => scenePair w R (φ i)),
            (fun j => linHatInterp (fun y => (w.1 y : ℝ)) R (sp j))) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      funext w
      have hs : Sandpile.scenery d (fun y => 1 + 2 * (d : ℝ) * (w.1 y : ℝ)) =
          fun y => (w.1 y : ℝ) := scenery_massField hd (fun y => (w.1 y : ℝ))
      refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
      · simp only [hXdef, hs, scenePair]
      · simp only [hXdef, hs]
        exact (linHatInterpBridge d _ R hR (sp j) (hspT j).1).symm
    have hjS : TendstoInDistribution
        (fun R (w : Data d) => X R (fun y => 1 + 2 * (d : ℝ) * (w.1 y : ℝ))) atTop
        (fun ω => ((fun i => Real.sqrt (variance (fun k : ℤ => (k : ℝ)) νZ) *
            W (fun y => φ i (WithLp.ofLp y)) ω),
          (fun j => Sandpile.Continuum.gaussianPotential d
            (variance (fun k : ℤ => (k : ℝ)) νZ) W (sp j).1 (WithLp.toLp 2 (sp j).2) ω)))
        (fun _ => Parking.law d νZ) PW := by
      refine Sandpile.Support.tendstoInDistribution_congr_atTop (fun R => ?_) hXT hjoint
      have h1 := hXm R
      rw [← hmap] at h1
      exact h1.comp_measurable measurable_massField
    have hjS' := tendstoInDistribution_of_comp_map_eq measurable_massField hmap hXm hjS
    set H : (Fin m → ℝ) × (Fin m' → ℝ) → (Fin m' → ℝ) := fun ab k =>
      Sum.elim (fun _ : K => ab.2 k)
        (fun l : Finset.range m => ab.1 ⟨l.1, Finset.mem_range.1 l.2⟩) (x k) with hHdef
    have hHc : Continuous H := by
      refine continuous_pi fun k => ?_
      rcases hxk : x k with q | i
      · simp only [hHdef, hxk, Sum.elim_inl]
        exact (continuous_apply k).comp continuous_snd
      · simp only [hHdef, hxk, Sum.elim_inr]
        exact (continuous_apply _).comp continuous_fst
    have h5 := hjS'.continuous_comp hHc
    refine h5.congr (fun R => Filter.Eventually.of_forall fun σ => ?_) ?_
    · funext k
      rcases hxk : x k with q | i
      · simp only [Function.comp, hHdef, hXdef, hfdef, hspdef, hxk, Sum.elim_inl]
      · simp only [Function.comp, hHdef, hXdef, hfdef, hxk, Sum.elim_inr]
    · have hall : ∀ k : Fin m', ∀ᵐ ω ∂PW,
          H ((fun ω => ((fun i => Real.sqrt (variance (fun k : ℤ => (k : ℝ)) νZ) *
              W (fun y => φ i (WithLp.ofLp y)) ω),
            (fun j => Sandpile.Continuum.gaussianPotential d
              (variance (fun k : ℤ => (k : ℝ)) νZ) W (sp j).1 (WithLp.toLp 2 (sp j).2) ω))) ω) k
            = g ω (x k) := by
        intro k
        rcases hxk : x k with q | i
        · filter_upwards [hZmod q.1.1 q.1.2] with ω hω
          simp only [hHdef, hgdef, hspdef, hxk, Sum.elim_inl, WithLp.toLp_ofLp]
          rw [hω, hvid]
        · refine Filter.Eventually.of_forall fun ω => ?_
          simp only [hHdef, hgdef, hxk, Sum.elim_inr, hvid]
      filter_upwards [ae_all_iff.mpr hall] with ω hω
      funext k
      exact hω k
  have hgm : ∀ x : K ⊕ Finset.range m, AEMeasurable (fun ω => g ω x) PW := by
    rintro (q | i)
    · exact (hgaussmeas q.1.1 q.1.2 (hKT q.property).1.1).aemeasurable.congr
        (hZmod q.1.1 q.1.2).symm
    · exact (measurable_const.mul (hW.meas _ (memLp_test_comp_ofLp _ (hφ _)))).aemeasurable
  have hgc : ∀ᵐ ω ∂PW, Continuous (g ω) := by
    filter_upwards [hZcont] with ω hω
    exact Continuous.sumElim
      (hω.comp_continuous continuous_subtype_val (fun q => hKT q.property))
      continuous_of_discreteTopology
  have heq : ∀ a b : ℝ, 0 < a → 0 < b → ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ R : ℝ in atTop,
      (Sandpile.centeredMassLaw d (νZ.map (fun k : ℤ => (k : ℝ))))
        {σ | ∃ x y : K ⊕ Finset.range m, dist x y < ρ ∧ b < |f R σ x - f R σ y|} ≤
          ENNReal.ofReal a := by
    intro a b ha hb
    obtain ⟨ρ₀, hρ₀, hr⟩ := hosc K hK hKT a b ha hb
    refine ⟨min ρ₀ 1, lt_min hρ₀ one_pos, (eventually_ge_atTop (1 : ℝ)).mono fun R hR => ?_⟩
    refine le_trans (measure_mono ?_) (hr R hR)
    rintro σ ⟨x, y, hxy, hv⟩
    rcases x with p | i <;> rcases y with q | j
    · have h2 : dist p.1 q.1 < min ρ₀ 1 := hxy
      exact ⟨p.1, p.2, q.1, q.2, lt_of_lt_of_le h2 (min_le_left _ _), hv⟩
    · exfalso
      have h1 : (1 : ℝ) ≤ dist (Sum.inl p : K ⊕ Finset.range m) (Sum.inr j) :=
        Metric.Sum.one_le_dist_inl_inr
      have h2 : dist (Sum.inl p : K ⊕ Finset.range m) (Sum.inr j) < min ρ₀ 1 := hxy
      exact absurd (lt_of_lt_of_le h2 (min_le_right _ _)) (not_lt.2 h1)
    · exfalso
      have h1 : (1 : ℝ) ≤ dist (Sum.inr i : K ⊕ Finset.range m) (Sum.inl q) :=
        Metric.Sum.one_le_dist_inr_inl
      have h2 : dist (Sum.inr i : K ⊕ Finset.range m) (Sum.inl q) < min ρ₀ 1 := hxy
      exact absurd (lt_of_lt_of_le h2 (min_le_right _ _)) (not_lt.2 h1)
    · exfalso
      have h2 : dist i j < min ρ₀ 1 := hxy
      have h3 : |((i.1 : ℕ) : ℝ) - ((j.1 : ℕ) : ℝ)| < 1 := by
        rw [← Real.dist_eq]
        exact lt_of_lt_of_le h2 (min_le_right _ _)
      have hij : i = j := Subtype.ext (eq_of_abs_natCast_sub_lt_one h3)
      subst hij
      rw [sub_self, abs_zero] at hv
      exact absurd hv (not_lt.2 hb.le)
  have h := Sandpile.Continuum.exists_field_coupling_on_compact
    (fun _ : ℝ => Sandpile.centeredMassLaw d (νZ.map (fun k : ℤ => (k : ℝ)))) PW f g hgm hgc
    atTop hfd heq ε δ hε hδ
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 h
  refine ⟨max 1 R₀, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro R hR
  obtain ⟨P, hP, hPf, hPs, hbad⟩ := hR₀ R ((le_max_right _ _).trans hR)
  refine ⟨P, hP, hPf, hPs, le_trans (measure_mono ?_) hbad⟩
  rintro p (⟨q, hq, hv⟩ | ⟨i, hv⟩)
  · exact ⟨Sum.inl ⟨q, hq⟩, hv⟩
  · exact ⟨Sum.inr ⟨i.1, Finset.mem_range.2 i.2⟩, hv⟩

/-- **Space-time coupling with retained scenery for integer critical laws.**  The space-time,
scenery-retained form of `Sandpile.dlt4_scaling_of_version` for the sandpile whose one-site law
is the real image of an integer critical law, as consumed by the spatial odometer scaling of the
parking process. -/
theorem spaceTimeCouplingCritical :
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
          ≤ ENNReal.ofReal δ := by
  intro hStab d hd hd3 νZ _ hcrit ν _ hνZ hmean hvar hvar' θ₀ hθ₀ hexp ΩW _ PW _ W hW Z hZmod
    hZcont hZgrow ΩB _ PB _ B hB hBc hBm K hK T₀ T₁ hT₀ hT₀T₁ m φ hφ ε δ hε hδ
  have hT : 0 < T₁ := lt_of_lt_of_le hT₀ hT₀T₁
  obtain ⟨hfdd, htight⟩ := Sandpile.Frozen.heat_potential_invariance d (by omega) hd3
    ν hmean hvar hvar' θ₀ hθ₀ hexp PW W hW T₁ hT
  have hmeasLin : ∀ (R t : ℝ) (y : Sandpile.Continuum.Space d), t ∈ Set.Icc (0 : ℝ) T₁ →
      AEMeasurable (fun σ : Sandpile.Site d → ℝ =>
        Sandpile.Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) t y)
        (Sandpile.centeredMassLaw d ν) := by
    intro R t y ht
    exact (measurable_pi_apply (0 : Fin 1)).comp_aemeasurable
      ((hfdd 1 (fun _ => t) (fun _ => y) (fun _ => ht)).forall_aemeasurable R)
  obtain ⟨R₀, hR₀, h⟩ := dlt4_scaling_of_coupling_uniform hStab d hd hd3 ν hmean hvar hvar' θ₀
    hθ₀ hexp ΩW PW W hW Z hZmod ΩB PB B hB hBc hBm K hK T₀ T₁ hT₀ hT₀T₁ (hZcont T₁ hT)
    (hZgrow T₁ hT) ε δ hε hδ
    (fun R => {p | ∃ i, ε < |R ^ (-(d : ℝ) / 2) *
        ∑' y : Sandpile.Site d, Sandpile.scenery d p.1 y * φ i (fun j => (y j : ℝ) / R)
      - Real.sqrt (variance id ν) * W (fun z => φ i (WithLp.ofLp z)) p.2|})
    (fun C hC hCT η δ' hη hδ' => by
      obtain ⟨R₁, hR₁, hc⟩ := exists_scenery_field_coupling hd hd3 νZ hcrit ν hνZ ΩW PW W hW Z
        hZmod T₁ hT (hZcont T₁ hT) hmeasLin
        (fun K hK hKT ε η hε hη => (htight K hK hKT).2 ε η hε hη) C hC hCT m φ hφ (min η ε)
        δ' (lt_min hη hε) hδ'
      refine ⟨R₁, hR₁, fun R hR => ?_⟩
      obtain ⟨P, hP, h1, h2, h3⟩ := hc R hR
      refine ⟨P, hP, h1, h2, le_trans (measure_mono ?_) h3⟩
      rintro p (⟨q, hq, hv⟩ | ⟨i, hv⟩)
      · exact Or.inl ⟨q, hq, lt_of_le_of_lt (min_le_left _ _) hv⟩
      · exact Or.inr ⟨i, lt_of_le_of_lt (min_le_right _ _) hv⟩)
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  obtain ⟨P, hP, h1, h2, h3⟩ := h R hR
  exact ⟨P, hP, h1, h2, h3⟩

end Parking.Support
