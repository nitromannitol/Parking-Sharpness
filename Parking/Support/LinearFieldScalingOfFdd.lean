import Parking.Support.SandpileLawBridge
import Parking.Support.LinearFieldMeasurable
import Sandpile.Frozen.HeatPotentialInvariance
import Sandpile.Support.StopFieldCoupling
import Sandpile.Support.MainExplWeak

/-!
# Joint scaling of scenery and the linear field

Auxiliary results for the joint scaling of the scenery and the interpolated linear field.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Parking.Support

/-- Joint convergence of integrals implies convergence of integrals in the second coordinate. -/
theorem tendsto_integral_snd_of_joint
    {A B Ω Ω' : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (a : ℝ → Ω → A) (b : ℝ → Ω → B)
    (a' : Ω' → A) (b' : Ω' → B)
    (h : ∀ F : BoundedContinuousFunction (A × B) ℝ,
      Tendsto (fun R : ℝ => ∫ ω, F (a R ω, b R ω) ∂μ) atTop
        (𝓝 (∫ ω, F (a' ω, b' ω) ∂ν)))
    (F : BoundedContinuousFunction B ℝ) :
    Tendsto (fun R : ℝ => ∫ ω, F (b R ω) ∂μ) atTop (𝓝 (∫ ω, F (b' ω) ∂ν)) := by
  simpa only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk] using
    h (F.compContinuous ⟨Prod.snd, continuous_snd⟩)

/-- A critical integer law has strictly positive finite variance. -/
theorem criticalLaw_variance_pos (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    0 < variance (fun k : ℤ => (k : ℝ)) ν := by
  obtain ⟨_, _, hpos, hfin, _, hvariance⟩ := Parking.criticalLaw_moments ν hν
  rw [← hvariance]
  exact ENNReal.toReal_pos (ne_of_gt hpos) (ne_of_lt hfin)

/-- Finite-dimensional convergence is preserved by selecting coordinates from either block. -/
theorem tendstoInDistribution_select_coordinates
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m n k : ℕ} (f : ℝ → Ω → Fin m → ℝ) (g : ℝ → Ω → Fin n → ℝ)
    (f' : Ω' → Fin m → ℝ) (g' : Ω' → Fin n → ℝ) (s : Fin k → Fin m ⊕ Fin n)
    (h : TendstoInDistribution (fun R ω => (f R ω, g R ω)) atTop
      (fun ω => (f' ω, g' ω)) (fun _ : ℝ => μ) ν) :
    TendstoInDistribution (fun R ω j => Sum.elim (f R ω) (g R ω) (s j)) atTop
      (fun ω j => Sum.elim (f' ω) (g' ω) (s j)) (fun _ : ℝ => μ) ν := by
  let proj : ((Fin m → ℝ) × (Fin n → ℝ)) → Fin k → ℝ :=
    fun p j => Sum.elim p.1 p.2 (s j)
  have hp : Continuous proj := by
    apply continuous_pi
    intro j
    cases hsj : s j with
    | inl i => simpa only [proj, hsj, Sum.elim_inl, Function.comp_def] using
        (continuous_apply i).comp (continuous_fst : Continuous (Prod.fst :
          ((Fin m → ℝ) × (Fin n → ℝ)) → (Fin m → ℝ)))
    | inr i => simpa only [proj, hsj, Sum.elim_inr, Function.comp_def] using
        (continuous_apply i).comp (continuous_snd : Continuous (Prod.snd :
          ((Fin m → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ)))
  simpa only [Function.comp_def, proj] using h.continuous_comp hp

/-- A uniform bound on a field over the support bounds the difference of its cutoffs. -/
theorem dist_cutoffBC_le {d : ℕ} (χ f g : ℝ × (Fin d → ℝ) → ℝ)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hf : Continuous f) (hg : Continuous g)
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hχM : ∀ p, |χ p| ≤ M)
    (hfg : ∀ p ∈ tsupport χ, |f p - g p| ≤ ε) :
    dist (Parking.cutoffBC χ f hχ hχc hf) (Parking.cutoffBC χ g hχ hχc hg) ≤ M * ε := by
  apply (BoundedContinuousFunction.dist_le (mul_nonneg hM hε)).2
  intro p
  change |χ p * f p - χ p * g p| ≤ M * ε
  by_cases hp : p ∈ tsupport χ
  · rw [← mul_sub, abs_mul]
    exact mul_le_mul (hχM p) (hfg p hp) (abs_nonneg _) hM
  · rw [image_eq_zero_of_notMem_tsupport hp]
    simpa using mul_nonneg hM hε

/-- Coordinatewise almost-everywhere versions give the same finite-dimensional limit. -/
theorem tendstoInDistribution_select_coordinates_of_ae
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m n k : ℕ} (f : ℝ → Ω → Fin m → ℝ) (g : ℝ → Ω → Fin n → ℝ)
    (f' f'' : Ω' → Fin m → ℝ) (g' g'' : Ω' → Fin n → ℝ)
    (s : Fin k → Fin m ⊕ Fin n)
    (hf : ∀ i, (fun ω => f' ω i) =ᵐ[ν] fun ω => f'' ω i)
    (hg : ∀ i, (fun ω => g' ω i) =ᵐ[ν] fun ω => g'' ω i)
    (h : TendstoInDistribution (fun R ω => (f R ω, g R ω)) atTop
      (fun ω => (f' ω, g' ω)) (fun _ : ℝ => μ) ν) :
    TendstoInDistribution (fun R ω j => Sum.elim (f R ω) (g R ω) (s j)) atTop
      (fun ω j => Sum.elim (f'' ω) (g'' ω) (s j)) (fun _ : ℝ => μ) ν := by
  apply (tendstoInDistribution_select_coordinates μ ν f g f' g' s h).congr
    (fun _ => Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [ae_all_iff.mpr hf, ae_all_iff.mpr hg] with ω hωf hωg
  funext j
  cases hs : s j with
  | inl i => simpa only [hs, Sum.elim_inl] using hωf i
  | inr i => simpa only [hs, Sum.elim_inr] using hωg i

/-- Equicontinuity in probability is preserved by a uniformly continuous change of index
and a measurable change of law. -/
theorem eventually_oscillation_le_of_map
    {Ω Ω' E F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [PseudoMetricSpace E] [PseudoMetricSpace F]
    (μ : Measure Ω) (ν : Measure Ω') (A : Ω → Ω') (hA : Measurable A)
    (hmap : μ.map A = ν) (φ : E → F) (hφ : UniformContinuous φ)
    (f : ℝ → Ω → E → ℝ) (g : ℝ → Ω' → F → ℝ)
    (heq : ∀ᶠ R in atTop, ∀ ω x, f R ω x = g R (A ω) (φ x))
    (htight : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ R in atTop,
      ν {ω | ∃ x y : F, dist x y < ρ ∧ η < |g R ω x - g R ω y|} ≤ ENNReal.ofReal ε) :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ R in atTop,
      μ {ω | ∃ x y : E, dist x y < δ ∧ η < |f R ω x - f R ω y|} ≤ ENNReal.ofReal ε := by
  intro ε η hε hη
  obtain ⟨ρ, hρ, hbound⟩ := htight ε η hε hη
  obtain ⟨δ, hδ, hδρ⟩ := Metric.uniformContinuous_iff.mp hφ ρ hρ
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [heq, hbound] with R hR hboundR
  let S : Set Ω' := {ω | ∃ x y : F, dist x y < ρ ∧ η < |g R ω x - g R ω y|}
  calc
    μ {ω | ∃ x y : E, dist x y < δ ∧ η < |f R ω x - f R ω y|} ≤ μ (A ⁻¹' S) := by
      apply measure_mono
      rintro ω ⟨x, y, hxy, hdiff⟩
      exact ⟨φ x, φ y, hδρ hxy, by simpa only [hR] using hdiff⟩
    _ ≤ μ.map A S := Measure.le_map_apply hA.aemeasurable S
    _ = ν S := by rw [hmap]
    _ ≤ ENNReal.ofReal ε := hboundR

/-- Compact-field couplings yield weak convergence of continuous functionals of the field. -/
theorem tendstoInDistribution_of_compact_field
    {E B Ω Ω' : Type*} [MetricSpace E] [CompactSpace E]
    [PseudoMetricSpace B] [MeasurableSpace B] [BorelSpace B]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : ℝ → Ω → E → ℝ) (g : Ω' → E → ℝ)
    (X : ℝ → Ω → B) (Y : Ω' → B)
    (hX : ∀ R, AEMeasurable (X R) μ) (hY : AEMeasurable Y ν)
    (hg : ∀ x, AEMeasurable (fun ω => g ω x) ν)
    (hc : ∀ᵐ ω ∂ν, Continuous (g ω))
    (hfdd : ∀ (m : ℕ) (x : Fin m → E), TendstoInDistribution
      (fun R ω k => f R ω (x k)) atTop (fun ω k => g ω (x k)) (fun _ => μ) ν)
    (htight : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ R in atTop,
      μ {ω | ∃ x y : E, dist x y < ρ ∧ η < |f R ω x - f R ω y|} ≤ ENNReal.ofReal ε)
    (hcontrol : ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ R ω ω',
      (∀ x, |f R ω x - g ω' x| ≤ ρ) → dist (X R ω) (Y ω') ≤ ε) :
    TendstoInDistribution X atTop Y (fun _ => μ) ν := by
  apply Sandpile.Continuum.tendstoInDistribution_of_coupling μ ν X Y hX hY
  intro ε δ hε hδ
  obtain ⟨ρ, hρ, hcontrol⟩ := hcontrol ε hε
  have hevent := Sandpile.Continuum.exists_field_coupling_on_compact
    (fun _ : ℝ => μ) ν f g hg hc atTop hfdd htight ρ δ hρ hδ
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hevent
  refine ⟨R₀, fun R hR => ?_⟩
  obtain ⟨P, hP, hfst, hsnd, hbad⟩ := hR₀ R hR
  refine ⟨P, hP, hfst, hsnd, (measure_mono ?_).trans hbad⟩
  intro p hp
  by_contra hno
  have hclose : ∀ x, |f R p.1 x - g p.2 x| ≤ ρ := by
    intro x
    exact le_of_not_gt (fun hx => hno ⟨x, hx⟩)
  exact (not_lt_of_ge (hcontrol R p.1 p.2 hclose)) hp

/-- Joint finite-dimensional convergence gives convergence on the disjoint index space. -/
theorem tendstoInDistribution_mixed_field
    (d : ℕ) (ν : Measure ℤ) [IsProbabilityMeasure (Parking.law d ν)]
    {Ω' : Type} [MeasurableSpace Ω'] (Q' : Measure Ω') [IsProbabilityMeasure Q']
    (WD : (Sandpile.Continuum.Space d → ℝ) → Ω' → ℝ)
    (W : ((Fin d → ℝ) → ℝ) → Ω' → ℝ)
    (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ)
    (hW : ∀ φ, Parking.IsTestFun φ → W φ =ᵐ[Q'] WD (fun y => φ (WithLp.ofLp y)))
    (hZ : ∀ t x, 0 ≤ t → (fun ω => Z ω t x) =ᵐ[Q']
      fun ω => Sandpile.Continuum.gaussianPotential d
        (variance (fun k : ℤ => (k : ℝ)) ν) WD t (WithLp.toLp 2 x) ω)
    (m : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ) (hφ : ∀ i, Parking.IsTestFun (φ i))
    (hjoint : ∀ (p : ℕ) (sp : Fin p → ℝ × (Fin d → ℝ)), (∀ j, 0 ≤ (sp j).1) →
      TendstoInDistribution
        (fun (R : ℝ) (w : Parking.Data d) =>
          ((fun i => Parking.scenePair w R (φ i)),
            (fun j => Parking.linHatInterp (fun y => (w.1 y : ℝ)) R (sp j)))) atTop
        (fun ω => ((fun i => Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) *
          WD (fun y => φ i (WithLp.ofLp y)) ω),
          (fun j => Sandpile.Continuum.gaussianPotential d
            (variance (fun k : ℤ => (k : ℝ)) ν) WD (sp j).1 (WithLp.toLp 2 (sp j).2) ω)))
        (fun _ => Parking.law d ν) Q')
    (K : Set (ℝ × (Fin d → ℝ))) (hK : ∀ p ∈ K, 0 ≤ p.1)
    (k : ℕ) (x : Fin k → K ⊕ Fin m) :
    TendstoInDistribution (fun R w j => match x j with
      | .inl p => Parking.linHatInterp (fun y => (w.1 y : ℝ)) R p.1
      | .inr i => Parking.scenePair w R (φ i)) atTop
      (fun ω j => match x j with
      | .inl p => Z ω p.1.1 p.1.2
      | .inr i => Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) * W (φ i) ω)
      (fun _ : ℝ => Parking.law d ν) Q' := by
  let sp : Fin k → ℝ × (Fin d → ℝ) := fun j => match x j with
    | .inl p => p.1
    | .inr _ => (0, 0)
  let s : Fin k → Fin m ⊕ Fin k := fun j => match x j with
    | .inl _ => .inr j
    | .inr i => .inl i
  have hsp : ∀ j, 0 ≤ (sp j).1 := by
    intro j
    cases hx : x j with
    | inl p => simpa [sp, hx] using hK p.1 p.2
    | inr i => simp [sp, hx]
  have hf : ∀ i, (fun ω => Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) *
      WD (fun y => φ i (WithLp.ofLp y)) ω) =ᵐ[Q']
      fun ω => Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) * W (φ i) ω := by
    intro i
    filter_upwards [(hW (φ i) (hφ i)).symm] with ω hω
    rw [hω]
  have hg : ∀ j, (fun ω => Sandpile.Continuum.gaussianPotential d
      (variance (fun k : ℤ => (k : ℝ)) ν) WD (sp j).1 (WithLp.toLp 2 (sp j).2) ω) =ᵐ[Q']
      fun ω => Z ω (sp j).1 (sp j).2 := fun j => (hZ (sp j).1 (sp j).2 (hsp j)).symm
  have h := tendstoInDistribution_select_coordinates_of_ae (Parking.law d ν) Q'
    (fun R w i => Parking.scenePair w R (φ i))
    (fun R w j => Parking.linHatInterp (fun y => (w.1 y : ℝ)) R (sp j))
    (fun ω i => Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) *
      WD (fun y => φ i (WithLp.ofLp y)) ω)
    (fun ω i => Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) * W (φ i) ω)
    (fun ω j => Sandpile.Continuum.gaussianPotential d
      (variance (fun k : ℤ => (k : ℝ)) ν) WD (sp j).1 (WithLp.toLp 2 (sp j).2) ω)
    (fun ω j => Z ω (sp j).1 (sp j).2) s hf hg (hjoint k sp hsp)
  have hsource : (fun (R : ℝ) (w : Parking.Data d) (j : Fin k) => Sum.elim
      (fun i => Parking.scenePair w R (φ i))
      (fun j => Parking.linHatInterp (fun y => (w.1 y : ℝ)) R (sp j)) (s j)) =
      (fun R w j => match x j with
      | .inl p => Parking.linHatInterp (fun y => (w.1 y : ℝ)) R p.1
      | .inr i => Parking.scenePair w R (φ i)) := by
    funext R w j
    cases hx : x j <;> simp [s, sp, hx]
  have hlimit : (fun (ω : Ω') (j : Fin k) => Sum.elim
      (fun i => Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) * W (φ i) ω)
      (fun j => Z ω (sp j).1 (sp j).2) (s j)) =
      (fun ω j => match x j with
      | .inl p => Z ω p.1.1 p.1.2
      | .inr i => Real.sqrt (variance (fun k : ℤ => (k : ℝ)) ν) * W (φ i) ω) := by
    funext ω j
    cases hx : x j <;> simp [s, sp, hx]
  rw [hsource, hlimit] at h
  exact h

end Parking.Support
