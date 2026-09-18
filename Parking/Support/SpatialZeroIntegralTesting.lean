/- Simultaneous testing on a fixed compact subset of the positive region. -/
import Parking.Generic.CompactTesting
import Parking.Generic.CompactTestCover
import Parking.Support.SpaceTimeContOp

open MeasureTheory Set
noncomputable section
namespace Parking
variable {d : ℕ}

/-- The test coefficient for the driven heat equation. -/
def spaceTimeResidualTest (ψ : ℝ × (Fin d → ℝ) → ℝ) (p : ℝ × (Fin d → ℝ)) : ℝ :=
  -timeDeriv ψ p - contOp d (fun x => ψ (p.1, x)) p.2

theorem continuous_spaceTimeResidualTest {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : IsSpaceTimeTest ψ) : Continuous (spaceTimeResidualTest ψ) :=
  (contDiff_timeDeriv hψ.1).continuous.neg.sub (contDiff_spaceTime_contOp hψ.1).continuous

theorem spaceTimeResidualTest_eq_zero_of_notMem {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : IsSpaceTimeTest ψ) {p : ℝ × (Fin d → ℝ)} (hp : p ∉ tsupport ψ) :
    spaceTimeResidualTest ψ p = 0 := by
  have ht : timeDeriv ψ p = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hp (tsupport_timeDeriv_subset ψ h))
  have hx : contOp d (fun x => ψ (p.1, x)) p.2 = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun q : ℝ × (Fin d → ℝ) =>
      contOp d (fun x => ψ (q.1, x)) q.2)
      (fun h => hp (tsupport_spaceTime_contOp_subset hψ.1 h))
  simp [spaceTimeResidualTest, ht, hx]

theorem integral_spaceTimeResidualTest {u ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hu : Continuous u) (hψ : IsSpaceTimeTest ψ) :
    (∫ p, u p * spaceTimeResidualTest ψ p) =
      -(∫ p, u p * deriv (fun s => ψ (s, p.2)) p.1) -
        ∫ p, u p * contOp d (fun x => ψ (p.1, x)) p.2 := by
  have ht := integrable_mul_timeSlice_deriv hu hψ
  simp_rw [deriv_timeSlice (hψ.1.differentiable (by simp)), Prod.mk.eta] at ht ⊢
  simp only [spaceTimeResidualTest, mul_sub, mul_neg]
  rw [integral_sub (f := fun p => -(u p * timeDeriv ψ p))
    ht.neg (integrable_mul_spaceTime_contOp hu hψ), integral_neg]

/-- The separate almost-sure zero-source test identities on a fixed compact set
hold on a common event. The compact set, rather than the individual test, fixes
which samples qualify. -/
theorem ae_forall_zeroIntegral_residual_on_compact
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    (u : Ω → ℝ × (Fin d → ℝ) → ℝ) (hu : ∀ ω, Continuous (u ω))
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K)
    (hfixed : ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
      (∀ x, (∫ s : ℝ, ψ (s, x)) = 0) →
      ∀ᵐ ω ∂Q, tsupport ψ ⊆ {p | 0 < u ω p} →
        (∫ p, u ω p * spaceTimeResidualTest ψ p) = 0) :
    ∀ᵐ ω ∂Q, K ⊆ {p | 0 < u ω p} →
      ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ → tsupport ψ ⊆ K →
        (∀ x, (∫ s : ℝ, ψ (s, x)) = 0) →
        (∫ p, u ω p * spaceTimeResidualTest ψ p) = 0 := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let μ : Measure K := volume.comap Subtype.val
  haveI : IsFiniteMeasure μ := ⟨by
    apply (Measure.comap_apply_le Subtype.val volume nullMeasurableSet_univ).trans_lt
    simpa using hK.measure_lt_top (μ := volume)⟩
  let T := {ψ : ℝ × (Fin d → ℝ) → ℝ // IsSpaceTimeTest ψ ∧ tsupport ψ ⊆ K ∧
    ∀ x, (∫ s : ℝ, ψ (s, x)) = 0}
  let U : Ω → C(K, ℝ) := fun ω => ⟨fun p => u ω p, (hu ω).comp continuous_subtype_val⟩
  let J : T → C(K, ℝ) := fun ψ => ⟨fun p => spaceTimeResidualTest ψ.1 p,
    (continuous_spaceTimeResidualTest ψ.2.1).comp continuous_subtype_val⟩
  have hid (ω : Ω) (ψ : T) : (∫ p, U ω p * J ψ p ∂μ) =
      ∫ p, u ω p * spaceTimeResidualTest ψ.1 p := by
    change (∫ p : K, u ω p * spaceTimeResidualTest ψ.1 p ∂volume.comap Subtype.val) = _
    rw [integral_subtype_comap hK.measurableSet
      (fun p => u ω p * spaceTimeResidualTest ψ.1 p)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    rw [spaceTimeResidualTest_eq_zero_of_notMem ψ.2.1 (fun h => hp (ψ.2.2.1 h)), mul_zero]
  have ht : ∀ ψ : T, ∀ᵐ ω ∂Q, K ⊆ {p | 0 < u ω p} →
      (∫ p, U ω p * J ψ p ∂μ) = 0 := by
    intro ψ
    filter_upwards [hfixed ψ.1 ψ.2.1 ψ.2.2.2] with ω hω hpos
    rw [hid]
    exact hω (ψ.2.2.1.trans hpos)
  have hall := Generic.SimultaneousTesting.ae_forall_integral_mul_eq_zero U J ht
  filter_upwards [hall] with ω hω hpos ψ hψ hsupp hzero
  simpa only [hid] using hω hpos ⟨ψ, hψ, hsupp, hzero⟩

/-- Zero-time-integral tests admit a common full-measure event on the entire
random open positive region. No samplewise regularity of a noise representative
is needed for this step. -/
theorem ae_forall_zeroIntegral_residual
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    (u : Ω → ℝ × (Fin d → ℝ) → ℝ) (hu : ∀ ω, Continuous (u ω))
    (hfixed : ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
      (∀ x, (∫ s : ℝ, ψ (s, x)) = 0) →
      ∀ᵐ ω ∂Q, tsupport ψ ⊆ {p | 0 < u ω p} →
        (∫ p, u ω p * spaceTimeResidualTest ψ p) = 0) :
    ∀ᵐ ω ∂Q, ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
      tsupport ψ ⊆ {p | 0 < u ω p} → (∀ x, (∫ s : ℝ, ψ (s, x)) = 0) →
        (∫ p, u ω p * spaceTimeResidualTest ψ p) = 0 := by
  obtain ⟨S, hSc, hSK, hcover⟩ :=
    Generic.CompactTestCover.exists_countable_compact_enclosures (ℝ × (Fin d → ℝ))
  have hall : ∀ᵐ ω ∂Q, ∀ K ∈ S, K ⊆ {p | 0 < u ω p} →
      ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ → tsupport ψ ⊆ K →
        (∀ x, (∫ s : ℝ, ψ (s, x)) = 0) →
          (∫ p, u ω p * spaceTimeResidualTest ψ p) = 0 :=
    (ae_ball_iff hSc).mpr fun K hK =>
      ae_forall_zeroIntegral_residual_on_compact u hu (hSK K hK) hfixed
  filter_upwards [hall] with ω hω ψ hψ hsupp hzero
  obtain ⟨K, hKS, hψK, hKO⟩ := hcover (tsupport ψ) hψ.2.1
    {p | 0 < u ω p} (isOpen_lt continuous_const (hu ω)) hsupp
  exact hω K hKS hKO ψ hψ hψK hzero

end Parking
