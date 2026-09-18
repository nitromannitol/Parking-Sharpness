/- A measurable source representative compatible with all local weak tests. -/
import Parking.Support.SpatialResidualAlgebra
import Parking.Support.SpatialNoiseCongruence
import Parking.Generic.CompactPositivity
import Parking.Generic.MeasurableLocalChoice

open MeasureTheory Set
noncomputable section
namespace Parking
variable {d : ℕ}

/-- Separate fixed-test identities determine a measurable version of the source
which satisfies all local test identities simultaneously. The field and its
probability space remain unchanged. -/
theorem exists_noise_version_of_fixed_residual
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ)
    (u : Ω → ℝ × (Fin d → ℝ) → ℝ)
    (hu : ∀ ω, Continuous (u ω)) (hum : ∀ p, Measurable fun ω => u ω p)
    (hWm : ∀ φ, IsTestFun φ → Measurable (W φ))
    (hW0 : ∀ᵐ ω ∂Q, W (fun _ => 0) ω = 0)
    (hfixed : ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
      ∀ᵐ ω ∂Q, tsupport ψ ⊆ {p | 0 < u ω p} →
        (∫ p, u ω p * spaceTimeResidualTest ψ p) = W (fun x => ∫ s : ℝ, ψ (s, x)) ω) :
    ∃ W' : ((Fin d → ℝ) → ℝ) → Ω → ℝ,
      (∀ φ, Measurable (W' φ)) ∧
      (∀ φ, IsTestFun φ → W' φ =ᵐ[Q] W φ) ∧
      (∀ᵐ ω ∂Q, ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
        tsupport ψ ⊆ {p | 0 < u ω p} →
        (∫ p, u ω p * spaceTimeResidualTest ψ p) = W' (fun x => ∫ s : ℝ, ψ (s, x)) ω) := by
  classical
  obtain ⟨K, hK, hcover⟩ :=
    Generic.CompactTestCover.exists_sequence_compact_enclosures (ℝ × (Fin d → ℝ))
  let HasTest : ((Fin d → ℝ) → ℝ) → ℕ → Prop := fun φ n =>
    ∃ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ ∧ tsupport ψ ⊆ K n ∧
      (fun x => ∫ s : ℝ, ψ (s, x)) = φ
  let test : ((Fin d → ℝ) → ℝ) → ℕ → ℝ × (Fin d → ℝ) → ℝ := fun φ n =>
    if h : HasTest φ n then Classical.choose h else fun _ => 0
  have htest (φ : (Fin d → ℝ) → ℝ) (n : ℕ) (h : HasTest φ n) :
      IsSpaceTimeTest (test φ n) ∧ tsupport (test φ n) ⊆ K n ∧
        (fun x => ∫ s : ℝ, test φ n (s, x)) = φ := by
    simp only [test, dif_pos h]
    exact Classical.choose_spec h
  have htest0 (φ : (Fin d → ℝ) → ℝ) (n : ℕ) : IsSpaceTimeTest (test φ n) := by
    by_cases h : HasTest φ n
    · exact (htest φ n h).1
    · simp only [test, dif_neg h]
      exact ⟨contDiff_const, by simp [HasCompactSupport], by simp⟩
  let P : ((Fin d → ℝ) → ℝ) → ℕ → Ω → Prop := fun φ n ω =>
    HasTest φ n ∧ K n ⊆ {p | 0 < u ω p}
  have hPm (φ : (Fin d → ℝ) → ℝ) (n : ℕ) : MeasurableSet {ω | P φ n ω} := by
    letI : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
    have hm := Generic.CompactPositivity.measurableSet_forall_pos
      (fun ω => (hu ω).comp (continuous_subtype_val : Continuous (Subtype.val : K n → _)))
      (fun p : K n => hum p)
    have hm' : MeasurableSet {ω | K n ⊆ {p | 0 < u ω p}} := by
      convert hm using 1
      ext ω
      exact ⟨fun h p => h p.property, fun h p hp => h ⟨p, hp⟩⟩
    exact (MeasurableSet.const (HasTest φ n)).inter hm'
  let F : ((Fin d → ℝ) → ℝ) → ℕ → Ω → ℝ := fun φ n ω =>
    ∫ p, u ω p * spaceTimeResidualTest (test φ n) p
  have hFm (φ : (Fin d → ℝ) → ℝ) (n : ℕ) : Measurable (F φ n) :=
    measurable_integral_mul_spaceTimeResidualTest hu hum (htest0 φ n)
  let b : ((Fin d → ℝ) → ℝ) → Ω → ℝ := fun φ => if IsTestFun φ then W φ else fun _ => 0
  have hbm (φ : (Fin d → ℝ) → ℝ) : Measurable (b φ) := by
    by_cases hφ : IsTestFun φ
    · simpa only [b, if_pos hφ] using hWm φ hφ
    · simp only [b, if_neg hφ]
      exact measurable_const
  choose W' hW'm hsel hnone using fun φ =>
    Generic.MeasurableLocalChoice.exists_measurable_selection
      (P φ) (hPm φ) (F φ) (hFm φ) (b φ) (hbm φ)
  refine ⟨W', hW'm, ?_, ?_⟩
  · intro φ hφ
    have hcoords : ∀ n, ∀ᵐ ω ∂Q, P φ n ω → F φ n ω = W φ ω := by
      intro n
      filter_upwards [hfixed (test φ n) (htest0 φ n)] with ω hω hp
      have h := hω ((htest φ n hp.1).2.1.trans hp.2)
      simpa only [(htest φ n hp.1).2.2] using h
    filter_upwards [ae_all_iff.mpr hcoords] with ω hω
    by_cases hp : ∃ n, P φ n ω
    · obtain ⟨n, hn, heq⟩ := hsel φ ω hp
      exact heq.trans (hω n hn)
    · simpa only [b, if_pos hφ] using hnone φ ω hp
  · have hfixed0 : ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
        (∀ x, (∫ s : ℝ, ψ (s, x)) = 0) →
        ∀ᵐ ω ∂Q, tsupport ψ ⊆ {p | 0 < u ω p} →
          (∫ p, u ω p * spaceTimeResidualTest ψ p) = 0 := by
      intro ψ hψ htime
      filter_upwards [hfixed ψ hψ, hW0] with ω hω h0 hsupp
      have h := hω hsupp
      rw [funext htime, h0] at h
      exact h
    filter_upwards [ae_forall_zeroIntegral_residual u hu hfixed0] with ω hω ψ hψ hsupp
    let φ : (Fin d → ℝ) → ℝ := fun x => ∫ s : ℝ, ψ (s, x)
    obtain ⟨n, hψK, hKO⟩ := hcover (tsupport ψ) hψ.2.1
      {p | 0 < u ω p} (isOpen_lt continuous_const (hu ω)) hsupp
    have hp : P φ n ω := ⟨⟨ψ, hψ, hψK, rfl⟩, hKO⟩
    obtain ⟨m, hm, heq⟩ := hsel φ ω ⟨n, hp⟩
    rw [heq]
    exact integral_residual_eq_of_timeIntegral_eq (hu ω) hω hψ (htest φ m hm.1).1
      hsupp ((htest φ m hm.1).2.1.trans hm.2)
      (fun x => (congrFun (htest φ m hm.1).2.2 x).symm)

/-- The driven heat equation for each fixed test supplies a version satisfying
the equation simultaneously, with the same white-noise laws. -/
theorem exists_spatial_noise_version_of_fixed_pde
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω)
    (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ)
    (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ) {intensity : ℝ}
    (hW : IsSpatialWhiteNoise d intensity Q W)
    (hWm : ∀ φ, IsTestFun φ → Measurable (W φ))
    (hu : ∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Uc ω p.1 p.2)
    (hum : ∀ s x, Measurable fun ω => Uc ω s x)
    (hfixed : ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
      ∀ᵐ ω ∂Q, tsupport ψ ⊆ {p | 0 < Uc ω p.1 p.2} →
        -(∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1) =
          (∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * contOp d (fun x => ψ (p.1, x)) p.2) +
            W (fun x => ∫ s : ℝ, ψ (s, x)) ω) :
    ∃ W' : ((Fin d → ℝ) → ℝ) → Ω → ℝ,
      IsSpatialWhiteNoise d intensity Q W' ∧
      (∀ φ, Measurable (W' φ)) ∧ (∀ φ, IsTestFun φ → W' φ =ᵐ[Q] W φ) ∧
      (∀ᵐ ω ∂Q, ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
        tsupport ψ ⊆ {p | 0 < Uc ω p.1 p.2} →
          -(∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * deriv (fun s => ψ (s, p.2)) p.1) =
            (∫ p : ℝ × (Fin d → ℝ), Uc ω p.1 p.2 * contOp d (fun x => ψ (p.1, x)) p.2) +
              W' (fun x => ∫ s : ℝ, ψ (s, x)) ω) := by
  have hres : ∀ ψ : ℝ × (Fin d → ℝ) → ℝ, IsSpaceTimeTest ψ →
      ∀ᵐ ω ∂Q, tsupport ψ ⊆ {p | 0 < Uc ω p.1 p.2} →
        (∫ p, Uc ω p.1 p.2 * spaceTimeResidualTest ψ p) =
          W (fun x => ∫ s : ℝ, ψ (s, x)) ω := by
    intro ψ hψ
    filter_upwards [hfixed ψ hψ] with ω hω hsupp
    rw [integral_spaceTimeResidualTest (hu ω) hψ]
    linarith [hω hsupp]
  obtain ⟨W', hW'm, heq, hsim⟩ := exists_noise_version_of_fixed_residual Q W
    (fun ω p => Uc ω p.1 p.2) hu (fun p => hum p.1 p.2) hWm (whiteNoise_apply_zero hW) hres
  refine ⟨W', isSpatialWhiteNoise_congr hW heq, hW'm, heq, ?_⟩
  filter_upwards [hsim] with ω hω ψ hψ hsupp
  have h := hω ψ hψ hsupp
  rw [integral_spaceTimeResidualTest (hu ω) hψ] at h
  linarith

end Parking
