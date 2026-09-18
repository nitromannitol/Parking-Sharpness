/- Fixed-test identification of the continuum heat equation from joint weak convergence. -/
import Parking.Support.SpatialResidualCutoff
import Parking.Support.SpatialSpaceTimeFunctional
import Parking.Support.SpatialResidualAlgebra
import Parking.Support.SpatialVanishingDistance

open MeasureTheory Set Filter Topology
open Parking.Generic.PositiveCutoff Parking.Generic.LocalResidual
noncomputable section
namespace Parking
variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    {W : ((Fin d → ℝ) → ℝ) → Ω → ℝ} {Uc : Ω → ℝ → (Fin d → ℝ) → ℝ}

/-- Every fixed supported test satisfies the weak equation on the original explicit limit space. -/
theorem spatial_fixed_test_residual_ae
    (hd : 1 ≤ d) (hd3 : d ≤ 3) (hGrowth : External.SandpileGrowth)
    (ν : Measure ℤ) (hν : CriticalLaw ν)
    (hUccont : ∀ ω, Continuous fun q : ℝ × (Fin d → ℝ) => Uc ω q.1 q.2)
    (hUcmeas : ∀ s x, Measurable fun ω => Uc ω s x)
    (hWmeas : ∀ φ, IsTestFun φ → Measurable (W φ))
    (hjointFDD : ∀ (m p' : ℕ) (φ : Fin m → (Fin d → ℝ) → ℝ)
      (sp : Fin p' → ℝ × (Fin d → ℝ)),
      (∀ i, IsTestFun (φ i)) → (∀ j, 0 < (sp j).1) →
      ∀ F : BoundedContinuousFunction ((Fin m → ℝ) × (Fin p' → ℝ)) ℝ,
        Tendsto (fun R : ℝ => ∫ w, F (fun i => scenePair w R (φ i),
              fun j => barDivisible w R (sp j).1 (sp j).2) ∂law d ν) atTop
          (𝓝 (∫ ω, F (fun i => W (φ i) ω, fun j => Uc ω (sp j).1 (sp j).2) ∂Q)))
    (hequicont : ∀ K : Set (ℝ × (Fin d → ℝ)), IsCompact K →
      (∀ p ∈ K, 0 < p.1) → ∀ ε : ℝ, 0 < ε → ∀ ε' : ℝ, 0 < ε' →
        ∃ δ : ℝ, 0 < δ ∧ ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
          ((law d ν) {w | ε < ⨆ p ∈ K, ⨆ q ∈ K, ⨆ _ : dist p q ≤ δ,
            |barDivisible w R p.1 p.2 - barDivisible w R q.1 q.2|}).toReal ≤ ε')
    {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ) :
    ∀ᵐ ω ∂Q, tsupport ψ ⊆ {p | 0 < Uc ω p.1 p.2} →
      (∫ p, Uc ω p.1 p.2 * spaceTimeResidualTest ψ p) = W (fun x => ∫ s : ℝ, ψ (s, x)) ω := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  obtain ⟨T, hT, hTsupp, _, _, hsource⟩ :=
    exists_tendsto_scenePair_time_quadrature_with_support hd hd3 ν hν.integrable_abs hψ
  obtain ⟨H, hH⟩ := hψ.2.1.isCompact.exists_bound_of_continuousOn
    (f := fun p : ℝ × (Fin d → ℝ) => p.1) continuous_fst.continuousOn
  obtain ⟨c, hc, _, hclow⟩ := exists_time_bounds (tsupport ψ) hψ.2.1 hψ.2.2 H hH
  let a := c / 2
  have ha : 0 < a := half_pos hc
  have hlow : ∀ s x, s < 2 * a → ψ (s, x) = 0 := by
    intro s x hs
    by_contra hn
    have := hclow (s, x) (subset_tsupport ψ hn)
    dsimp [a] at hs
    linarith
  have hhigh : ∀ s x, T ≤ s → ψ (s, x) = 0 := by
    intro s x hs
    by_contra hn
    exact (not_lt.mpr hs) (hTsupp (s, x) (subset_tsupport ψ hn))
  obtain ⟨B0, hB0⟩ := hψ.2.1.isCompact.exists_bound_of_continuousOn
    (f := fun p : ℝ × (Fin d → ℝ) => p.2) continuous_snd.continuousOn
  let B := max B0 1
  have hb : ∀ s x, ψ (s, x) ≠ 0 → ‖x‖ ≤ B :=
    fun s x hx => (hB0 (s, x) (subset_tsupport ψ hx)).trans (le_max_left _ _)
  let K : Set (ℝ × (Fin d → ℝ)) := Icc a (T + 1) ×ˢ Metric.closedBall 0 (B + 2)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKt : ∀ p ∈ K, 0 < p.1 := fun p hp => ha.trans_le hp.1.1
  have hSK : tsupport ψ ⊆ K := by
    intro p hp
    refine ⟨⟨?_, (hTsupp p hp).le.trans (by linarith)⟩, ?_⟩
    · exact (half_le_self hc.le).trans (hclow p hp)
    · have hx := (hB0 p hp).trans (le_max_left B0 1)
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx.trans (show B ≤ B + 2 by linarith)
  haveI : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top (μ := volume)⟩
  let φ : (Fin d → ℝ) → ℝ := fun x => ∫ s : ℝ, ψ (s, x)
  have hφ : IsTestFun φ := isTestFun_timeIntegral hψ
  have hAc := continuous_spaceTimeResidualTest hψ
  obtain ⟨M0, hM0⟩ := hK.exists_bound_of_continuousOn hAc.continuousOn
  let M := max M0 0
  have hM : 0 ≤ M := le_max_right _ _
  have hAb : ∀ p ∈ K, |spaceTimeResidualTest ψ p| ≤ M :=
    fun p hp => (hM0 p hp).trans (le_max_left _ _)
  have hlimitmeas : ∀ δ : ℝ, Measurable (fun ω => test volume K (tsupport ψ) δ
      (spaceTimeResidualTest ψ) (W φ ω) (fun p => Uc ω p.1 p.2)) := by
    intro δ
    have hcm := measurable_cutoff_continuous (tsupport ψ) δ
      (fun ω p => Uc ω p.1 p.2) hUccont (fun p => hUcmeas p.1 p.2)
    have hj : Measurable (fun p : Ω × (ℝ × (Fin d → ℝ)) => Uc p.1 p.2.1 p.2.2) :=
      (measurable_uncurry_of_continuous_of_measurable hUccont
        (fun p => hUcmeas p.1 p.2)).comp measurable_swap
    have hi : Measurable (fun ω => ∫ p in K, Uc ω p.1 p.2 * spaceTimeResidualTest ψ p) :=
      (hj.mul (hAc.measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
    exact hcm.mul (measurable_const.min ((hi.sub (hWmeas φ hφ)).abs))
  have hz : ∀ n : ℕ, (∫ ω, test volume K (tsupport ψ) (1 / ((n : ℝ) + 1))
      (spaceTimeResidualTest ψ) (W φ ω) (fun p => Uc ω p.1 p.2) ∂Q) = 0 := by
    intro n
    let δ := 1 / ((n : ℝ) + 1)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    let Φ : (Fin 1 → ℝ) → ((ℝ × (Fin d → ℝ)) → ℝ) → ℝ :=
      fun b u => test volume K (tsupport ψ) δ (spaceTimeResidualTest ψ) (b 0) u
    have ht := tendsto_integral_scenePair_spaceTime_functional hd ν hUccont hUcmeas hWmeas
      hjointFDD hequicont (fun _ : Fin 1 => φ) (fun _ => hφ) hK hKt
      (Φ := Φ) (Eventually.of_forall fun R => measurable_discreteResidualTest hψ K δ R)
      (M := 1) (C := 1 / δ + volume.real K * M) (D := 1)
      (fun b u => by rw [abs_of_nonneg (test_nonneg _ _ _ _ _ _ _)]; exact test_le_one _ _ _ _ _ _ _)
      (by positivity) zero_le_one
      (fun b u v hum hvm hub hvb => Generic.LocalResidual.abs_test_sub_le
        hK.measurableSet hSK hδ hAc.measurable hM hAb (b 0) hum hvm hub hvb)
      (fun b c u _ _ => by
        have hh := abs_test_block_sub_le volume K (tsupport ψ) δ (spaceTimeResidualTest ψ) (b 0) (c 0) u
        exact hh.trans (by simpa only [Real.dist_eq, one_mul] using dist_le_pi_dist b c 0))
    have ht0 := tendsto_integral_discreteResidualTest_zero hd hd3 hGrowth ν hν hψ ha hT hlow hhigh hb hsource hδ
    exact tendsto_nhds_unique ht ht0
  have hall := Generic.LocalResidual.ae_pairing_eq_of_cutoff_integrals (μ := volume) (K := K)
    (S := tsupport ψ) Q hψ.2.1 (fun ω p => Uc ω p.1 p.2) (W φ) (spaceTimeResidualTest ψ)
    hUccont (fun n => hlimitmeas _) hz
  filter_upwards [hall] with ω hω hpos
  have he := hω hpos
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
    rw [spaceTimeResidualTest_eq_zero_of_notMem hψ (fun h => hp (hSK h)), mul_zero])] at he
  exact he

end Parking
