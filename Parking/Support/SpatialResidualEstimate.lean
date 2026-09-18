/- The weak residual is bounded by an arbitrarily small multiple of local mass. -/
import Parking.Support.SpatialParabolicSupport
import Parking.Support.SpatialSpaceTimeMass
import Parking.Support.SpatialZeroIntegralTesting
import Parking.Generic.CompactPairing

open MeasureTheory Set Filter Topology LatticeProb
noncomputable section
namespace Parking
variable {d : ℕ}

theorem measurable_parabolicIndex (R : ℝ) :
    Measurable (fun p : ℝ × (Fin d → ℝ) => (⌊p.1 * R ^ 2⌋₊, latticePoint R p.2)) := by
  exact (Nat.measurable_floor.comp (measurable_fst.mul_const _)).prodMk
    (measurable_pi_lambda _ fun i => Int.measurable_floor.comp
      (measurable_const.mul ((measurable_pi_apply i).comp measurable_snd)))

theorem measurable_parabolicTimeTest (ψ : ℝ × (Fin d → ℝ) → ℝ) (R : ℝ) :
    Measurable (parabolicTimeTest ψ R) := by
  exact (measurable_from_countable' (fun q : ℕ × Site d => R ^ 2 *
    (ψ ((q.1 : ℝ) / R ^ 2 + 1 / R ^ 2, fun i => (q.2 i : ℝ) / R) -
      ψ ((q.1 : ℝ) / R ^ 2, fun i => (q.2 i : ℝ) / R)))).comp (measurable_parabolicIndex R)

theorem measurable_parabolicSpaceTest (ψ : ℝ × (Fin d → ℝ) → ℝ) (R : ℝ) :
    Measurable (parabolicSpaceTest ψ R) := by
  let f : ℕ × Site d → ℝ := fun q => R ^ 2 *
    (walkOp (fun y => ψ ((q.1 : ℝ) / R ^ 2 + 1 / R ^ 2, fun i => (y i : ℝ) / R)) q.2 -
      ψ ((q.1 : ℝ) / R ^ 2 + 1 / R ^ 2, fun i => (q.2 i : ℝ) / R))
  have hf : Measurable f := measurable_from_countable' f
  have he : parabolicSpaceTest ψ R = f ∘
      (fun p : ℝ × (Fin d → ℝ) => (⌊p.1 * R ^ 2⌋₊, latticePoint R p.2)) := rfl
  rw [he]
  exact hf.comp (measurable_parabolicIndex R)

/-- Restricting to a compact set containing both coefficients preserves the tested identity. -/
theorem barDivisible_tested_compact (w : Data d)
    {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ) (T : ℝ)
    {R : ℝ} (hR : 1 ≤ R) (hzero : ∀ x, ψ (0, x) = 0)
    (hfinal : ∀ x, ψ (((⌈T * R ^ 2⌉₊ : ℝ) / R ^ 2), x) = 0)
    (hpos : tsupport ψ ⊆ {p | 0 < barDivisible w R p.1 p.2})
    {K : Set (ℝ × (Fin d → ℝ))}
    (hK : Function.support (parabolicTimeTest ψ R) ⊆ K ∧
      Function.support (parabolicSpaceTest ψ R) ⊆ K)
    (hstrip : ∀ p : ℝ × (Fin d → ℝ), p.1 ∉ Ico 0 ((⌈T * R ^ 2⌉₊ : ℝ) / R ^ 2) →
      parabolicTimeTest ψ R p = 0 ∧ parabolicSpaceTest ψ R p = 0) :
    -(∫ p in K, barDivisible w R p.1 p.2 * parabolicTimeTest ψ R p) =
      (∫ p in K, barDivisible w R p.1 p.2 * parabolicSpaceTest ψ R p) +
        scenePair w R (sampledTimeIntegral ψ T R) := by
  have he := barDivisible_tested_parabolic_integral w hψ T hR hzero hfinal hpos
  have hKt : (∫ p in K, barDivisible w R p.1 p.2 * parabolicTimeTest ψ R p) =
      ∫ p, barDivisible w R p.1 p.2 * parabolicTimeTest ψ R p :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => by
      rw [show parabolicTimeTest ψ R p = 0 by by_contra hn; exact hp (hK.1 hn), mul_zero]
  have hKx : (∫ p in K, barDivisible w R p.1 p.2 * parabolicSpaceTest ψ R p) =
      ∫ p, barDivisible w R p.1 p.2 * parabolicSpaceTest ψ R p :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => by
      rw [show parabolicSpaceTest ψ R p = 0 by by_contra hn; exact hp (hK.2 hn), mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by rw [(hstrip p hp).1, mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by rw [(hstrip p hp).2, mul_zero])] at he
  rwa [hKt, hKx]

/-- Uniform coefficient consistency gives a pathwise residual bound on a fixed positive compact. -/
theorem eventually_abs_discreteResidual_le (hd : 1 ≤ d)
    {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ)
    {a B T : ℝ} (ha : 0 < a) (hT : 0 < T)
    (hlow : ∀ s x, s < 2 * a → ψ (s, x) = 0)
    (hhigh : ∀ s x, T ≤ s → ψ (s, x) = 0)
    (hb : ∀ s x, ψ (s, x) ≠ 0 → ‖x‖ ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ w : Data d,
      tsupport ψ ⊆ {p | 0 < barDivisible w R p.1 p.2} →
      |(∫ p in Icc a (T + 1) ×ˢ Metric.closedBall 0 (B + 2),
          barDivisible w R p.1 p.2 * spaceTimeResidualTest ψ p) -
        scenePair w R (sampledTimeIntegral ψ T R)| ≤
        ε * ∫ p in Icc a (T + 1) ×ˢ Metric.closedBall 0 (B + 2), barDivisible w R p.1 p.2 := by
  let K : Set (ℝ × (Fin d → ℝ)) := Icc a (T + 1) ×ˢ Metric.closedBall 0 (B + 2)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  haveI : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top (μ := volume)⟩
  have hKt : ∀ p ∈ K, 0 ≤ p.1 := fun p hp => ha.le.trans hp.1.1
  have htm := (Generic.TimeTest.contDiff_timeDeriv hψ.1).continuous
  have hxm := (contDiff_spaceTime_contOp hψ.1).continuous
  obtain ⟨Mt, hMt⟩ := hK.exists_bound_of_continuousOn htm.continuousOn
  obtain ⟨Mx, hMx⟩ := hK.exists_bound_of_continuousOn hxm.continuousOn
  have ht : Tendsto (fun R : ℝ => 1 / R ^ 2) atTop (𝓝 0) := by
    simpa only [one_div_pow, zero_pow (by norm_num : 2 ≠ 0)] using
      (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun R : ℝ => 1 / R) atTop (𝓝 0)).pow 2
  filter_upwards [eventually_ge_atTop (1 : ℝ), (tendsto_order.mp ht).2 a ha,
    eventually_parabolicTimeTest_error_le hψ (half_pos hε),
    eventually_parabolicSpaceTest_error_le hd hψ (half_pos hε)] with R hR hmesh hterr hxerr w hpos
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have hu := exists_bound_spaceTime_barDivisible hd w hRpos.le hK
  have htimeBound : ∀ p ∈ K, |parabolicTimeTest ψ R p| ≤ ε / 2 + Mt := by
    intro p hp
    have ht0 := hterr p (hKt p hp)
    have := abs_sub_le (parabolicTimeTest ψ R p) (Generic.TimeTest.timeDeriv ψ p) 0
    simpa only [sub_zero] using this.trans (add_le_add ht0 (by simpa using hMt p hp))
  have hspaceBound : ∀ p ∈ K, |parabolicSpaceTest ψ R p| ≤ ε / 2 + Mx := by
    intro p hp
    have := abs_sub_le (parabolicSpaceTest ψ R p) (contOp d (fun x => ψ (p.1, x)) p.2) 0
    simpa only [sub_zero] using this.trans (add_le_add (hxerr p (hKt p hp)) (by simpa using hMx p hp))
  have hIt := Generic.CompactPairing.integrableOn_mul (μ := volume) hK.measurableSet
    (measurable_spaceTime_barDivisible w R) (measurable_parabolicTimeTest ψ R) hu.choose_spec htimeBound
  have hIx := Generic.CompactPairing.integrableOn_mul (μ := volume) hK.measurableSet
    (measurable_spaceTime_barDivisible w R) (measurable_parabolicSpaceTest ψ R) hu.choose_spec hspaceBound
  obtain ⟨Mc, hMc⟩ := hK.exists_bound_of_continuousOn (continuous_spaceTimeResidualTest hψ).continuousOn
  have hIc := Generic.CompactPairing.integrableOn_mul (μ := volume) hK.measurableSet
    (measurable_spaceTime_barDivisible w R) (continuous_spaceTimeResidualTest hψ).measurable hu.choose_spec hMc
  have hf : ∀ x, ψ (((⌈T * R ^ 2⌉₊ : ℝ) / R ^ 2), x) = 0 := fun x =>
    hhigh _ x ((le_div_iff₀ (sq_pos_of_pos hRpos)).mpr (Nat.le_ceil _))
  have heq := barDivisible_tested_compact w hψ T hR (fun x => hlow 0 x (by linarith)) hf hpos
    (parabolicTests_support_subset ha hT hR hmesh hlow hhigh hb)
    (fun p hp => parabolicTests_eq_zero_outside_strip ha hT hR hmesh hlow hhigh hp)
  let c : ℝ × (Fin d → ℝ) → ℝ := fun p => spaceTimeResidualTest ψ p +
    parabolicTimeTest ψ R p + parabolicSpaceTest ψ R p
  have hcid : (∫ p in K, barDivisible w R p.1 p.2 * c p) =
      (∫ p in K, barDivisible w R p.1 p.2 * spaceTimeResidualTest ψ p) -
        scenePair w R (sampledTimeIntegral ψ T R) := by
    simp only [c, mul_add]
    have hIct : IntegrableOn (fun p => barDivisible w R p.1 p.2 * spaceTimeResidualTest ψ p +
        barDivisible w R p.1 p.2 * parabolicTimeTest ψ R p) K := hIc.add hIt
    rw [integral_add hIct hIx, integral_add hIc hIt]
    linarith [heq]
  change |(∫ p in K, _) - _| ≤ ε * ∫ p in K, _
  rw [← hcid]
  apply Generic.CompactPairing.abs_integral_mul_le_mass hK.measurableSet
    (integrableOn_spaceTime_barDivisible hd w hRpos.le hK)
    (fun p _ => barDivisible_nonneg w hRpos.le _ _)
  intro p hp
  have htc := hterr p (hKt p hp)
  rw [deriv_timeSlice (hψ.1.differentiable (by simp))] at htc
  have he : c p = (parabolicTimeTest ψ R p - timeDeriv ψ p) +
      (parabolicSpaceTest ψ R p - contOp d (fun x => ψ (p.1, x)) p.2) := by
    unfold c spaceTimeResidualTest
    ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith [hxerr p (hKt p hp)])

end Parking
