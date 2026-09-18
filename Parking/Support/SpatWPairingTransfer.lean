import Parking.Support.SpatWDivisiblePairing
import Parking.Support.NearestBallEvent
import Parking.Support.SpatialVanishingDistance
import Parking.Support.SpatWMiddleApproximation

open MeasureTheory LatticeProb Filter Topology

noncomputable section
namespace Parking

variable {d : ℕ}

/-- Local uniform comparison of the fields controls every compactly supported pairing. -/
theorem abs_pairing_barOdometer_sub_barDivisible_le (hd : 1 ≤ d) (w : Data d)
    {R : ℝ} (hR : 0 ≤ R) {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    {g : (Fin d → ℝ) → ℝ} (hg : Continuous g) (hsupp : Function.support g ⊆ K)
    {M ε : ℝ} (hM : ∀ x ∈ K, |g x| ≤ M)
    (hclose : ∀ x ∈ K, |barOdometer w R 1 x - barDivisible w R 1 x| ≤ ε) :
    |(∫ x, barOdometer w R 1 x * g x) - ∫ x, barDivisible w R 1 x * g x|
      ≤ ε * M * volume.real K := by
  have hKt : IsCompact (({(1 : ℝ)} : Set ℝ) ×ˢ K) := isCompact_singleton.prod hK
  obtain ⟨B, _, hbd, hbo⟩ := exists_bound_on_compact hd w hR _ hKt
  have hno : NiceOnK K (fun x => barOdometer w R 1 x) :=
    ⟨measurable_barOdometer_in_x w R 1, B, fun x hx => hbo (1, x) ⟨rfl, hx⟩⟩
  have hnd : NiceOnK K (fun x => barDivisible w R 1 x) :=
    ⟨measurable_barDivisible_in_x w R 1, B, fun x hx => hbd (1, x) ⟨rfl, hx⟩⟩
  have hiO := integrableOn_mul_of_niceOnK hK hg hno
  have hiD := integrableOn_mul_of_niceOnK hK hg hnd
  have heq : ∀ f : (Fin d → ℝ) → ℝ, (∫ x in K, f x * g x) = ∫ x, f x * g x := by
    intro f
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : g x = 0 := by by_contra hn; exact hx (hsupp hn)
    simp [hz]
  rw [← heq, ← heq, ← integral_sub hiO hiD]
  have hb : ∀ x ∈ K, ‖barOdometer w R 1 x * g x - barDivisible w R 1 x * g x‖ ≤ ε * M := by
    intro x hx
    rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
    exact mul_le_mul (hclose x hx) (hM x hx) (abs_nonneg _) ((abs_nonneg _).trans (hclose x hx))
  simpa only [Real.norm_eq_abs, mul_comm (volume.real K)] using
    norm_setIntegral_le_of_norm_le_const hK.measure_lt_top hb

/-- Compactly supported spatial pairings of the parking and divisible odometers
have a difference tending to zero in probability. -/
theorem tendsto_barOdometer_sub_barDivisible_pairing_zero (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : External.SandpileGrowth) (hBernstein : External.Bernstein)
    (hConcentration : External.UConcentration) (hGreenNorms : External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) {g : (Fin d → ℝ) → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => ((law d ν) {w | a <
      |(∫ x, barOdometer w R 1 x * g x) - ∫ x, barDivisible w R 1 x * g x|}).toReal)
      atTop (𝓝 0) := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  let K := tsupport g
  have hK : IsCompact K := hgs
  obtain ⟨M, hM, hb⟩ := exists_bound_h_on_K hK hg
  let C := M * volume.real K + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have htail := exists_spatial_vanishing_distance hd hd3 hGrowth hBernstein
    hConcentration hGreenNorms ν hν (({(1 : ℝ)} : Set ℝ) ×ˢ K)
    (isCompact_singleton.prod hK) (fun p hp => by simpa only [Set.mem_singleton_iff.mp hp.1] using zero_lt_one)
    (a / C) (div_pos ha hC)
  apply squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) _ htail
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro w hw
  by_contra hn
  have hclose : ∀ x ∈ K, |barOdometer w R 1 x - barDivisible w R 1 x| ≤ a / C :=
    fun x hx => abs_barOdometer_sub_barDivisible_le hd w hR
      (({(1 : ℝ)} : Set ℝ) ×ˢ K)
      (isCompact_singleton.prod hK) (ε := a / C) hn (p := (1, x)) ⟨rfl, hx⟩
  have hbound := abs_pairing_barOdometer_sub_barDivisible_le hd w hR hK hg
    (subset_tsupport g) hb hclose
  have he : a / C * M * volume.real K ≤ a := by
    rw [mul_assoc, div_mul_eq_mul_div, div_le_iff₀ hC]
    dsimp [C]
    nlinarith
  exact not_lt_of_ge (hbound.trans he) hw


open Set

/-- Local uniform closeness transfers to integration against a continuous compactly supported test. -/
theorem tendsto_barOdometer_pairing_sub_barDivisible_pairing_zero
    (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : External.SandpileGrowth) (hBernstein : External.Bernstein)
    (hConcentration : External.UConcentration) (hGreenNorms : External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν)
    (t : ℝ) (ht : 0 < t) {g : (Fin d → ℝ) → ℝ} (hg : Continuous g)
    (hgs : HasCompactSupport g) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun R : ℝ => ((law d ν) {w | a < |(∫ x, barOdometer w R t x * g x) -
      ∫ x, barDivisible w R t x * g x|}).toReal) atTop (𝓝 0) := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  obtain ⟨B, hB, hb⟩ := exists_norm_bound_of_hasCompactSupport hgs
  let K := Metric.closedBall (0 : Fin d → ℝ) B
  have hK : IsCompact K := isCompact_closedBall _ _
  let K' := ({t} : Set ℝ) ×ˢ K
  have hK' : IsCompact K' := isCompact_singleton.prod hK
  have hpos : ∀ p ∈ K', 0 < p.1 := fun p hp => by
    have he : p.1 = t := hp.1
    rwa [he]
  let M := ∫ x in K, |g x|
  have hM : 0 ≤ M := integral_nonneg (fun x => abs_nonneg (g x))
  let δ := a / (M + 1)
  have hδ : 0 < δ := div_pos ha (by linarith)
  have hδM : δ * M < a := by
    have he : δ * (M + 1) = a := div_mul_cancel₀ _ (by linarith)
    nlinarith
  have hv := exists_spatial_vanishing_distance hd hd3 hGrowth hBernstein hConcentration
    hGreenNorms ν hν K' hK' hpos δ hδ
  have hzero : ∀ x ∉ K, g x = 0 := by
    intro x hx
    by_contra hne
    apply hx
    simpa [K, Metric.mem_closedBall, dist_eq_norm] using hb x hne
  have hI : ∀ f : (Fin d → ℝ) → ℝ,
      (∫ x in K, f x * g x) = ∫ x, f x * g x := fun f =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hzero x hx, mul_zero]
  have hbound : ∀ᶠ R : ℝ in atTop,
      ((law d ν) {w | a < |(∫ x, barOdometer w R t x * g x) -
        ∫ x, barDivisible w R t x * g x|}).toReal ≤
      ((law d ν) {w | δ < ⨆ p ∈ K', |barOdometer w R p.1 p.2 - barDivisible w R p.1 p.2|}).toReal := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro w hw
    by_contra hbad
    have hpoint : ∀ x ∈ K, |barOdometer w R t x - barDivisible w R t x| ≤ δ :=
      fun x hx => abs_barOdometer_sub_barDivisible_le (p := (t, x)) hd w hR K' hK' hbad ⟨rfl, hx⟩
    have hu := integrableOn_barOdometer w (t := t) (B := B) hR
    obtain ⟨N, _hN, hNb⟩ := exists_norm_le_of_hasCompactSupport hg hgs
    have hiu : IntegrableOn (fun x => barOdometer w R t x * g x) K volume :=
      hu.mul_bdd hg.measurable.aestronglyMeasurable (ae_of_all _ hNb)
    have hiv : IntegrableOn (fun x => barDivisible w R t x * g x) K volume :=
      integrableOn_mul_of_niceOnK hK hg (niceOnK_barDivisible hd w R t B hR ht.le)
    have hweight : IntegrableOn g K volume := hg.continuousOn.integrableOn_compact hK
    have he := Generic.WeightedIntegral.abs_pairing_sub_le hweight
      (by simpa only [mul_comm, IntegrableOn] using hiu) (by simpa only [mul_comm, IntegrableOn] using hiv)
      (by filter_upwards [ae_restrict_mem hK.measurableSet] with x hx; exact hpoint x hx)
    have he' : |(∫ x in K, barOdometer w R t x * g x) - ∫ x in K, barDivisible w R t x * g x| ≤ δ * M := by
      simpa only [mul_comm] using he
    rw [hI, hI] at he'
    exact (not_lt_of_ge (he'.trans hδM.le)) hw
  exact squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hbound hv

end Parking
end
