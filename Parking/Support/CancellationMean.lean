/-
Averaging the conditional finite cancellation count over priorities and the
resampling law gives the half-square coefficient times the random-walk
hitting sum. All expectations are nonnegative Lebesgue integrals.
-/
import Parking.Support.OppositeMeans
import Parking.Support.DiscrepancyTransport

noncomputable section

open MeasureTheory LatticeProb
open scoped ENNReal

variable {d : ℕ}

theorem Parking.measurable_discrepancyOppositePairs (z : Site d) :
    Measurable fun c : Site d → ℤ × ℤ => (Parking.discrepancyOppositePairs c z : ℝ≥0∞) := by
  simp_rw [Parking.discrepancyOppositePairs_nat, Nat.cast_add, Nat.cast_mul]
  change Measurable fun c : Site d → ℤ × ℤ =>
    (fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      ((q.1.2 - q.1.1).toNat : ℝ≥0∞) * ((q.2.1 - q.2.2).toNat : ℝ≥0∞) +
      ((q.1.1 - q.1.2).toNat : ℝ≥0∞) * ((q.2.2 - q.2.1).toNat : ℝ≥0∞)) (c z, c 0)
  exact (measurable_of_countable (fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      ((q.1.2 - q.1.1).toNat : ℝ≥0∞) * ((q.2.1 - q.2.2).toNat : ℝ≥0∞) +
      ((q.1.1 - q.1.2).toNat : ℝ≥0∞) * ((q.2.2 - q.2.1).toNat : ℝ≥0∞))).comp
    ((measurable_pi_apply z).prodMk (measurable_pi_apply (0 : Site d)))

theorem Parking.measurable_discrepancyCancelledPairs_card (hd : 1 ≤ d) (T : ℕ) (z : Site d) :
    Measurable fun ω : Parking.CoupledData d =>
      ((Parking.discrepancyCancelledPairs ω.1.1 ω.1.2 ω.2 T z).card : ℝ≥0∞) :=
by
  have hm := Parking.measurable_discrepancyCancelledPairs (Ω := Parking.CoupledData d) ⟨0, hd⟩
    (fun ω : Parking.CoupledData d => ω.1.1) (fun ω : Parking.CoupledData d => ω.1.2) Prod.snd
    (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst) measurable_snd T z
  exact (measurable_of_countable (fun s : Finset (ℕ × ℕ) => (s.card : ℝ≥0∞))).comp hm

/-- Averaging the conditional cancellation count uses only the initial
opposite-pair mean. -/
theorem Parking.lintegral_discrepancyCancelledPairs_coupled (hd : 1 ≤ d)
    (ν : Measure ℤ) [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1)
    (hint : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (ν.prod ν))
    (T : ℕ) (z : Site d) (hz : z ≠ 0) :
    ∫⁻ ω : Parking.CoupledData d,
      ((Parking.discrepancyCancelledPairs ω.1.1 ω.1.2 ω.2 T z).card : ℝ≥0∞)
      ∂(Parking.coupledLaw d ν p) ≤
      ENNReal.ofReal ((p.toReal * Parking.gammaOf ν) ^ 2 / 2) *
        (Parking.walkLaw d) {r | ∃ s ≤ 2 * T, Parking.walkPath z r s = 0} := by
  haveI := Parking.resampleOne_isProbability ν hp
  haveI : IsProbabilityMeasure (Parking.resampleLaw d ν p) := by
    unfold Parking.resampleLaw LatticeProb.iidLaw
    infer_instance
  haveI := LatticeProb.rankLaw_isProbability d
  haveI := Parking.roundNoiseLaw_isProbability hd
  let h := (Parking.walkLaw d) {r | ∃ s ≤ 2 * T, Parking.walkPath z r s = 0}
  have hm := Parking.measurable_discrepancyOppositePairs z
  unfold Parking.coupledLaw
  rw [lintegral_prod _ (Parking.measurable_discrepancyCancelledPairs_card hd T z).aemeasurable]
  calc ∫⁻ ω, ∫⁻ σ, ((Parking.discrepancyCancelledPairs ω.1 ω.2 σ T z).card : ℝ≥0∞)
          ∂(Parking.roundNoiseLaw d) ∂((Parking.resampleLaw d ν p).prod (rankLaw d))
      ≤ ∫⁻ ω, (Parking.discrepancyOppositePairs ω.1 z : ℝ≥0∞) * h
          ∂((Parking.resampleLaw d ν p).prod (rankLaw d)) :=
        lintegral_mono fun ω => Parking.lintegral_discrepancyCancelledPairs_le hd ω.1 ω.2 T z hz
    _ = (∫⁻ c, (Parking.discrepancyOppositePairs c z : ℝ≥0∞) ∂(Parking.resampleLaw d ν p)) * h := by
      rw [lintegral_prod (fun ω : (Site d → ℤ × ℤ) × (Label d × ℕ → ℝ) =>
        (Parking.discrepancyOppositePairs ω.1 z : ℝ≥0∞) * h)
        ((hm.comp measurable_fst).mul_const h).aemeasurable]
      simp only [lintegral_const, measure_univ, mul_one]
      exact lintegral_mul_const h hm
    _ = _ := by rw [Parking.lintegral_discrepancyOppositePairs ν hp hint z hz]

/-- The expected number of lost origin labels is bounded by the full hitting sum. -/
theorem Parking.lintegral_discrepancyDead_le (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1)
    (hint : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (ν.prod ν)) (T : ℕ) :
    ∫⁻ ω : Parking.CoupledData d, ((Parking.discrepancyDead ω.1.1 ω.1.2 ω.2 T).card : ℝ≥0∞)
      ∂(Parking.coupledLaw d ν p) ≤
      ENNReal.ofReal ((p.toReal * Parking.gammaOf ν) ^ 2 / 2) * Parking.hitSum d (2 * T) := by
  classical
  let a := ENNReal.ofReal ((p.toReal * Parking.gammaOf ν) ^ 2 / 2)
  let f : Site d → ℝ≥0∞ := fun z =>
    if z = 0 then 0 else (Parking.walkLaw d) {r | ∃ s ≤ 2 * T, Parking.walkPath z r s = 0}
  have hterm : ∀ z : Site d, ∫⁻ ω : Parking.CoupledData d,
      ((Parking.discrepancyCancelledPairs ω.1.1 ω.1.2 ω.2 T z).card : ℝ≥0∞)
      ∂(Parking.coupledLaw d ν p) ≤ a * f z := by
    intro z
    by_cases hz : z = 0
    · subst z
      simp only [Parking.discrepancyCancelledPairs_zero, Finset.card_empty, Nat.cast_zero,
        lintegral_zero, f, if_true, mul_zero, le_refl]
    · exact (Parking.lintegral_discrepancyCancelledPairs_coupled hd ν hp hint T z hz).trans_eq
        (by simp only [f, if_neg hz, a])
  calc ∫⁻ ω : Parking.CoupledData d, ((Parking.discrepancyDead ω.1.1 ω.1.2 ω.2 T).card : ℝ≥0∞)
        ∂(Parking.coupledLaw d ν p)
      ≤ ∫⁻ ω : Parking.CoupledData d, ∑ z ∈ boxFinset (0 : Site d) (2 * T),
        ((Parking.discrepancyCancelledPairs ω.1.1 ω.1.2 ω.2 T z).card : ℝ≥0∞)
        ∂(Parking.coupledLaw d ν p) := lintegral_mono fun ω => by
          simpa only [Nat.cast_sum] using
            (Nat.cast_le (α := ℝ≥0∞)).mpr (Parking.card_discrepancyDead_le ω.1.1 ω.1.2 ω.2 T)
    _ = ∑ z ∈ boxFinset (0 : Site d) (2 * T), ∫⁻ ω : Parking.CoupledData d,
        ((Parking.discrepancyCancelledPairs ω.1.1 ω.1.2 ω.2 T z).card : ℝ≥0∞)
        ∂(Parking.coupledLaw d ν p) :=
      lintegral_finsetSum _ fun z _ => Parking.measurable_discrepancyCancelledPairs_card hd T z
    _ ≤ ∑ z ∈ boxFinset (0 : Site d) (2 * T), a * f z := Finset.sum_le_sum fun z _ => hterm z
    _ = a * ∑ z ∈ boxFinset (0 : Site d) (2 * T), f z := (Finset.mul_sum _ _ _).symm
    _ ≤ a * ∑' z, f z := mul_le_mul_right (ENNReal.sum_le_tsum (boxFinset (0 : Site d) (2 * T))) a
    _ = _ := rfl

end
