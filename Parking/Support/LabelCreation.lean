/-
The initial label mass has the expected absolute resampling size and splits
exactly into surviving and cancelled labels. Independent directions and
priorities disappear when integrating a function of the configurations.
-/
import Parking.Support.DiscrepancyTransport
import Parking.Support.OppositeMeans

noncomputable section

open MeasureTheory LatticeProb
open scoped ENNReal

variable {d : ℕ}

/-- Integrating a function of the two initial configurations removes the
independent priorities and direction tables. -/
theorem Parking.lintegral_coupled_conf (hd : 1 ≤ d) (ν : Measure ℤ)
    {p : ℝ≥0∞}
    (f : (Site d → ℤ × ℤ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ ω : Parking.CoupledData d, f ω.1.1 ∂(Parking.coupledLaw d ν p) =
      ∫⁻ c, f c ∂(Parking.resampleLaw d ν p) := by
  haveI := LatticeProb.rankLaw_isProbability d
  haveI := Parking.roundNoiseLaw_isProbability hd
  unfold Parking.coupledLaw
  rw [lintegral_prod (fun ω : Parking.CoupledData d => f ω.1.1)
    ((hf.comp measurable_fst).comp measurable_fst).aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [lintegral_prod (fun ω : (Site d → ℤ × ℤ) × (Label d × ℕ → ℝ) => f ω.1)
    (hf.comp measurable_fst).aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]

/-- The expected number of initial labels at the origin is the mean absolute resampling change. -/
theorem Parking.lintegral_discrepancyInitial (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1)
    (hint : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (ν.prod ν)) :
    ∫⁻ ω : Parking.CoupledData d, ((Parking.discrepancyConf ω.1.1 0).toNat : ℝ≥0∞)
      ∂(Parking.coupledLaw d ν p) = ENNReal.ofReal (p.toReal * Parking.gammaOf ν) := by
  let f : ℤ × ℤ → ℝ≥0∞ := fun q => (|(q.2 - q.1)|.toNat : ℝ≥0∞)
  have hf : Measurable f := measurable_of_countable f
  have heval := lintegral_map (μ := Parking.resampleLaw d ν p) hf (measurable_pi_apply (0 : Site d))
  rw [Parking.resampleLaw_map_eval ν hp] at heval
  have h := ofReal_integral_eq_lintegral_ofReal (Parking.integrable_absDiff_resampleOne ν hp hint)
    (Filter.Eventually.of_forall fun q : ℤ × ℤ => abs_nonneg ((q.2 : ℝ) - q.1))
  rw [Parking.integral_absDiff_resampleOne ν hp hint] at h
  calc ∫⁻ ω : Parking.CoupledData d, ((Parking.discrepancyConf ω.1.1 0).toNat : ℝ≥0∞)
        ∂(Parking.coupledLaw d ν p)
      = ∫⁻ c : Site d → ℤ × ℤ, f (c 0) ∂(Parking.resampleLaw d ν p) :=
        Parking.lintegral_coupled_conf hd ν _ (hf.comp (measurable_pi_apply (0 : Site d)))
    _ = ∫⁻ q, f q ∂(Parking.resampleOne ν p) := heval.symm
    _ = _ := by
      rw [h]
      apply lintegral_congr
      intro q
      change ((|(q.2 - q.1)|.toNat : ℕ) : ℝ≥0∞) = ENNReal.ofReal |(q.2 : ℝ) - q.1|
      rw [← ENNReal.ofReal_natCast]
      congr 1
      rw [Parking.toNat_cast_eq_max, Int.cast_abs, Int.cast_sub]
      exact max_eq_left (abs_nonneg _)

/-- Every initially created label is either alive or has disappeared. -/
theorem Parking.discrepancySurvivors_add_dead (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ) :
    Parking.discrepancySurvivors c ρ σ t 0 + (Parking.discrepancyDead c ρ σ t).card =
      (Parking.discrepancyConf c 0).toNat := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.range (Parking.discrepancyConf c 0).toNat)
    (p := fun i => (Parking.discrepancyState c ρ σ t).active (0, i) = true)
  simpa only [Parking.discrepancySurvivors, Parking.discrepancyDead, Bool.not_eq_true,
    Finset.card_range] using h

/-- The created-label mean splits into surviving and cancelled-label means. -/
theorem Parking.discrepancy_initial_mean_split (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1)
    (hint : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (ν.prod ν)) (t : ℕ) :
    ENNReal.ofReal (p.toReal * Parking.gammaOf ν) =
      (∫⁻ ω : Parking.CoupledData d, (Parking.discrepancySurvivors ω.1.1 ω.1.2 ω.2 t 0 : ℝ≥0∞)
        ∂(Parking.coupledLaw d ν p)) +
      ∫⁻ ω : Parking.CoupledData d, ((Parking.discrepancyDead ω.1.1 ω.1.2 ω.2 t).card : ℝ≥0∞)
        ∂(Parking.coupledLaw d ν p) := by
  have hmN : Measurable fun ω : Parking.CoupledData d => Parking.discrepancySurvivors ω.1.1 ω.1.2 ω.2 t 0 := by
    simp_rw [Parking.discrepancySurvivors_eq_sum_sentTo]
    exact Finset.measurable_sum _ fun b _ => Parking.measurable_discrepancySentTo hd t 0 b
  have hm : Measurable fun ω : Parking.CoupledData d =>
      (Parking.discrepancySurvivors ω.1.1 ω.1.2 ω.2 t 0 : ℝ≥0∞) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp hmN
  rw [← Parking.lintegral_discrepancyInitial hd ν hp hint, ← lintegral_add_left hm]
  apply lintegral_congr
  intro ω
  simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ℝ≥0∞))
    (Parking.discrepancySurvivors_add_dead ω.1.1 ω.1.2 ω.2 t).symm

end
