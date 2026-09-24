/-
Nonnegative expectations of initial discrepancy labels and opposite pairs.
Distinct resampling sites are independent; each sign has half the mean
absolute change, giving the required half-square pair mean.
-/
import Parking.Support.CancellationCount
import Parking.Support.CouplingTarget
import Parking.Support.ConfMoments

noncomputable section

open MeasureTheory LatticeProb
open scoped ENNReal

variable {d : ℕ}

/-- Initial opposite-pair counts are the two products of signed parts. -/
theorem Parking.discrepancyOppositePairs_eq (c : Site d → ℤ × ℤ) (z : Site d) :
    (Parking.discrepancyOppositePairs c z : ℝ) =
      Parking.dPos c z * Parking.dNeg c 0 + Parking.dNeg c z * Parking.dPos c 0 := by
  have hc : ∀ x, ((Parking.discrepancyConf c x).toNat : ℝ) =
      |((c x).2 : ℝ) - ((c x).1 : ℝ)| := by
    intro x
    rw [Parking.toNat_cast_eq_max]
    simp only [Parking.discrepancyConf, Int.cast_abs, Int.cast_sub]
    exact max_eq_left (abs_nonneg _)
  unfold Parking.discrepancyOppositePairs Parking.discrepancySign
  by_cases hz : 0 < (c z).2 - (c z).1 <;> by_cases h0 : 0 < (c 0).2 - (c 0).1
  · have hzr : (0 : ℝ) < ((c z).2 : ℝ) - (c z).1 := by exact_mod_cast hz
    have h0r : (0 : ℝ) < ((c 0).2 : ℝ) - (c 0).1 := by exact_mod_cast h0
    simp only [hz, h0, decide_true, if_true, Nat.cast_zero, Parking.dPos, Parking.dNeg,
      max_eq_right (by linarith : ((c z).1 : ℝ) - (c z).2 ≤ 0),
      max_eq_right (by linarith : ((c 0).1 : ℝ) - (c 0).2 ≤ 0), mul_zero, zero_mul, add_zero]
  · have hzr : (0 : ℝ) < ((c z).2 : ℝ) - (c z).1 := by exact_mod_cast hz
    have h0r : ((c 0).2 : ℝ) - (c 0).1 ≤ 0 := by exact_mod_cast le_of_not_gt h0
    simp only [hz, h0, decide_true, decide_false, Bool.true_eq_false, if_false, Nat.cast_mul, hc,
      abs_of_pos hzr, abs_of_nonpos h0r, Parking.dPos, Parking.dNeg,
      max_eq_left (le_of_lt hzr), max_eq_right h0r,
      max_eq_right (by linarith : ((c z).1 : ℝ) - (c z).2 ≤ 0),
      max_eq_left (by linarith : 0 ≤ ((c 0).1 : ℝ) - (c 0).2), zero_mul, add_zero]
    ring
  · have hzr : ((c z).2 : ℝ) - (c z).1 ≤ 0 := by exact_mod_cast le_of_not_gt hz
    have h0r : (0 : ℝ) < ((c 0).2 : ℝ) - (c 0).1 := by exact_mod_cast h0
    simp only [hz, h0, decide_true, decide_false, Bool.false_eq_true, if_false, Nat.cast_mul, hc,
      abs_of_nonpos hzr, abs_of_pos h0r, Parking.dPos, Parking.dNeg,
      max_eq_right hzr, max_eq_left (le_of_lt h0r),
      max_eq_left (by linarith : 0 ≤ ((c z).1 : ℝ) - (c z).2),
      max_eq_right (by linarith : ((c 0).1 : ℝ) - (c 0).2 ≤ 0), zero_mul, zero_add]
    ring
  · have hzr : ((c z).2 : ℝ) - (c z).1 ≤ 0 := by exact_mod_cast le_of_not_gt hz
    have h0r : ((c 0).2 : ℝ) - (c 0).1 ≤ 0 := by exact_mod_cast le_of_not_gt h0
    simp only [hz, h0, decide_false, if_true, Nat.cast_zero, Parking.dPos, Parking.dNeg,
      max_eq_right hzr, max_eq_right h0r, mul_zero, zero_mul, add_zero]

/-- A positive-part label count has the prescribed mean under the one-site law. -/
theorem Parking.lintegral_posNat_resampleOne (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {p : ℝ≥0∞} (hp : p ≤ 1)
    (hint : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (ν.prod ν)) :
    ∫⁻ q : ℤ × ℤ, (((q.2 - q.1).toNat : ℕ) : ℝ≥0∞) ∂(Parking.resampleOne ν p) =
      ENNReal.ofReal (p.toReal * Parking.gammaOf ν / 2) := by
  have hm : Measurable fun q : ℤ × ℤ => max ((q.2 : ℝ) - q.1) 0 := by fun_prop
  have hi : Integrable (fun q : ℤ × ℤ => max ((q.2 : ℝ) - q.1) 0) (Parking.resampleOne ν p) := by
    apply (Parking.integrable_absDiff_resampleOne ν hp hint).mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro q
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun q => le_max_right (((q.2 : ℝ) - q.1)) 0)
  rw [Parking.integral_posPart_resampleOne ν hp hint] at he
  rw [he]
  apply lintegral_congr
  intro q
  rw [← Int.cast_sub, ← Parking.toNat_cast_eq_max, ENNReal.ofReal_natCast]

/-- The negative-part label count has the same mean by symmetry. -/
theorem Parking.lintegral_negNat_resampleOne (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {p : ℝ≥0∞} (hp : p ≤ 1)
    (hint : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (ν.prod ν)) :
    ∫⁻ q : ℤ × ℤ, (((q.1 - q.2).toNat : ℕ) : ℝ≥0∞) ∂(Parking.resampleOne ν p) =
      ENNReal.ofReal (p.toReal * Parking.gammaOf ν / 2) := by
  have hm : Measurable fun q : ℤ × ℤ => (((q.2 - q.1).toNat : ℕ) : ℝ≥0∞) := measurable_of_countable _
  have he := lintegral_map (μ := Parking.resampleOne ν p) hm measurable_swap
  rw [Parking.resampleOne_map_swap] at he
  exact he.symm.trans (Parking.lintegral_posNat_resampleOne ν hp hint)

/-- The same opposite-pair identity in natural-number counts. -/
theorem Parking.discrepancyOppositePairs_nat (c : Site d → ℤ × ℤ) (z : Site d) :
    Parking.discrepancyOppositePairs c z =
      ((c z).2 - (c z).1).toNat * ((c 0).1 - (c 0).2).toNat +
        ((c z).1 - (c z).2).toNat * ((c 0).2 - (c 0).1).toNat := by
  apply Nat.cast_injective (R := ℝ)
  rw [Parking.discrepancyOppositePairs_eq]
  simp only [Nat.cast_add, Nat.cast_mul, Parking.toNat_cast_eq_max, Int.cast_sub,
    Parking.dPos, Parking.dNeg]

/-- Nonnegative products at distinct resampling sites factorize. -/
theorem Parking.lintegral_resample_pair (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {p : ℝ≥0∞} (hp : p ≤ 1) (z : Site d) (hz : z ≠ 0)
    (f g : ℤ × ℤ → ℝ≥0∞) :
    ∫⁻ c, f (c z) * g (c 0) ∂(Parking.resampleLaw d ν p) =
      (∫⁻ q, f q ∂(Parking.resampleOne ν p)) * ∫⁻ q, g q ∂(Parking.resampleOne ν p) := by
  haveI := Parking.resampleOne_isProbability ν hp
  have hmap : (Parking.resampleLaw d ν p).map (fun c => (c z, c 0)) =
      (Parking.resampleOne ν p).prod (Parking.resampleOne ν p) :=
    Measure.infinitePi_map_eval_prod hz
  have h := lintegral_map (μ := Parking.resampleLaw d ν p)
    (f := fun q : (ℤ × ℤ) × (ℤ × ℤ) => f q.1 * g q.2)
    (((measurable_of_countable f).comp measurable_fst).mul
      ((measurable_of_countable g).comp measurable_snd))
    ((measurable_pi_apply z).prodMk (measurable_pi_apply (0 : Site d)))
  rw [hmap] at h
  rw [← h]
  exact lintegral_prod_mul (measurable_of_countable f).aemeasurable
    (measurable_of_countable g).aemeasurable

/-- The mean number of opposite initial pairs across distinct sites is
one half the square of the mean number of labels created at a site. -/
theorem Parking.lintegral_discrepancyOppositePairs (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {p : ℝ≥0∞} (hp : p ≤ 1)
    (hint : Integrable (fun q : ℤ × ℤ => |(q.2 : ℝ) - (q.1 : ℝ)|) (ν.prod ν))
    (z : Site d) (hz : z ≠ 0) :
    ∫⁻ c, (Parking.discrepancyOppositePairs c z : ℝ≥0∞) ∂(Parking.resampleLaw d ν p) =
      ENNReal.ofReal ((p.toReal * Parking.gammaOf ν) ^ 2 / 2) := by
  have hγ : 0 ≤ Parking.gammaOf ν := integral_nonneg fun _ => abs_nonneg _
  have he : 0 ≤ p.toReal * Parking.gammaOf ν / 2 := by positivity
  simp_rw [Parking.discrepancyOppositePairs_nat, Nat.cast_add, Nat.cast_mul]
  rw [lintegral_add_left (by fun_prop),
    Parking.lintegral_resample_pair ν hp z hz
      (fun q => ((q.2 - q.1).toNat : ℝ≥0∞)) (fun q => ((q.1 - q.2).toNat : ℝ≥0∞)),
    Parking.lintegral_resample_pair ν hp z hz
      (fun q => ((q.1 - q.2).toNat : ℝ≥0∞)) (fun q => ((q.2 - q.1).toNat : ℝ≥0∞)),
    Parking.lintegral_posNat_resampleOne ν hp hint, Parking.lintegral_negNat_resampleOne ν hp hint,
    ← ENNReal.ofReal_mul he, ← ENNReal.ofReal_add (mul_nonneg he he) (mul_nonneg he he)]
  congr 1
  ring

end
