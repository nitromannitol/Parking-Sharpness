/- Joint measurability and local integrability of the rescaled space-time field. -/
import Parking.Support.SpatWBarDivisibleJointMeasurable

open MeasureTheory

noncomputable section
namespace Parking
variable {d : ℕ}

/-- The time horizon and lattice site form a countable measurable index. -/
theorem measurable_uncurry_spaceTime_barDivisible (R : ℝ) :
    Measurable (fun p : Data d × (ℝ × (Fin d → ℝ)) =>
      barDivisible p.1 R p.2.1 p.2.2) := by
  have hn : Measurable (fun p : Data d × (ℝ × (Fin d → ℝ)) =>
      ⌊p.2.1 * R ^ 2⌋₊) :=
    Nat.measurable_floor.comp ((measurable_fst.comp measurable_snd).mul_const _)
  have hx : Measurable (fun p : Data d × (ℝ × (Fin d → ℝ)) =>
      latticePoint R p.2.2) :=
    measurable_pi_lambda _ fun i => Int.measurable_floor.comp
      (measurable_const.mul ((measurable_pi_apply i).comp
        (measurable_snd.comp measurable_snd)))
  exact (measurable_eval_var _ (hn.prodMk hx)
    (fun p (q : ℕ × Site d) => uOf p.1 q.1 q.2)
    (fun q => (measurable_uOf q.1 q.2).comp measurable_fst)).const_mul _

theorem measurable_spaceTime_barDivisible (w : Data d) (R : ℝ) :
    Measurable (fun p : ℝ × (Fin d → ℝ) => barDivisible w R p.1 p.2) :=
  (measurable_uncurry_spaceTime_barDivisible R).comp
    (measurable_const.prodMk measurable_id)

/-- Compact space-time sets see finitely many time horizons and lattice sites. -/
theorem exists_bound_spaceTime_barDivisible (hd : 1 ≤ d) (w : Data d)
    {R : ℝ} (hR : 0 ≤ R) {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K) :
    ∃ M : ℝ, ∀ p ∈ K, |barDivisible w R p.1 p.2| ≤ M := by
  obtain ⟨C, hC, hbound⟩ := exists_radius_of_isCompact K hK
  exact ⟨_, fun p hp => abs_barDivisible_le hd w hR hC
    (hbound p hp).1 (hbound p hp).2⟩

theorem integrableOn_spaceTime_barDivisible (hd : 1 ≤ d) (w : Data d)
    {R : ℝ} (hR : 0 ≤ R) {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K) :
    IntegrableOn (fun p => barDivisible w R p.1 p.2) K := by
  haveI : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top (μ := volume)⟩
  obtain ⟨M, hM⟩ := exists_bound_spaceTime_barDivisible hd w hR hK
  exact Integrable.of_bound
    (measurable_spaceTime_barDivisible w R).aestronglyMeasurable M
    ((ae_restrict_mem hK.measurableSet).mono fun p hp => hM p hp)

/-- Every compactly restricted space-time pairing is a measurable random variable. -/
theorem measurable_integral_spaceTime_barDivisible_mul (R : ℝ)
    (K : Set (ℝ × (Fin d → ℝ))) (g : ℝ × (Fin d → ℝ) → ℝ) (hg : Measurable g) :
    Measurable (fun w : Data d => ∫ p in K, barDivisible w R p.1 p.2 * g p) :=
  (((measurable_uncurry_spaceTime_barDivisible R).mul
    (hg.comp measurable_snd)).stronglyMeasurable.integral_prod_right').measurable

end Parking
