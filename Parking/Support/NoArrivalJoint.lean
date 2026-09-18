import Parking.Support.NoArrivalExponential
import Parking.Support.FlatNoise

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The whole no-arrival history is measurable in the initial field and all drivers. -/
theorem measurable_noArrivalFlag_of {Ω : Type*} [MeasurableSpace Ω] (hd : 1 ≤ d)
    (e : Ω → Site d → ℤ) (r : Ω → Label d × ℕ → ℝ) (s : Ω → RoundNoise d)
    (he : Measurable e) (hr : Measurable r) (hs : Measurable s) (t : ℕ) (x : Site d) :
    Measurable (fun ω => noArrivalFlag (e ω) (r ω) (s ω) t x) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have hm : Measurable (fun ω => (matchedArrivals (e ω) (r ω) (s ω) t x).card) := by
        simp_rw [card_matchedArrivals_eq_countArrivals]
        exact (measurable_from_countable' Finset.card).comp
          (measurable_countArrivals _ _ (measurable_matchedCount ⟨0, hd⟩ e r s he hr hs t)
            ((measurable_pi_apply t).comp hs) x)
      exact (measurable_from_countable' (fun q : Bool × ℕ => q.1 && decide (q.2 = 0))).comp (ih.prodMk hm)

theorem measurable_arrivalCompensator_of {Ω : Type*} [MeasurableSpace Ω] (hd : 1 ≤ d)
    (e : Ω → Site d → ℤ) (r : Ω → Label d × ℕ → ℝ) (s : Ω → RoundNoise d)
    (he : Measurable e) (hr : Measurable r) (hs : Measurable s) (t : ℕ) (x : Site d) :
    Measurable (fun ω => arrivalCompensator (e ω) (r ω) (s ω) t x) := by
  have hS := measurableState_matchedState ⟨0, hd⟩ e r s he hr hs t
  simp only [arrivalCompensator, walkOp_eq_nbrFinset]
  exact (Finset.measurable_sum _ fun y _ =>
    (measurable_from_countable' fun n : ℕ => (n : ℝ)).comp (hS.2.2.2 y)).div_const _

theorem measurable_noArrivalWeight_of {Ω : Type*} [MeasurableSpace Ω] (hd : 1 ≤ d)
    (e : Ω → Site d → ℤ) (r : Ω → Label d × ℕ → ℝ) (s : Ω → RoundNoise d)
    (he : Measurable e) (hr : Measurable r) (hs : Measurable s) (t : ℕ) (x : Site d) :
    Measurable (fun ω => noArrivalWeight (e ω) (r ω) (s ω) t x) :=
  Measurable.ite ((measurable_noArrivalFlag_of hd e r s he hr hs t x) (measurableSet_singleton true))
    (measurable_arrivalCompensator_of hd e r s he hr hs t x).exp measurable_const

/-- Mixing bounded initial fields preserves the no-arrival exponential estimate. -/
theorem integral_noArrivalWeight_prod_le_one {Ω : Type} [MeasurableSpace Ω] (hd : 1 ≤ d)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Φ : Ω → Site d → ℤ) (hΦ : Measurable Φ)
    (K : ℕ) (hK : ∀ ω y, (Φ ω y).toNat ≤ K) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) :
    ∫ z, noArrivalWeight (Φ z.1) ρ (curryRoundNoise z.2) T x ∂(μ.prod (flatRoundNoiseLaw d)) ≤ 1 := by
  haveI := flatRoundNoiseLaw_isProbability hd
  have hm := measurable_noArrivalWeight_of hd (fun z : Ω × FlatRoundNoise d => Φ z.1)
    (fun _ => ρ) (fun z => curryRoundNoise z.2) (hΦ.comp measurable_fst) measurable_const
    (measurable_curryRoundNoise.comp measurable_snd) T x
  have hi : Integrable (fun z : Ω × FlatRoundNoise d => noArrivalWeight (Φ z.1) ρ (curryRoundNoise z.2) T x)
      (μ.prod (flatRoundNoiseLaw d)) :=
    Integrable.of_bound hm.aestronglyMeasurable _
      (ae_of_all _ fun z => noArrivalWeight_bound hd (Φ z.1) K (hK z.1) ρ (curryRoundNoise z.2) T x)
  rw [integral_prod _ hi]
  calc
    (∫ ω, ∫ ξ, noArrivalWeight (Φ ω) ρ (curryRoundNoise ξ) T x ∂(flatRoundNoiseLaw d) ∂μ) ≤
        ∫ _ω, (1 : ℝ) ∂μ := by
      apply integral_mono hi.integral_prod_left (integrable_const _)
      intro ω
      have he := integral_map (μ := flatRoundNoiseLaw d) measurable_curryRoundNoise.aemeasurable
        (f := fun σ => noArrivalWeight (Φ ω) ρ σ T x)
        (by rw [map_curryRoundNoise hd]; exact (measurable_noArrivalWeight hd (Φ ω) ρ T x).aestronglyMeasurable)
      rw [map_curryRoundNoise hd] at he
      change (∫ ξ, noArrivalWeight (Φ ω) ρ (curryRoundNoise ξ) T x ∂(flatRoundNoiseLaw d)) ≤ 1
      rw [← he]
      exact integral_noArrivalWeight_le_one hd (Φ ω) K (hK ω) ρ T x
    _ = 1 := by simp
end Parking
