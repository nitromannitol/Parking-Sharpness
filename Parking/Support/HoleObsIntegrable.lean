/-
The integrability of the hole count of the range, the last hypothesis
`lem:product` puts on `Z` (`parking.tex:2321-2332`).

Hole counts never grow, so `Z` is at most the number of holes the initial
configuration puts on `R_t`, a finite sum of `(-\eta(x))^+`, and the first
moment of the count is what the setting of Section 9 assumes.  A functional of
the counts at finitely many sites has the same integrability under `restrictLaw`
and under the full product law, where the counts are the first of three
independent fields.
-/
import Parking.Support.HoleObsBound
import Parking.Support.SubcriticalMeasurable
import Parking.Support.CountFiltration
import Parking.Support.RestrictLaw

open MeasureTheory

noncomputable section

namespace Parking

variable {d : ℕ}

theorem integrable_negPart_coord {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (y : Site d) :
    Integrable (fun a : Site d → ℤ => (((-(a y)).toNat : ℕ) : ℝ)) (LatticeProb.iidLaw d ν) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  refine Integrable.mono' (integrable_coord hint y).abs ?_ ?_
  · exact ((measurable_from_top :
      Measurable fun k : ℤ => (((-k).toNat : ℕ) : ℝ)).comp
      (measurable_pi_apply y)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun a => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : ((-(a y)).toNat : ℤ) ≤ |a y| := by
      rcases lt_or_ge (a y) 0 with h | h
      · rw [Int.toNat_of_nonneg (by omega), abs_of_neg h]
      · rw [Int.toNat_eq_zero.mpr (by omega)]
        exact_mod_cast abs_nonneg (a y)
    have h2 : (((-(a y)).toNat : ℕ) : ℝ) ≤ ((|a y| : ℤ) : ℝ) := by exact_mod_cast h1
    rwa [Int.cast_abs] at h2

theorem integrable_pDataLaw_of_counts (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {G : (Site d → ℤ) → ℝ} (hG : Integrable G (LatticeProb.iidLaw d ν)) :
    Integrable (fun ω : PData d => G ω.1) (pDataLaw d ν) := by
  haveI := Parking.stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  have hmp : MeasurePreserving (Prod.fst : PData d → (Site d → ℤ))
      (pDataLaw d ν) (LatticeProb.iidLaw d ν) := by
    unfold pDataLaw
    exact measurePreserving_fst
  exact hmp.integrable_comp_of_integrable hG

/-- The holes the initial configuration puts on the range are integrable. -/
theorem integrable_initialHoles (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (w : ℕ → Fin d × Bool) (t : ℕ)
    {N : Finset (Site d)} (hN : rangeFinset (0 : Site d) w t ⊆ N) (ω₀ : PData d) :
    Integrable (fun ω : PData d =>
        ∑ x ∈ rangeFinset (0 : Site d) w t, (((-(ω.1 x)).toNat : ℕ) : ℝ))
      (restrictLaw d N ν ω₀) := by
  classical
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hmeas : Measurable fun ω : PData d =>
      ∑ x ∈ rangeFinset (0 : Site d) w t, (((-(ω.1 x)).toNat : ℕ) : ℝ) := by
    refine Finset.measurable_sum _ fun x _ => ?_
    exact (measurable_from_top : Measurable fun k : ℤ => (((-k).toNat : ℕ) : ℝ)).comp
      ((measurable_pi_apply x).comp measurable_fst)
  have hdep : DependsOn N (fun ω : PData d =>
      ∑ x ∈ rangeFinset (0 : Site d) w t, (((-(ω.1 x)).toNat : ℕ) : ℝ)) := by
    intro ω ω' hc _ _
    exact Finset.sum_congr rfl fun x hx => by rw [hc x (hN hx)]
  rw [integrable_restrictLaw_iff hdep hmeas]
  refine integrable_pDataLaw_of_counts (G := fun a : Site d → ℤ =>
    ∑ x ∈ rangeFinset (0 : Site d) w t, (((-(a x)).toNat : ℕ) : ℝ)) hd ?_
  exact integrable_finsetSum _ fun x _ => integrable_negPart_coord hint x

/-- **`Z` is integrable**, the last hypothesis of `lem:product` about it. -/
theorem integrable_holeObs (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (w : ℕ → Fin d × Bool) (t : ℕ)
    {N : Finset (Site d)} (hN : rangeFinset (0 : Site d) w t ⊆ N) (ω₀ : PData d) :
    Integrable (holeObs w t) (restrictLaw d N ν ω₀) := by
  refine Integrable.mono' (integrable_initialHoles hd hint w t hN ω₀)
    (measurable_holeObs w t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (holeObs_nonneg w t ω)]
  exact holeObs_le_initial w t ω

end Parking

end
