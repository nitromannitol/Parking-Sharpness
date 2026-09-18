/-
The first inequality of Step 1 of `thm:subcritical` (`parking.tex:2453-2458`):
the mean number of unfilled holes of the range at time `t` is at least
`δ(λ)|R_t|`.

The mean at a single site is the same at every site and at least `-E η(0)`
(`Support/SubcriticalHoleMean.lean`), for the stack construction; the two
constructions have the same law (`Support/HoleLawTransfer.lean`), so the same
holds for the hole counts the observable `Z` reads; and `Z` is the sum of `|R_t|`
of them.
-/
import Parking.Support.HoleLawTransfer
import Parking.Support.SubcriticalHoleMean
import Parking.Support.HoleObsIntegrable

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- The hole count at a site is a measurable function of the particle-driven
data, jointly with the configuration. -/
theorem measurable_conf_pHoleCount (n : ℕ) (x : Site d) :
    Measurable fun ω : PData d =>
      ((ω.1, pHoleCount (toPDriver ω) n x) : (Site d → ℤ) × ℕ) :=
  measurable_fst.prodMk
    ((measurableState_pState (fun ω : PData d => ω.1) (fun ω => ω.2.1) (fun ω => ω.2.2)
      measurable_fst (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_snd) n).2.2.1 x)

/-- The mean hole count at a site is the same in both constructions. -/
theorem integral_pHoleCount_eq (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (n : ℕ) (x : Site d) :
    ∫ ω, (pHoleCount (toPDriver ω) n x : ℝ) ∂(pDataLaw d ν)
      = ∫ ω, (Parking.H ω n x : ℝ) ∂(law d ν) := by
  have hf : Measurable fun z : (Site d → ℤ) × ℕ => ((z.2 : ℕ) : ℝ) :=
    (measurable_from_countable' fun k : ℕ => (k : ℝ)).comp measurable_snd
  have h1 : ∫ ω, (pHoleCount (toPDriver ω) n x : ℝ) ∂(pDataLaw d ν)
      = ∫ z, ((z.2 : ℕ) : ℝ)
        ∂((pDataLaw d ν).map fun ω : PData d =>
          ((ω.1, pHoleCount (toPDriver ω) n x) : (Site d → ℤ) × ℕ)) :=
    (integral_map (measurable_conf_pHoleCount n x).aemeasurable
      hf.aestronglyMeasurable).symm
  have h2 : ∫ ω, (Parking.H ω n x : ℝ) ∂(law d ν)
      = ∫ z, ((z.2 : ℕ) : ℝ)
        ∂((law d ν).map fun ω : Data d => ((ω.1, Parking.H ω n x) : (Site d → ℤ) × ℕ)) :=
    (integral_map (measurable_fst.prodMk (measurable_H n x)).aemeasurable
      hf.aestronglyMeasurable).symm
  rw [h1, h2, map_conf_pHoleCount hd ν n x]

/-- The mean of the configuration at one site is the mean of the one-site law. -/
theorem integral_eta_iidLaw (d : ℕ) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    ∫ η, ((η (0 : Site d) : ℤ) : ℝ) ∂(iidLaw d ν) = ∫ k, (k : ℝ) ∂ν := by
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  have hmap : (iidLaw d ν).map (fun η : Site d → ℤ => η 0) = ν :=
    Measure.infinitePi_map_eval _ 0
  have h := integral_map (μ := iidLaw d ν) (φ := fun η : Site d → ℤ => η 0)
    (f := fun k : ℤ => (k : ℝ)) (measurable_pi_apply (0 : Site d)).aemeasurable
    ((measurable_from_countable' fun k : ℤ => (k : ℝ)).aestronglyMeasurable)
  rw [hmap] at h
  exact h.symm

/-- **The mean hole count at a site is at least the drift.** -/
theorem neg_mean_le_integral_pHoleCount (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (t : ℕ) (x : Site d) :
    -∫ k, (k : ℝ) ∂ν ≤ ∫ ω, (pHoleCount (toPDriver ω) t x : ℝ) ∂(pDataLaw d ν) := by
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  have hi0 : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) (iidLaw d ν) := by
    have hmap : (iidLaw d ν).map (fun η : Site d → ℤ => η 0) = ν :=
      Measure.infinitePi_map_eval _ 0
    have hi : Integrable (fun k : ℤ => |(k : ℝ)|)
        ((iidLaw d ν).map (fun η : Site d → ℤ => η 0)) := by rw [hmap]; exact hint
    exact (integrable_map_measure (g := fun k : ℤ => |(k : ℝ)|)
      (f := fun η : Site d → ℤ => η 0) (μ := iidLaw d ν)
      (by rw [hmap]; exact hint.aestronglyMeasurable)
      (measurable_pi_apply (0 : Site d)).aemeasurable).mp hi
  have hti : TranslationInvariant (iidLaw d ν) := fun v => iidLaw_map_shiftConf' ν v
  have hlaw : law d ν = dataLaw d (iidLaw d ν) := rfl
  have hstack := neg_integral_eta_le_integral_H_site hd hti hi0 t x
  rw [← integral_eta_iidLaw d ν]
  rw [integral_pHoleCount_eq hd ν t x, hlaw]
  exact hstack

/-- The hole count at a site is integrable. -/
theorem integrable_pHoleCount (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (t : ℕ) (x : Site d) :
    Integrable (fun ω : PData d => (pHoleCount (toPDriver ω) t x : ℝ)) (pDataLaw d ν) := by
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  refine Integrable.mono'
    (integrable_pDataLaw_of_counts (G := fun a : Site d → ℤ => (((-(a x)).toNat : ℕ) : ℝ)) hd
      (integrable_negPart_coord hint x))
    (((measurable_from_countable' fun k : ℕ => (k : ℝ)).comp
      ((measurableState_pState (fun ω : PData d => ω.1) (fun ω => ω.2.1) (fun ω => ω.2.2)
        measurable_fst (measurable_fst.comp measurable_snd)
        (measurable_snd.comp measurable_snd) t).2.2.1 x)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h0 : pHoleCount (toPDriver ω) 0 x = (((-(ω.1 x)).toNat : ℕ)) := rfl
  have hle : pHoleCount (toPDriver ω) t x ≤ (((-(ω.1 x)).toNat : ℕ)) := by
    rw [← h0]
    exact pHoleCount_antitone (toPDriver ω) x (Nat.zero_le t)
  exact_mod_cast hle

/-- **The first inequality of Step 1**: the mean number of unfilled holes of the
range at time `t` is at least the drift times the size of the range. -/
theorem rangeCard_mul_le_integral_holeObs (hd : 1 ≤ d) {ν : Measure ℤ}
    [IsProbabilityMeasure ν] (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (w : ℕ → Fin d × Bool) (t : ℕ) :
    (rangeCard (0 : Site d) w t : ℝ) * (-∫ k, (k : ℝ) ∂ν)
      ≤ ∫ ω, holeObs w t ω ∂(pDataLaw d ν) := by
  classical
  have hsplit : ∫ ω, holeObs w t ω ∂(pDataLaw d ν)
      = ∑ x ∈ rangeFinset (0 : Site d) w t,
        ∫ ω, (pHoleCount (toPDriver ω) t x : ℝ) ∂(pDataLaw d ν) := by
    unfold holeObs
    exact integral_finsetSum _ fun x _ => integrable_pHoleCount hd hint t x
  rw [hsplit, rangeCard_eq_card]
  calc ((rangeFinset (0 : Site d) w t).card : ℝ) * (-∫ k, (k : ℝ) ∂ν)
      = (rangeFinset (0 : Site d) w t).card • (-∫ k, (k : ℝ) ∂ν) := (nsmul_eq_mul _ _).symm
    _ ≤ ∑ x ∈ rangeFinset (0 : Site d) w t,
          ∫ ω, (pHoleCount (toPDriver ω) t x : ℝ) ∂(pDataLaw d ν) :=
        Finset.card_nsmul_le_sum _ _ _ fun x _ =>
          neg_mean_le_integral_pHoleCount hd hint t x

end Parking

end
