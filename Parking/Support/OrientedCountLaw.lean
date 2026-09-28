import Parking.Support.OrientedOdometerMeasurable
import Parking.Support.OrientedMoments
import Parking.Support.UpperTarget

/-!
# Marginal identities for the directed count law

Marginal identities for the directed count recursion under the particle law.
-/

open LatticeProb (measurable_from_countable')

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Pushing `orientedLaw d ν` forward under `ω ↦ (ω.1, ω.2.1)`, which discards the rank
component of `Data d`, gives the product law `(iidLaw d ν).prod (orientedStackLaw d)`. -/
theorem orientedLaw_map_confStack (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    (orientedLaw d ν).map (fun ω : Data d => (ω.1, ω.2.1)) =
      (iidLaw d ν).prod (orientedStackLaw d) := by
  haveI := orientedStackLaw_isProbability hd
  haveI := LatticeProb.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  change ((iidLaw d ν).prod ((orientedStackLaw d).prod (rankLaw d))).map (Prod.map id Prod.fst) = _
  rw [← Measure.map_prod_map _ _ measurable_id measurable_fst,
    Measure.map_id, Measure.map_fst_prod]
  simp

/-- Change of variables under `orientedLaw_map_confStack`: the `orientedLaw d ν` integral
of a measurable `F (ω.1, ω.2.1)` equals the integral of `F` against the product law
`(iidLaw d ν).prod (orientedStackLaw d)`. -/
theorem integral_oriented_confStack (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {F : (Site d → ℤ) × (Site d × ℕ → Site d) → ℝ} (hF : Measurable F) :
    (∫ ω : Data d, F (ω.1, ω.2.1) ∂(orientedLaw d ν)) =
      ∫ z, F z ∂((iidLaw d ν).prod (orientedStackLaw d)) := by
  have h := integral_map (μ := orientedLaw d ν) (φ := fun ω : Data d => (ω.1, ω.2.1))
    (f := F) (by fun_prop) hF.aestronglyMeasurable
  rw [orientedLaw_map_confStack hd ν] at h
  exact h.symm

/-- The `orientedLaw d ν` expectation of the odometer count `U ω n x` does not depend on
the site `x`, and equals `meanU (orientedLaw d ν) n`, by translation invariance of
`orientedLaw` (`orientedLaw_map_shiftData`). -/
theorem integral_oriented_U_shift (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (n : ℕ) (x : Site d) :
    (∫ ω : Data d, (U ω n x : ℝ) ∂(orientedLaw d ν)) = meanU (orientedLaw d ν) n := by
  have hm : Measurable (fun ω : Data d => (U ω n x : ℝ)) :=
    (measurable_from_countable' fun m : ℕ => (m : ℝ)).comp (measurable_U n x)
  have h := integral_map (μ := orientedLaw d ν) (φ := shiftData (-x))
    (f := fun ω : Data d => (U ω n x : ℝ)) (measurable_shiftData _).aemeasurable
    hm.aestronglyMeasurable
  rw [orientedLaw_map_shiftData hd ν (-x)] at h
  simpa only [U_shiftData, add_neg_cancel, meanU] using h

/-- Under a `CriticalLaw` hypothesis on `ν`, the odometer count `U ω n x` is integrable
against `orientedLaw d ν`, obtained from `integrable_oriented_U_rpow` at exponent `r = 1`
using the exponential moment supplied by `hν.expMoment`. -/
theorem integrable_oriented_U (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (n : ℕ) (x : Site d) : Integrable (fun ω : Data d => (U ω n x : ℝ)) (orientedLaw d ν) := by
  haveI := hν.prob
  obtain ⟨θ, hθ, he⟩ := hν.expMoment
  simpa only [Real.rpow_one] using integrable_oriented_U_rpow hd ν hθ
    (integrable_expMax_of_expAbs hθ he) (r := 1) le_rfl n x

/-- The odometer `orientedOdometer z.1 z.2 n x` is integrable against the product law
`(iidLaw d ν).prod (orientedStackLaw d)`, transported from `integrable_oriented_U` through
the a.e. identification `orientedOdometer_ae_eq_U` and the marginal identity
`orientedLaw_map_confStack`. -/
theorem integrable_orientedOdometer_joint (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (n : ℕ) (x : Site d) :
    Integrable (fun z : (Site d → ℤ) × (Site d × ℕ → Site d) =>
      (orientedOdometer z.1 z.2 n x : ℝ)) ((iidLaw d ν).prod (orientedStackLaw d)) := by
  haveI := hν.prob
  have hm : Measurable (fun z : (Site d → ℤ) × (Site d × ℕ → Site d) =>
      (orientedOdometer z.1 z.2 n x : ℝ)) :=
    (measurable_from_countable' fun m : ℕ => (m : ℝ)).comp
      (measurable_orientedOdometer _ _ measurable_fst measurable_snd n x)
  rw [← orientedLaw_map_confStack hd ν]
  apply (integrable_map_measure hm.aestronglyMeasurable (by fun_prop)).mpr
  exact (integrable_oriented_U hd ν hν n x).congr
    ((orientedOdometer_ae_eq_U hd ν n x).mono fun ω hω => congrArg Nat.cast hω.symm)

/-- Averaging `orientedOdometer η σ n x` over the stack law `orientedStackLaw d` and then
over the configuration law `iidLaw d ν` gives `meanU (orientedLaw d ν) n`, by Fubini
(`integral_prod`) combined with `integral_oriented_confStack` and
`integral_oriented_U_shift`. -/
theorem integral_orientedOdometer_given_mean (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (n : ℕ) (x : Site d) :
    (∫ η : Site d → ℤ, ∫ σ : Site d × ℕ → Site d,
      (orientedOdometer η σ n x : ℝ) ∂(orientedStackLaw d) ∂(iidLaw d ν)) =
        meanU (orientedLaw d ν) n := by
  haveI := hν.prob
  haveI := orientedStackLaw_isProbability hd
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  rw [← integral_prod _ (integrable_orientedOdometer_joint hd ν hν n x)]
  rw [← integral_oriented_confStack hd ν (by
    exact (measurable_from_countable' fun m : ℕ => (m : ℝ)).comp
      (measurable_orientedOdometer _ _ measurable_fst measurable_snd n x))]
  rw [integral_congr_ae ((orientedOdometer_ae_eq_U hd ν n x).mono
    fun ω hω => congrArg Nat.cast hω)]
  exact integral_oriented_U_shift hd ν n x

end Parking
