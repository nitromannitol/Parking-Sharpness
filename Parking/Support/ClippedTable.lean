import Parking.Support.TableLaw
import Parking.Support.SceneryLaw
import Parking.Support.FlatNoise
import Parking.Support.BoundedMoment

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Coordinatewise truncation to the support of the sparse law. -/
def clippedField (η : Site d → ℤ) : Site d → ℤ := fun y => clipSparse (η y)

theorem measurable_clippedField : Measurable (clippedField (d := d)) :=
  measurable_pi_lambda _ fun y => (measurable_from_countable' clipSparse).comp (measurable_pi_apply y)

theorem clippedField_particle_bound (η : Site d → ℤ) (y : Site d) :
    (clippedField η y).toNat ≤ 1 := by
  have h := (clipSparse_bounds (η y)).2
  change (clipSparse (η y)).toNat ≤ 1
  omega

theorem ae_clippedField (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hclip : ∀ᵐ k ∂ν, clipSparse k = k) :
    ∀ᵐ η ∂(iidLaw d ν), clippedField η = η := by
  have ha : ∀ᵐ η ∂(iidLaw d ν), ∀ y, clipSparse (η y) = η y :=
    ae_all_iff.mpr fun y =>
      (measurePreserving_eval_infinitePi (fun _ : Site d => ν) y).quasiMeasurePreserving.ae hclip
  exact ha.mono fun _ h => funext h

/-- Clipping and reshaping the independent instructions preserve the count law. -/
theorem measurePreserving_clippedTable (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hclip : ∀ᵐ k ∂ν, clipSparse k = k) :
    MeasurePreserving (fun ω : (Site d → ℤ) × FlatRoundNoise d => (clippedField ω.1, curryRoundNoise ω.2))
      ((iidLaw d ν).prod (flatRoundNoiseLaw d)) ((iidLaw d ν).prod (roundNoiseLaw d)) := by
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  haveI := flatRoundNoiseLaw_isProbability hd
  haveI := roundNoiseLaw_isProbability hd
  have hη : MeasurePreserving clippedField (iidLaw d ν) (iidLaw d ν) :=
    ⟨measurable_clippedField, (Measure.map_congr (ae_clippedField ν hclip)).trans (Measure.map_id)⟩
  exact hη.prod ⟨measurable_curryRoundNoise, map_curryRoundNoise hd⟩

/-- A bounded real odometer on the product of the scenery and the flattened table. -/
def clippedTableU (T : ℕ) (x : Site d) (ω : (Site d → ℤ) × FlatRoundNoise d) : ℝ :=
  ((matchedState (clippedField ω.1) 0 (curryRoundNoise ω.2) T).departures x : ℝ)

theorem clippedTableU_nonneg (T : ℕ) (x : Site d) (ω : (Site d → ℤ) × FlatRoundNoise d) :
    0 ≤ clippedTableU T x ω := Nat.cast_nonneg _

theorem measurable_clippedTableU (hd : 1 ≤ d) (T : ℕ) (x : Site d) :
    Measurable (clippedTableU T x) := by
  have h := measurableState_matchedState ⟨0, hd⟩
    (fun ω : (Site d → ℤ) × FlatRoundNoise d => clippedField ω.1) (fun _ => 0)
    (fun ω => curryRoundNoise ω.2) (measurable_clippedField.comp measurable_fst)
    measurable_const (measurable_curryRoundNoise.comp measurable_snd) T
  exact (measurable_from_countable' fun n : ℕ => (n : ℝ)).comp (h.2.2.2 x)

theorem clippedTableU_bound (T : ℕ) (x : Site d) (ω : (Site d → ℤ) × FlatRoundNoise d) :
    |clippedTableU T x ω| ≤ ((T * (2 * T + 1) ^ d : ℕ) : ℝ) := by
  rw [abs_of_nonneg (clippedTableU_nonneg T x ω)]
  have h := matchedOdometer_le_box (clippedField ω.1) 1 (clippedField_particle_bound ω.1) 0
    (curryRoundNoise ω.2) T x
  simp only [mul_one] at h
  exact Nat.cast_le.mpr h

/-- Every measurable function of the bounded table odometer has the original expectation. -/
theorem integral_clippedTableU (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hclip : ∀ᵐ k ∂ν, clipSparse k = k) (T : ℕ) (x : Site d)
    (φ : ℝ → ℝ) (hφ : Measurable φ) :
    ∫ ω, φ (clippedTableU T x ω) ∂((iidLaw d ν).prod (flatRoundNoiseLaw d)) =
      ∫ ω, φ (U ω T x : ℝ) ∂(law d ν) := by
  let Ψ : (Site d → ℤ) × FlatRoundNoise d → (Site d → ℤ) × RoundNoise d :=
    fun ω => (clippedField ω.1, curryRoundNoise ω.2)
  let f : (Site d → ℤ) × RoundNoise d → ℕ := fun ω => (matchedState ω.1 0 ω.2 T).departures x
  have hf : Measurable f :=
    (measurable_pi_apply (T, x)).comp (measurable_fst.comp (measurable_tableHistory hd))
  have hc : Measurable (fun n : ℕ => φ (n : ℝ)) :=
    hφ.comp (measurable_from_countable' fun n : ℕ => (n : ℝ))
  have hΨ := measurePreserving_clippedTable hd ν hclip
  have he : (∫ ω, φ (clippedTableU T x ω) ∂((iidLaw d ν).prod (flatRoundNoiseLaw d))) =
      ∫ ω, φ (f ω : ℝ) ∂((iidLaw d ν).prod (roundNoiseLaw d)) := by
    rw [← hΨ.map_eq]
    exact (integral_map hΨ.measurable.aemeasurable
      (show AEStronglyMeasurable (fun ω => φ (f ω : ℝ)) _ from (hc.comp hf).aestronglyMeasurable)).symm
  rw [he, ← integral_map hf.aemeasurable hc.aestronglyMeasurable, map_tableOdometer hd ν T x]
  exact integral_map (measurable_U T x).aemeasurable hc.aestronglyMeasurable
end Parking
