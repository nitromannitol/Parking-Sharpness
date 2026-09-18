import Parking.Support.ClippedRoundLaw
import Parking.Support.Invariance

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The surviving-hole probability is independent of the target site. -/
theorem holeProb_at_site (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] (T : ℕ) (x : Site d) :
    ((law d ν) {ω | H ω T x = 1}).toReal = holeProb d ν T := by
  have h := congrArg (fun μ => μ {ω : Data d | H ω T 0 = 1}) (law_map_shiftData hd ν x)
  have hS : MeasurableSet {ω : Data d | H ω T 0 = 1} := (measurable_H T 0) (measurableSet_singleton 1)
  rw [Measure.map_apply (measurable_shiftData x) hS] at h
  have he : (shiftData x) ⁻¹' {ω : Data d | H ω T 0 = 1} = {ω : Data d | H ω T x = 1} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, H_shiftData, zero_add]
  rw [he] at h
  exact congrArg ENNReal.toReal h

/-- The bounded table hole probability equals the original hole probability. -/
theorem clippedRoundH_probability (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hclip : ∀ᵐ k ∂ν, clipSparse k = k) (T : ℕ) (x : Site d) :
    (((iidLaw d ν).prod (roundNoiseLaw d)) {ω | clippedRoundH T x ω = 1}).toReal = holeProb d ν T := by
  have hm : Measurable (fun O : CountHistory d => O.2.2 (T, x)) :=
    (measurable_pi_apply (T, x)).comp (measurable_snd.comp measurable_snd)
  have h := measure_clippedRoundHistory hd ν hclip {O | O.2.2 (T, x) = 1} (hm (measurableSet_singleton 1))
  have h' := congrArg ENNReal.toReal h
  exact h'.trans (holeProb_at_site hd ν T x)

/-- The table construction preserves the joint two-hole event. -/
theorem clippedRoundH_pair_probability (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hclip : ∀ᵐ k ∂ν, clipSparse k = k) (T : ℕ) (x z : Site d) :
    (((iidLaw d ν).prod (roundNoiseLaw d)) {ω | clippedRoundH T x ω = 1 ∧ clippedRoundH T z ω = 1}).toReal =
      ((law d ν) {ω | H ω T x = 1 ∧ H ω T z = 1}).toReal := by
  have hm (v : Site d) : Measurable (fun O : CountHistory d => O.2.2 (T, v)) :=
    (measurable_pi_apply (T, v)).comp (measurable_snd.comp measurable_snd)
  have h := measure_clippedRoundHistory hd ν hclip {O | O.2.2 (T, x) = 1 ∧ O.2.2 (T, z) = 1}
    ((hm x (measurableSet_singleton 1)).inter (hm z (measurableSet_singleton 1)))
  exact congrArg ENNReal.toReal h

/-- Since a clipped site has at most one hole, its real count is its survival indicator. -/
theorem clippedRoundH_eq_indicator (T : ℕ) (x : Site d) (ω : (Site d → ℤ) × RoundNoise d) :
    (clippedRoundH T x ω : ℝ) = {η | clippedRoundH T x η = 1}.indicator (fun _ => (1 : ℝ)) ω := by
  classical
  by_cases h : clippedRoundH T x ω = 1
  · simp [h]
  · have hz : clippedRoundH T x ω = 0 := by have := clippedRoundH_le_one T x ω; omega
    simp [hz]

/-- Averaging the conditional future hole mean gives h at every site. -/
theorem integral_clippedMeanH_eq_holeProb (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hclip : ∀ᵐ k ∂ν, clipSparse k = k) (T : ℕ) (x : Site d) :
    (∫ η, matchedMeanH (clippedField η) 0 T x ∂(iidLaw d ν)) = holeProb d ν T := by
  haveI := roundNoiseLaw_isProbability hd
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  let μ := (iidLaw d ν).prod (roundNoiseLaw d)
  have hi : Integrable (fun ω => (clippedRoundH T x ω : ℝ)) μ :=
    Integrable.of_bound ((measurable_from_countable' fun n : ℕ => (n : ℝ)).comp (measurable_clippedRoundH hd T x)).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast clippedRoundH_le_one T x ω)
  have he : (∫ η, matchedMeanH (clippedField η) 0 T x ∂(iidLaw d ν)) = ∫ ω, (clippedRoundH T x ω : ℝ) ∂μ :=
    (integral_prod _ hi).symm
  rw [he]
  simp_rw [clippedRoundH_eq_indicator]
  have hS : MeasurableSet {ω : (Site d → ℤ) × RoundNoise d | clippedRoundH T x ω = 1} :=
    (measurable_clippedRoundH hd T x) (measurableSet_singleton 1)
  rw [integral_indicator_const (1 : ℝ) hS]
  simp only [smul_eq_mul, mul_one]
  change (((iidLaw d ν).prod (roundNoiseLaw d)) {ω | clippedRoundH T x ω = 1}).toReal = holeProb d ν T
  exact clippedRoundH_probability hd ν hclip T x

/-- Every real moment of a table odometer equals the original moment. -/
theorem integral_clippedRoundU_rpow (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hclip : ∀ᵐ k ∂ν, clipSparse k = k) (T : ℕ) (x : Site d) (r : ℝ) :
    (∫ ω, clippedRoundU T x ω ^ r ∂((iidLaw d ν).prod (roundNoiseLaw d))) =
      ∫ ω, (U ω T x : ℝ) ^ r ∂(law d ν) := by
  have hm : Measurable (fun O : CountHistory d => (O.1 (T, x) : ℝ) ^ r) :=
    (measurable_from_countable' fun n : ℕ => (n : ℝ) ^ r).comp ((measurable_pi_apply (T, x)).comp measurable_fst)
  exact integral_clippedRoundHistory hd ν hclip _ hm
end Parking
