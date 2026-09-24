import Parking.Support.SceneryHole
import Parking.Support.PartialComparison

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The two-step relative scenery comparison survives every partial initial-field reveal. -/
theorem scenery_partial_hole_relative (hd : 3 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x v : Site d)
    (S : Set (Site d)) [DecidablePred (· ∈ S)] (η : Site d → ℤ) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ k : ℤ,
      escapePotential d x v ^ 2 * b ≤
        partialInt (fun _ : Site d => ν) (insert v S) (fun ζ => matchedMeanH (clippedField ζ) ρ T x)
          (Function.update η v k) ∧
      partialInt (fun _ : Site d => ν) (insert v S) (fun ζ => matchedMeanH (clippedField ζ) ρ T x)
          (Function.update η v k) ≤ b := by
  have hd1 : 1 ≤ d := by omega
  let F (k : ℤ) (ζ : Site d → ℤ) := matchedMeanH (clippedField (Function.update ζ v k)) ρ T x
  have hFm (k : ℤ) : Measurable (F k) := (measurable_matchedMeanH hd1 ρ T x).comp
    (measurable_clippedField.comp measurable_update_left)
  have hFb (k : ℤ) (ζ : Site d → ℤ) : |F k ζ| ≤ 1 := by
    rw [abs_of_nonneg (matchedMeanH_nonneg _ _ _ _)]
    exact (clippedMeanH_bounds hd1 _ ρ T x).2
  have hrel (k : ℤ) (ζ : Site d → ℤ) : escapePotential d x v ^ 2 * F (-1) ζ ≤ F k ζ ∧ F k ζ ≤ F (-1) ζ := by
    dsimp only [F]
    rw [clippedField_update, clippedField_update, clipSparse_eq (by norm_num : (-1 : ℤ) ≤ -1 ∧ -1 ≤ 1)]
    exact matchedMeanH_sparse_update_relative hd (clippedField ζ) v x ρ T (clipSparse k) (clipSparse_bounds k)
  refine ⟨partialInt (fun _ : Site d => ν) S (F (-1)) η, ?_, fun k => ?_⟩
  · exact integral_nonneg fun ζ => matchedMeanH_nonneg _ _ _ _
  · have hlo := partialInt_mul_le (fun _ : Site d => ν) S (F (-1)) (F k) (hFm (-1)) (hFm k)
      1 1 (hFb (-1)) (hFb k) (escapePotential d x v ^ 2) (fun ζ => (hrel k ζ).1) η
    have hhi := partialInt_mul_le (fun _ : Site d => ν) S (F k) (F (-1)) (hFm k) (hFm (-1))
      1 1 (hFb k) (hFb (-1)) 1 (fun ζ => by simpa only [one_mul] using (hrel k ζ).2) η
    have he := partialInt_update_insert (fun _ : Site d => ν) S
      (fun ζ => matchedMeanH (clippedField ζ) ρ T x) v η k
    change partialInt (fun _ : Site d => ν) S (F k) η = _ at he
    rw [he] at hlo hhi
    exact ⟨hlo, by simpa only [one_mul] using hhi⟩
end Parking
