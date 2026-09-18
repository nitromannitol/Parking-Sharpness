import Parking.Support.ClippedTable

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The table and particle descriptions have identical moment norms. -/
theorem rNorm_clippedTableU (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hclip : ∀ᵐ k ∂ν, clipSparse k = k) (T : ℕ) (x : Site d) {r : ℝ} (hr : 0 ≤ r) :
    rNorm ((iidLaw d ν).prod (flatRoundNoiseLaw d)) r (clippedTableU T x) =
      rNorm (law d ν) r (fun ω => (U ω T x : ℝ)) := by
  unfold rNorm
  rw [integral_clippedTableU hd ν hclip T x (fun z => |z| ^ r)
    ((measurable_rpow_const hr).comp measurable_id.abs)]

/-- Translation invariance makes the bounded table moments independent of the observation site. -/
theorem integral_clippedTableU_rpow_shift (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4)
    (T : ℕ) (x : Site d) {r : ℝ} (hr : 1 ≤ r) :
    ∫ ω, clippedTableU T x ω ^ r ∂((iidLaw d (threePointLaw p)).prod (flatRoundNoiseLaw d)) =
      ∫ ω, clippedTableU T 0 ω ^ r ∂((iidLaw d (threePointLaw p)).prod (flatRoundNoiseLaw d)) := by
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  rw [integral_clippedTableU hd _ (ae_clipSparse_threePointLaw p) T x _
    (measurable_rpow_const (by linarith)),
    integral_clippedTableU hd _ (ae_clipSparse_threePointLaw p) T 0 _
    (measurable_rpow_const (by linarith))]
  exact integral_U_rpow_shift hd _ (by norm_num : (0 : ℝ) < 1)
    (integrable_threePointLaw p _) hr T x

/-- Every sparse table odometer has the same moment norm as the origin. -/
theorem rNorm_clippedTableU_shift (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4)
    (T : ℕ) (x : Site d) {r : ℝ} (hr : 1 ≤ r) :
    rNorm ((iidLaw d (threePointLaw p)).prod (flatRoundNoiseLaw d)) r (clippedTableU T x) =
      rNorm ((iidLaw d (threePointLaw p)).prod (flatRoundNoiseLaw d)) r (clippedTableU T 0) := by
  unfold rNorm
  simp_rw [abs_of_nonneg (clippedTableU_nonneg _ _ _)]
  rw [integral_clippedTableU_rpow_shift hd hp hp4 T x hr]
end Parking
