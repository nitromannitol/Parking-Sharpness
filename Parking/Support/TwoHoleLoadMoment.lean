import Parking.Support.TwoHoleJoint
import Parking.Support.OnePointMoment
import Parking.Support.WeightedNorm

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Every finite two-hole load has the one-point linear moment bound times its total weight. -/
theorem exists_twoHoleLoad_moment_bound (hBernstein : External.Bernstein) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 0 < p → p ≤ 1 / 4 → ∀ (T : ℕ) (x z u : Site d) (R : ℕ) (B : ℝ),
      (∑ y ∈ boxFinset u R, holeKernel d x z y) ≤ B → ∀ r : ℝ, 2 ≤ r →
        Integrable (fun ω => twoHoleLoad T x z u R ω ^ r) ((iidLaw d (threePointLaw p)).prod (roundNoiseLaw d)) ∧
          rNorm ((iidLaw d (threePointLaw p)).prod (roundNoiseLaw d)) r (twoHoleLoad T x z u R) ≤
            C * (meanU (law d (threePointLaw p)) T + r) * B := by
  obtain ⟨C, hC, hb⟩ := exists_sparse_odometer_moment_bound hBernstein hd
  refine ⟨C, hC, fun p hp hp4 T x z u R B hB r hr => ?_⟩
  have hd1 : 1 ≤ d := by omega
  have hd3 : 3 ≤ d := by omega
  haveI := threePointLaw_isProbability hp.le (by linarith : 2 * p ≤ 1)
  haveI : IsProbabilityMeasure (iidLaw d (threePointLaw p)) := by unfold iidLaw; infer_instance
  haveI := roundNoiseLaw_isProbability hd1
  let μ := (iidLaw d (threePointLaw p)).prod (roundNoiseLaw d)
  let M := C * (meanU (law d (threePointLaw p)) T + r)
  have hM : 0 ≤ M := mul_nonneg hC.le (add_nonneg (integral_nonneg fun _ => Nat.cast_nonneg _) (by linarith))
  have hi (y : Site d) : Integrable (fun ω => clippedRoundU T y ω ^ r) μ :=
    integrable_rpow_bounded_nonneg μ _ (measurable_clippedRoundU hd1 T y)
      (fun ω => (clippedRoundU_bounds T y ω).1) _ (fun ω => (clippedRoundU_bounds T y ω).2) (by linarith)
  have hnorm (y : Site d) : rNorm μ r (clippedRoundU T y) ≤ M := by
    unfold rNorm
    simp only [abs_of_nonneg (clippedRoundU_bounds T y _).1]
    rw [integral_clippedRoundU_rpow hd1 _ (ae_clipSparse_threePointLaw p) T y r]
    exact (hb p hp hp4 T y r hr).2
  have h := rNorm_weighted_sum_le μ (boxFinset u R) (holeKernel d x z) (clippedRoundU T)
    (fun y _ => holeKernel_nonneg hd3 x z y) (fun y _ ω => (clippedRoundU_bounds T y ω).1)
    (fun y _ => measurable_clippedRoundU hd1 T y) (by linarith : 1 ≤ r) (fun y _ => hi y) M hM (fun y _ => hnorm y)
  refine ⟨h.1, h.2.trans ?_⟩
  exact (mul_le_mul_of_nonneg_right hB hM).trans_eq (mul_comm _ _)
end Parking
