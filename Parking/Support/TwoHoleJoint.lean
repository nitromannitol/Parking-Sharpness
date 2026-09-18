import Parking.Support.TwoHoleWeight
import Parking.Support.SceneryHoleProduct
import Parking.Support.ClippedRoundMean

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The finite weighted odometer that controls the instruction factors. -/
def twoHoleLoad (T : ℕ) (x z u : Site d) (R : ℕ) (ω : (Site d → ℤ) × RoundNoise d) : ℝ :=
  ∑ y ∈ boxFinset u R, holeKernel d x z y * clippedRoundU T y ω

theorem twoHoleLoad_nonneg (hd : 3 ≤ d) (T : ℕ) (x z u : Site d) (R : ℕ)
    (ω : (Site d → ℤ) × RoundNoise d) : 0 ≤ twoHoleLoad T x z u R ω :=
  Finset.sum_nonneg fun y _ => mul_nonneg (holeKernel_nonneg hd x z y) (clippedRoundU_bounds T y ω).1

theorem measurable_twoHoleLoad (hd : 1 ≤ d) (T : ℕ) (x z u : Site d) (R : ℕ) :
    Measurable (twoHoleLoad T x z u R) := by
  apply Finset.measurable_sum
  intro y _
  exact (measurable_clippedRoundU hd T y).const_mul _

/-- The joint hole indicator discounted by the instruction cost. -/
def twoHoleDiscount (T : ℕ) (x z u : Site d) (R : ℕ) (ω : (Site d → ℤ) × RoundNoise d) : ℝ :=
  ((clippedRoundH T x ω : ℝ) * (clippedRoundH T z ω : ℝ)) *
    Real.exp (-(twoHoleLoad T x z u R ω / (1 / (2 * escapeConst d)) ^ 2))

theorem twoHoleDiscount_bounds (hd : 3 ≤ d) (T : ℕ) (x z u : Site d) (R : ℕ)
    (ω : (Site d → ℤ) × RoundNoise d) : 0 ≤ twoHoleDiscount T x z u R ω ∧ twoHoleDiscount T x z u R ω ≤ 1 := by
  have hx : (clippedRoundH T x ω : ℝ) ≤ 1 := by exact_mod_cast clippedRoundH_le_one T x ω
  have hz : (clippedRoundH T z ω : ℝ) ≤ 1 := by exact_mod_cast clippedRoundH_le_one T z ω
  have hc : Real.exp (-(twoHoleLoad T x z u R ω / (1 / (2 * escapeConst d)) ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (twoHoleLoad_nonneg hd T x z u R ω) (sq_nonneg _)))
  refine ⟨mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.exp_pos _).le, ?_⟩
  have hp : (clippedRoundH T x ω : ℝ) * (clippedRoundH T z ω : ℝ) ≤ 1 :=
    (mul_le_mul hx hz (Nat.cast_nonneg _) (by norm_num)).trans_eq (one_mul _)
  exact (mul_le_mul hp hc (Real.exp_pos _).le (by norm_num)).trans_eq (one_mul _)

theorem measurable_twoHoleDiscount (hd : 1 ≤ d) (T : ℕ) (x z u : Site d) (R : ℕ) :
    Measurable (twoHoleDiscount T x z u R) := by
  have hm (y : Site d) : Measurable (fun ω => (clippedRoundH T y ω : ℝ)) :=
    (measurable_from_countable' fun n : ℕ => (n : ℝ)).comp (measurable_clippedRoundH hd T y)
  exact ((hm x).mul (hm z)).mul (Real.measurable_exp.comp ((measurable_twoHoleLoad hd T x z u R).div_const _).neg)

/-- The scenery and instruction factors together control the discounted two-hole event. -/
theorem integral_twoHoleDiscount_le (hd : 3 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hclip : ∀ᵐ k ∂ν, clipSparse k = k) (T : ℕ) (x z u : Site d) (hxz : x ≠ z) (R : ℕ)
    (hxR : boxFinset x T ⊆ boxFinset u R) (hzR : boxFinset z T ⊆ boxFinset u R) :
    (∫ ω, twoHoleDiscount T x z u R ω ∂((iidLaw d ν).prod (roundNoiseLaw d))) ≤
      Real.exp (holeSceneryConst d * ∑ y ∈ boxFinset u R,
        (1 - escapePotential d x y) * (1 - escapePotential d z y)) * holeProb d ν T ^ 2 := by
  have hd1 : 1 ≤ d := by omega
  haveI := roundNoiseLaw_isProbability hd1
  haveI : IsProbabilityMeasure (iidLaw d ν) := by unfold iidLaw; infer_instance
  let μ := (iidLaw d ν).prod (roundNoiseLaw d)
  have hi : Integrable (twoHoleDiscount T x z u R) μ :=
    Integrable.of_bound (measurable_twoHoleDiscount hd1 T x z u R).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (twoHoleDiscount_bounds hd T x z u R ω).1]
        exact (twoHoleDiscount_bounds hd T x z u R ω).2)
  have hgm (y : Site d) : Measurable (fun η : Site d → ℤ => matchedMeanH (clippedField η) 0 T y) :=
    (measurable_matchedMeanH hd1 0 T y).comp measurable_clippedField
  have hgi : Integrable (fun η => matchedMeanH (clippedField η) 0 T x * matchedMeanH (clippedField η) 0 T z) (iidLaw d ν) :=
    Integrable.of_bound ((hgm x).mul (hgm z)).aestronglyMeasurable 1
      (ae_of_all _ fun η => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (clippedMeanH_bounds hd1 η 0 T x).1 (clippedMeanH_bounds hd1 η 0 T z).1)]
        exact (mul_le_mul (clippedMeanH_bounds hd1 η 0 T x).2 (clippedMeanH_bounds hd1 η 0 T z).2
          (clippedMeanH_bounds hd1 η 0 T z).1 (by norm_num)).trans_eq (one_mul _))
  have hpoint (η : Site d → ℤ) : (∫ σ, twoHoleDiscount T x z u R (η, σ) ∂(roundNoiseLaw d)) ≤
      matchedMeanH (clippedField η) 0 T x * matchedMeanH (clippedField η) 0 T z :=
    integral_twoHole_discount_le hd (clippedField η) 1 (clippedField_particle_bound η) 0 T x z u R hxR hzR
  have h := integral_mono hi.integral_prod_left hgi hpoint
  rw [← integral_prod _ hi] at h
  apply h.trans
  have hs := scenery_hole_product_factor hd ν 0 T x z u hxz R hxR hzR
  rw [integral_clippedMeanH_eq_holeProb hd1 ν hclip T x, integral_clippedMeanH_eq_holeProb hd1 ν hclip T z] at hs
  simpa only [pow_two] using hs
end Parking
