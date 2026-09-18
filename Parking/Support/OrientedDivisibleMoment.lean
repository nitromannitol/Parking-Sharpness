/- Moment bounds for the two-dimensional directed divisible process. -/
import Parking.Support.OrientedMaxMoment

noncomputable section
namespace Parking
open MeasureTheory LatticeProb

theorem exists_uOriented_two_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (r : ℝ) (hr : 4 < r) (hmom : Integrable (fun z : ℝ => |z| ^ r) μ)
    (hmean : ∫ z : ℝ, z ∂μ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Integrable (fun η : Site 2 → ℝ => |uOriented η n 0| ^ r) (iidLaw 2 μ) ∧
      rNorm (iidLaw 2 μ) r (fun η => uOriented η n 0) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4) := by
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  haveI : IsProbabilityMeasure (iidLaw 2 μ) := by unfold iidLaw; infer_instance
  obtain ⟨A, hA, hmax⟩ := exists_orientedMax_moment μ r hr hmom hmean
  refine ⟨2 * A, by positivity, fun n hn => ?_⟩
  obtain ⟨hi, hb⟩ := hmax n hn
  let F : (ℕ → Fin 2 × Bool) × (Site 2 → ℝ) → ℝ :=
    fun ω => orientedMax (orientedPotential ω.2) n 0 ω.1
  let J : (Site 2 → ℝ) → ℝ := fun η => ∫ p, |F (p, η)| ^ r ∂(walkLaw 2)
  have hJi : Integrable J (iidLaw 2 μ) := hi.integral_prod_right
  have hpt (η : Site 2 → ℝ) : |uOriented η n 0| ^ r ≤ (2 : ℝ) ^ r * J η := by
    have hMn (p : ℕ → Fin 2 × Bool) : 0 ≤ F (p, η) := orientedMax_nonneg _ _ _ _
    have hMi : Integrable (fun p => F (p, η)) (walkLaw 2) := integrable_orientedMax (d := 2) (by norm_num) (orientedPotential η) n 0
    have hMri : Integrable (fun p => F (p, η) ^ r) (walkLaw 2) := by
      apply integrable_of_finite_dependence (by norm_num) n
      intro p q hpq
      dsimp only [F]
      rw [orientedMax_congr (orientedPotential η) n 0 hpq]
    have hJensen := rpow_integral_le hMn hMi hr1 hMri
    have hj : (orientedMaxMean (orientedPotential η) n 0) ^ r ≤ J η := by
      simpa only [J, abs_of_nonneg (hMn _), orientedMaxMean, F] using hJensen
    have hu := uOriented_le_potential_add_max (d := 2) (by norm_num) η n 0
    have ha := abs_le_orientedMaxMean (d := 2) (by norm_num) (orientedPotential η) n 0
    have huB : uOriented η n 0 ≤ 2 * orientedMaxMean (orientedPotential η) n 0 := by
      linarith [le_abs_self (orientedPotential η n 0)]
    have hM : 0 ≤ orientedMaxMean (orientedPotential η) n 0 := (abs_nonneg _).trans ha
    rw [abs_of_nonneg (uOriented_nonneg η n 0)]
    calc uOriented η n 0 ^ r ≤ (2 * orientedMaxMean (orientedPotential η) n 0) ^ r :=
        Real.rpow_le_rpow (uOriented_nonneg η n 0) huB hr0.le
      _ = 2 ^ r * (orientedMaxMean (orientedPotential η) n 0) ^ r :=
        Real.mul_rpow (by norm_num) hM
      _ ≤ _ := mul_le_mul_of_nonneg_left hj (Real.rpow_nonneg (by norm_num) r)
  have hui : Integrable (fun η : Site 2 → ℝ => |uOriented η n 0| ^ r) (iidLaw 2 μ) := by
    refine (hJi.const_mul (2 ^ r)).mono'
      (((measurable_uOriented n 0).abs.pow_const r).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun η => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r)]
    exact hpt η
  have hraw := integral_mono hui (hJi.const_mul (2 ^ r)) hpt
  rw [integral_const_mul] at hraw
  have hJ : (∫ η, J η ∂(iidLaw 2 μ)) =
      ∫ ω, |F ω| ^ r ∂((walkLaw 2).prod (iidLaw 2 μ)) :=
    (integral_prod_symm (fun ω => |F ω| ^ r) hi).symm
  rw [hJ] at hraw
  have hroot := Real.rpow_le_rpow
    (integral_nonneg fun η => Real.rpow_nonneg (abs_nonneg _) r)
    hraw (by positivity : (0 : ℝ) ≤ 1 / r)
  rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) r)
    (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) r),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    mul_one_div, div_self hr0.ne', Real.rpow_one] at hroot
  refine ⟨hui, hroot.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

end Parking
