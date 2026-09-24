/- Applying the cited kernel concentration estimate to the directed divisible recursion. -/
import Parking.Support.OrientedAllNorms
import Parking.Support.OrientedLaw
import Parking.Support.OrientedFinite

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

theorem orientedKappa_nonneg (d n : ℕ) : 0 ≤ orientedKappa d n := by
  unfold orientedKappa
  split_ifs
  · positivity
  · exact Real.log_nonneg (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  · norm_num

theorem exists_uOriented_centered_bound (hd : 2 ≤ d) (hConc : Parking.External.UConcentration)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {θ : ℝ} (hθ : 0 < θ)
    (he : Integrable (fun z : ℝ => Real.exp (θ * |z|)) μ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
      (∫ η : Site d → ℝ, |uOriented η n 0 - ∫ η', uOriented η' n 0 ∂(iidLaw d μ)| ^ r
        ∂(iidLaw d μ)) ^ (1 / r) ≤ C * (Real.sqrt (r * orientedKappa d n) + r) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨A, hA, hb⟩ := hConc d hd1 1 (orientedKern d) (isLatticeKernel_oriented hd1)
    μ inferInstance θ hθ he
  obtain ⟨c, D, _hc, hD, hg⟩ := exists_orientedGreen_sq_rates hd
  refine ⟨A * (Real.sqrt D + 1), by positivity, fun n hn r hr => ?_⟩
  have hr0 : 0 ≤ r := by linarith
  have h := hb n hn r hr
  simp only [kSol_oriented, kGreen_oriented] at h
  have hnorm : l2Norm (orientedGreen d n) ≤ Real.sqrt D * Real.sqrt (orientedKappa d n) := by
    have h := Real.sqrt_le_sqrt (hg n hn).2
    rwa [Real.sqrt_mul hD.le] at h
  have h1 : Real.sqrt r * l2Norm (orientedGreen d n) ≤
      Real.sqrt D * Real.sqrt (r * orientedKappa d n) := by
    have h := mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg r)
    rw [Real.sqrt_mul hr0]
    nlinarith [h]
  have h2 : r * supAbs (orientedGreen d n) ≤ r := by
    have h := mul_le_mul_of_nonneg_left (orientedGreen_supAbs_le hd1 n) hr0
    simpa only [mul_one] using h
  have h3 : Real.sqrt r * l2Norm (orientedGreen d n) + r * supAbs (orientedGreen d n) ≤
      (Real.sqrt D + 1) * (Real.sqrt (r * orientedKappa d n) + r) := by
    nlinarith [Real.sqrt_nonneg (r * orientedKappa d n),
      mul_nonneg (Real.sqrt_nonneg D) hr0]
  exact h.trans ((mul_le_mul_of_nonneg_left h3 hA.le).trans_eq (by ring))

theorem exists_oriented_centered_bound (hd : 2 ≤ d) (hConc : Parking.External.UConcentration)
    (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
      (∫ ω : Data d, |uOriented (fun y => (ω.1 y : ℝ)) n 0 -
          meanuOriented (orientedLaw d ν) n| ^ r ∂(orientedLaw d ν)) ^ (1 / r) ≤
        C * (Real.sqrt (r * orientedKappa d n) + r) := by
  haveI := hν.prob
  obtain ⟨θ, hθ, he⟩ := realLaw_expMoment ν hν
  obtain ⟨C, hC, hb⟩ := exists_uOriented_centered_bound hd hConc (realLaw ν) hθ he
  refine ⟨C, hC, fun n hn r hr => ?_⟩
  have hmean : meanuOriented (orientedLaw d ν) n =
      ∫ η : Site d → ℝ, uOriented η n 0 ∂(iidLaw d (realLaw ν)) :=
    integral_oriented_confReal (by omega) ν (measurable_uOriented n 0)
  have hmap := integral_oriented_confReal (by omega : 1 ≤ d) ν
    (((measurable_uOriented n 0).sub measurable_const).abs.pow_const r)
      (G := fun η => |uOriented η n 0 - meanuOriented (orientedLaw d ν) n| ^ r)
  rw [hmean] at hmap
  rw [hmean]
  change (∫ ω : Data d, |uOriented (confReal ω) n 0 -
    ∫ η : Site d → ℝ, uOriented η n 0 ∂(iidLaw d (realLaw ν))| ^ r ∂(orientedLaw d ν)) ^ (1 / r) ≤ _
  rw [hmap]
  exact hb n hn r hr

end Parking
