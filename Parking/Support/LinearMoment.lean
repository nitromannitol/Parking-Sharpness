/- A square-function estimate for finite centered linear combinations. -/
import LatticeProb.Prob.LpSmooth
import LatticeProb.Prob.FiniteMarginal

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset

theorem linear_sum_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a ξ : ι → ℝ) (i : ι) (y : ℝ) :
    (∑ j, a j * ξ j) - (∑ j, a j * Function.update ξ i y j) = a i * (ξ i - y) := by
  rw [← sum_sub_distrib, sum_eq_single i]
  · simp only [Function.update_self]
    ring
  · intro j _ hji
    rw [Function.update_of_ne hji]
    ring
  · simp

/-- The square of the `L^p` norm of a centered linear combination is bounded
by its coefficient square sum. The constant precedes the number of coordinates. -/
theorem exists_linear_moment_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 2 ≤ p) (hmom : Integrable (fun z : ℝ => |z| ^ p) μ)
    (hmean : ∫ z : ℝ, z ∂μ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a : Fin N → ℝ),
      Integrable (fun ξ : Fin N → ℝ => |∑ i, a i * ξ i| ^ p) (Measure.pi fun _ : Fin N => μ) ∧
      (∫ ξ : Fin N → ℝ, |∑ i, a i * ξ i| ^ p ∂(Measure.pi fun _ : Fin N => μ)) ^ (2 / p) ≤
        C * ∑ i, a i ^ 2 := by
  obtain ⟨C, hC, hsquare⟩ := exists_lp_square_pi hp
  let V := pairMoment μ p ^ (2 / p)
  have hV : 0 ≤ V := Real.rpow_nonneg (pairMoment_nonneg μ p) _
  refine ⟨C * (V + 1), mul_pos hC (by linarith), fun N a => ?_⟩
  let F : (Fin N → ℝ) → ℝ := fun ξ => ∑ i, a i * ξ i
  have hFm : Measurable F := by
    dsimp only [F]
    fun_prop
  have hLip : ∀ ξ : Fin N → ℝ, ∀ i : Fin N, ∀ y : ℝ,
      |F ξ - F (Function.update ξ i y)| ≤ |a i| * |ξ i - y| := by
    intro ξ i y
    rw [show F ξ - F (Function.update ξ i y) = a i * (ξ i - y) from linear_sum_update a ξ i y,
      abs_mul]
  have hI : Integrable (fun ξ => |F ξ| ^ p) (Measure.pi fun _ : Fin N => μ) :=
    integrable_rpow_of_lip_fam _ (by linarith) (fun _ => hmom) F hFm
      (fun i => |a i|) (fun i => abs_nonneg _) hLip
  have hid : Integrable (fun z : ℝ => z) μ := integrable_abs_of_rpow μ (by linarith)
    _ measurable_id.aestronglyMeasurable hmom
  have hcoord : ∀ i : Fin N, Integrable (fun ξ : Fin N → ℝ => ξ i) (Measure.pi fun _ : Fin N => μ) := by
    intro i
    exact integrable_comp_mp (measurePreserving_eval (fun _ : Fin N => μ) i)
      (fun z : ℝ => z) measurable_id.aestronglyMeasurable hid
  have hcoordmean : ∀ i : Fin N, (∫ ξ : Fin N → ℝ, ξ i ∂(Measure.pi fun _ : Fin N => μ)) = 0 := by
    intro i
    exact (integral_comp_mp (measurePreserving_eval (fun _ : Fin N => μ) i)
      (fun z : ℝ => z) measurable_id.aestronglyMeasurable).symm.trans hmean
  have hFmean : (∫ ξ, F ξ ∂(Measure.pi fun _ : Fin N => μ)) = 0 := by
    rw [show F = fun ξ : Fin N → ℝ => ∑ i, a i * ξ i from rfl,
      integral_finsetSum _ (fun i _ => (hcoord i).const_mul (a i))]
    simp only [integral_const_mul, hcoordmean, mul_zero, sum_const_zero]
  have hsq := hsquare N (fun _ : Fin N => μ) (fun _ => inferInstance) F hFm
    (fun i => |a i|) (fun i => abs_nonneg _) hLip (fun _ => hmom)
  simp only [hFmean, sub_zero, sq_abs] at hsq
  rw [← sum_mul] at hsq
  refine ⟨hI, hsq.trans ?_⟩
  have ha : 0 ≤ ∑ i : Fin N, a i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  change C * ((∑ i : Fin N, a i ^ 2) * V) ≤ C * (V + 1) * ∑ i : Fin N, a i ^ 2
  nlinarith

end Parking
