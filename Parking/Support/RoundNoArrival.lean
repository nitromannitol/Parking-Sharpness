import Parking.Support.IncomingSlots
import Parking.Support.CoordinateProductIntegral

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The entrance probability of one possible table entry. -/
def entryEntranceProb (x : Site d) (q : RoundSlot d) : ℝ :=
  match q with
  | Sum.inl (y, _) => kern d y x
  | Sum.inr _ => 0

theorem entryAvoids_nonneg (x : Site d) (q : RoundSlot d) (b : Fin d × Bool) : 0 ≤ entryAvoids x q b := by
  cases q with
  | inl q => rcases q with ⟨y, j⟩; dsimp only [entryAvoids]; split <;> norm_num
  | inr q => norm_num [entryAvoids]

/-- A fresh entry avoids the target with probability one minus its entrance probability. -/
theorem integral_entryAvoids (hd : 1 ≤ d) (x : Site d) (q : RoundSlot d) :
    ∫ b, entryAvoids x q b ∂(stepLaw d) = 1 - entryEntranceProb x q := by
  classical
  haveI := stepLaw_isProbability hd
  cases q with
  | inr q => simp [entryAvoids, entryEntranceProb]
  | inl q =>
      rcases q with ⟨y, j⟩
      let F : Fin d × Bool → ℝ := fun b => if y + stepVec b = x then 1 else 0
      have hi : Integrable F (stepLaw d) := by
        apply Integrable.of_bound (measurable_from_countable' F).aestronglyMeasurable 1
        exact ae_of_all _ fun b => by dsimp only [F]; split <;> norm_num
      have he (b : Fin d × Bool) : entryAvoids x (Sum.inl (y, j)) b = 1 - F b := by
        dsimp only [entryAvoids, F]
        split <;> norm_num
      simp_rw [he]
      rw [integral_sub (integrable_const 1) hi, integral_const, probReal_univ, one_smul]
      have hF : (∫ b, F b ∂(stepLaw d)) = kern d y x := by
        change (∫ b, (fun z : Site d => if z = x then (1 : ℝ) else 0) (y + stepVec b) ∂(stepLaw d)) = _
        rw [integral_stepLaw_add hd (fun z : Site d => if z = x then (1 : ℝ) else 0) y, walkOp_eq_nbrFinset]
        by_cases hx : x ∈ nbrFinset y <;> simp [kern, hx]
      rw [hF]
      rfl

/-- The entrance probabilities of the potentially used entries add to the expected arrivals. -/
theorem sum_entryEntranceProb (A : Site d → ℕ) (x : Site d) :
    ∑ q ∈ incomingSlots A x, entryEntranceProb x q = walkOp (fun y => (A y : ℝ)) x := by
  rw [sum_incomingSlots]
  simp only [entryEntranceProb, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [walkOp_eq_nbrFinset, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y hy
  rw [kern, if_pos (nbrFinset_symm hy)]
  ring

/-- The probability of no arrival in a fresh round is at most the exponential of minus its compensator. -/
theorem integral_noArrivals_le_exp (hd : 1 ≤ d) (A : Site d → ℕ) (x : Site d) :
    (∫ τ, (if (countArrivals A τ x).card = 0 then (1 : ℝ) else 0)
      ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d)) ≤
        Real.exp (-walkOp (fun y => (A y : ℝ)) x) := by
  classical
  haveI := stepLaw_isProbability hd
  simp_rw [noArrivals_eq_prod]
  rw [integral_finset_prod_coordinates _ _ (entryAvoids x) (fun q => measurable_from_countable' _)]
  have hprod : (∏ q ∈ incomingSlots A x, ∫ b, entryAvoids x q b ∂(stepLaw d)) ≤
      ∏ q ∈ incomingSlots A x, Real.exp (-entryEntranceProb x q) := by
    apply Finset.prod_le_prod
    · intro q _
      exact integral_nonneg (entryAvoids_nonneg x q)
    · intro q _
      rw [integral_entryAvoids hd]
      exact Real.one_sub_le_exp_neg _
  rw [← Real.exp_sum, Finset.sum_neg_distrib, sum_entryEntranceProb] at hprod
  exact hprod
end Parking
