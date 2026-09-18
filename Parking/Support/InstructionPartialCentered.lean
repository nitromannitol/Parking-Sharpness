import Parking.Support.InstructionPartial

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- After every unrevealed instruction is averaged, a used entry still has variance at most PG². -/
theorem instruction_partial_centered_bounds (hd : 3 ≤ d) (A H : Site d → ℕ)
    (N : ℕ) (hA : ∀ y, A y ≤ N) (v : Site d) (j : ℕ)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d)
    (S : Set (RoundSlot d)) [DecidablePred (· ∈ S)] (τ : RoundSlot d → Fin d × Bool) :
    let f := fun a : Fin d × Bool => partialInt (fun _ : RoundSlot d => stepLaw d)
      (insert (Sum.inl (v, j)) S) (fun ζ => matchedMeanU (roundSigned A H ζ) ρ T x)
        (Function.update τ (Sum.inl (v, j)) a)
    (∀ a, |f a - ∫ b, f b ∂(stepLaw d)| ≤ escapeConst d) ∧
      (∫ a, (f a - ∫ b, f b ∂(stepLaw d)) ^ 2 ∂(stepLaw d)) ≤
        if j < A v then walkOp (fun y => fullGreen d (y - x) ^ 2) v else 0 := by
  classical
  have hd1 : 1 ≤ d := by omega
  haveI := stepLaw_isProbability hd1
  dsimp only
  by_cases hj : j < A v
  · rw [if_pos hj]
    obtain ⟨m, hm⟩ := instruction_partial_influence hd A H N hA v j hj ρ T x S τ
    have h := centered_influence_bounds (stepLaw d)
      (fun a : Fin d × Bool => partialInt (fun _ : RoundSlot d => stepLaw d)
        (insert (Sum.inl (v, j)) S) (fun ζ => matchedMeanU (roundSigned A H ζ) ρ T x)
          (Function.update τ (Sum.inl (v, j)) a))
      (fun a => fullGreen d (v + stepVec a - x)) m (escapeConst d)
      (measurable_from_countable' _) (measurable_from_countable' _)
      (fun a => ⟨(hm a).1, (hm a).2, fullGreen_le_escapeConst hd _⟩)
    refine ⟨h.1, h.2.trans_eq ?_⟩
    exact integral_stepLaw_add hd1 (fun y => fullGreen d (y - x) ^ 2) v
  · rw [if_neg hj]
    have hf (a : Fin d × Bool) : partialInt (fun _ : RoundSlot d => stepLaw d)
        (insert (Sum.inl (v, j)) S) (fun ζ => matchedMeanU (roundSigned A H ζ) ρ T x)
          (Function.update τ (Sum.inl (v, j)) a) =
        partialInt (fun _ : RoundSlot d => stepLaw d) (insert (Sum.inl (v, j)) S)
          (fun ζ => matchedMeanU (roundSigned A H ζ) ρ T x) τ := by
      unfold partialInt
      apply integral_congr_ae
      apply ae_of_all
      intro ζ
      have he : comb (insert (Sum.inl (v, j)) S) (Function.update τ (Sum.inl (v, j)) a) ζ =
          Function.update (comb (insert (Sum.inl (v, j)) S) τ ζ) (Sum.inl (v, j)) a := by
        funext q
        by_cases hq : q = Sum.inl (v, j)
        · subst q; simp [comb]
        · simp [comb, hq]
      calc
        _ = matchedMeanU (roundSigned A H
            (Function.update (comb (insert (Sum.inl (v, j)) S) τ ζ) (Sum.inl (v, j)) a)) ρ T x :=
          congrArg (fun z => matchedMeanU (roundSigned A H z) ρ T x) he
        _ = _ := congrArg (fun z => matchedMeanU z ρ T x)
          (roundSigned_update_unused A H _ v j (Nat.le_of_not_gt hj) a)
    simp only [hf, integral_const, probReal_univ, one_smul, sub_self, abs_zero]
    exact ⟨fun _ => (by positivity : (0 : ℝ) ≤ 1).trans (one_le_escapeConst hd), by norm_num⟩
end Parking
