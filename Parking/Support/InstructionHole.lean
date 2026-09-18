import Parking.Support.HoleRelative
import Parking.Support.InstructionPartial

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Averaging future rounds cannot create more holes than the current signed field contains. -/
theorem roundMeanH_bound (hd : 1 ≤ d) (A H : Site d → ℕ) (ρ : Label d × ℕ → ℝ)
    (T : ℕ) (x : Site d) (τ : RoundSlot d → Fin d × Bool) :
    |matchedMeanH (roundSigned A H τ) ρ T x| ≤ (H x : ℝ) := by
  rw [abs_of_nonneg (matchedMeanH_nonneg _ _ _ _)]
  apply (matchedMeanH_le_initial hd _ ρ T x).trans
  apply Nat.cast_le.mpr
  unfold roundSigned
  omega

theorem roundWithoutMeanH_bound (hd : 1 ≤ d) (A H : Site d → ℕ) (ρ : Label d × ℕ → ℝ)
    (T : ℕ) (x v : Site d) (j : ℕ) (τ : RoundSlot d → Fin d × Bool) :
    |matchedMeanH (roundWithout A H τ v j) ρ T x| ≤ (H x : ℝ) := by
  rw [abs_of_nonneg (matchedMeanH_nonneg _ _ _ _)]
  apply (matchedMeanH_le_initial hd _ ρ T x).trans
  apply Nat.cast_le.mpr
  unfold roundWithout
  omega

/-- Restoring one suppressed instruction reduces each hole probability only by its hitting factor. -/
theorem instruction_hole_relative (hd : 3 ≤ d) (A H : Site d → ℕ)
    (τ : RoundSlot d → Fin d × Bool) (v : Site d) (j : ℕ) (hj : j < A v)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (a : Fin d × Bool) :
    escapePotential d x (v + stepVec a) * matchedMeanH (roundWithout A H τ v j) ρ T x ≤
        matchedMeanH (roundSigned A H (Function.update τ (Sum.inl (v, j)) a)) ρ T x ∧
      matchedMeanH (roundSigned A H (Function.update τ (Sum.inl (v, j)) a)) ρ T x ≤
        matchedMeanH (roundWithout A H τ v j) ρ T x := by
  rw [roundSigned_eq_addParticle _ _ _ _ _ hj, Function.update_self, roundWithout_update]
  exact matchedMeanH_addParticle_relative hd _ _ _ _ _

/-- The same multiplicative influence survives averaging all unrevealed current entries. -/
theorem instruction_partial_hole_relative (hd : 3 ≤ d) (A H : Site d → ℕ)
    (v : Site d) (j : ℕ) (hj : j < A v) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d)
    (S : Set (RoundSlot d)) [DecidablePred (· ∈ S)] (τ : RoundSlot d → Fin d × Bool) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ a : Fin d × Bool,
      escapePotential d x (v + stepVec a) * b ≤
        partialInt (fun _ : RoundSlot d => stepLaw d) (insert (Sum.inl (v, j)) S)
          (fun ζ => matchedMeanH (roundSigned A H ζ) ρ T x) (Function.update τ (Sum.inl (v, j)) a) ∧
      partialInt (fun _ : RoundSlot d => stepLaw d) (insert (Sum.inl (v, j)) S)
          (fun ζ => matchedMeanH (roundSigned A H ζ) ρ T x) (Function.update τ (Sum.inl (v, j)) a) ≤ b := by
  classical
  have hd1 : 1 ≤ d := by omega
  haveI := stepLaw_isProbability hd1
  let Q := Measure.infinitePi fun _ : RoundSlot d => stepLaw d
  let g : (RoundSlot d → Fin d × Bool) → ℝ := fun ζ =>
    matchedMeanH (roundWithout A H (comb S τ ζ) v j) ρ T x
  have hm : Measurable (fun ζ : RoundSlot d → Fin d × Bool => comb S τ ζ) :=
    (measurable_comb S).comp (measurable_const.prodMk measurable_id)
  have hgm : Measurable g := (measurable_matchedMeanH hd1 ρ T x).comp
    (measurable_roundWithout (fun _ => A) (fun _ => H) (fun ζ => comb S τ ζ)
      measurable_const measurable_const hm v j)
  have hgi : Integrable g Q := Integrable.of_bound hgm.aestronglyMeasurable _
    (ae_of_all _ fun ζ => roundWithoutMeanH_bound hd1 A H ρ T x v j (comb S τ ζ))
  refine ⟨∫ ζ, g ζ ∂Q, integral_nonneg (fun ζ => matchedMeanH_nonneg _ _ _ _), fun a => ?_⟩
  let f : (RoundSlot d → Fin d × Bool) → ℝ := fun ζ =>
    matchedMeanH (roundSigned A H (Function.update (comb S τ ζ) (Sum.inl (v, j)) a)) ρ T x
  have hfm : Measurable f := (measurable_matchedMeanH hd1 ρ T x).comp
    (measurable_roundSigned (fun _ => A) (fun _ => H)
      (fun ζ => Function.update (comb S τ ζ) (Sum.inl (v, j)) a) measurable_const measurable_const
      (measurable_update_left.comp hm))
  have hfi : Integrable f Q := Integrable.of_bound hfm.aestronglyMeasurable _
    (ae_of_all _ fun ζ => roundMeanH_bound hd1 A H ρ T x _)
  have he (ζ : RoundSlot d → Fin d × Bool) :
      comb (insert (Sum.inl (v, j)) S) (Function.update τ (Sum.inl (v, j)) a) ζ =
        Function.update (comb S τ ζ) (Sum.inl (v, j)) a := by
    funext q
    by_cases hq : q = Sum.inl (v, j)
    · subst q; simp [comb]
    · simp [comb, hq]
  have havg : partialInt (fun _ : RoundSlot d => stepLaw d) (insert (Sum.inl (v, j)) S)
      (fun ζ => matchedMeanH (roundSigned A H ζ) ρ T x) (Function.update τ (Sum.inl (v, j)) a) = ∫ ζ, f ζ ∂Q := by
    unfold partialInt
    exact integral_congr_ae (ae_of_all _ fun ζ => congrArg (fun ξ => matchedMeanH (roundSigned A H ξ) ρ T x) (he ζ))
  rw [havg]
  constructor
  · rw [← integral_const_mul]
    exact integral_mono (hgi.const_mul _) hfi (fun ζ => (instruction_hole_relative hd A H (comb S τ ζ) v j hj ρ T x a).1)
  · exact integral_mono hfi hgi (fun ζ => (instruction_hole_relative hd A H (comb S τ ζ) v j hj ρ T x a).2)
end Parking
