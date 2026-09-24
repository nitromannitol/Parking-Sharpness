import Parking.Support.RoundMeanField
import Parking.Support.ProductReveal
import Parking.Support.InstructionUnused

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Averaging the unrevealed entries preserves the one-particle Green influence. -/
theorem instruction_partial_influence (hd : 3 ≤ d) (A H : Site d → ℕ)
    (N : ℕ) (hA : ∀ y, A y ≤ N) (v : Site d) (j : ℕ) (hj : j < A v)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d)
    (S : Set (RoundSlot d)) [DecidablePred (· ∈ S)]
    (τ : RoundSlot d → Fin d × Bool) :
    ∃ m : ℝ, ∀ a : Fin d × Bool,
      0 ≤ partialInt (fun _ : RoundSlot d => stepLaw d) (insert (Sum.inl (v, j)) S)
        (fun ζ => matchedMeanU (roundSigned A H ζ) ρ T x) (Function.update τ (Sum.inl (v, j)) a) - m ∧
      partialInt (fun _ : RoundSlot d => stepLaw d) (insert (Sum.inl (v, j)) S)
        (fun ζ => matchedMeanU (roundSigned A H ζ) ρ T x) (Function.update τ (Sum.inl (v, j)) a) - m
          ≤ fullGreen d (v + stepVec a - x) := by
  classical
  have hd1 : 1 ≤ d := by omega
  haveI := stepLaw_isProbability hd1
  let Q := Measure.infinitePi fun _ : RoundSlot d => stepLaw d
  let B : ℝ := ((T * ((2 * T + 1) ^ d * (2 * d * N)) : ℕ) : ℝ)
  let g : (RoundSlot d → Fin d × Bool) → ℝ := fun ζ =>
    matchedMeanU (roundWithout A H (comb S τ ζ) v j) ρ T x
  have hm : Measurable (fun ζ : RoundSlot d → Fin d × Bool => comb S τ ζ) :=
    (measurable_comb S).comp (measurable_const.prodMk measurable_id)
  have hgm : Measurable g := (measurable_matchedMeanU hd1 ρ T x).comp
    (measurable_roundWithout (fun _ => A) (fun _ => H) (fun ζ => comb S τ ζ)
      measurable_const measurable_const hm v j)
  have hgB (ζ : RoundSlot d → Fin d × Bool) : |g ζ| ≤ B := by
    rw [abs_of_nonneg (matchedMeanU_nonneg _ _ _ _)]
    have h := (matchedMeanU_addParticle hd (roundWithout A H (comb S τ ζ) v j)
      (v + stepVec ((comb S τ ζ) (Sum.inl (v, j)))) ρ T x).1
    rw [← roundSigned_eq_addParticle _ _ _ _ _ hj] at h
    exact (sub_nonneg.mp h).trans (by
      have hb := roundMeanU_bound hd1 A H N hA ρ T x (comb S τ ζ)
      exact (le_abs_self _).trans hb)
  have hgi : Integrable g Q := Integrable.of_bound hgm.aestronglyMeasurable B (ae_of_all _ hgB)
  refine ⟨∫ ζ, g ζ ∂Q, fun a => ?_⟩
  let f : (RoundSlot d → Fin d × Bool) → ℝ := fun ζ =>
    matchedMeanU (roundSigned A H (Function.update (comb S τ ζ) (Sum.inl (v, j)) a)) ρ T x
  have hfm : Measurable f := (measurable_matchedMeanU hd1 ρ T x).comp
    (measurable_roundSigned (fun _ => A) (fun _ => H)
      (fun ζ => Function.update (comb S τ ζ) (Sum.inl (v, j)) a) measurable_const measurable_const
      (measurable_update_left.comp hm))
  have hfi : Integrable f Q := Integrable.of_bound hfm.aestronglyMeasurable B
    (ae_of_all _ fun ζ => roundMeanU_bound hd1 A H N hA ρ T x _)
  have he (ζ : RoundSlot d → Fin d × Bool) :
      comb (insert (Sum.inl (v, j)) S) (Function.update τ (Sum.inl (v, j)) a) ζ =
        Function.update (comb S τ ζ) (Sum.inl (v, j)) a := by
    funext q
    by_cases hq' : q = Sum.inl (v, j)
    · subst q; simp [comb]
    · simp [comb, hq']
  have hvb (ζ : RoundSlot d → Fin d × Bool) : 0 ≤ f ζ - g ζ ∧
      f ζ - g ζ ≤ fullGreen d (v + stepVec a - x) :=
    instruction_future_influence hd A H (comb S τ ζ) v j hj ρ T x a
  have havg : partialInt (fun _ : RoundSlot d => stepLaw d) (insert (Sum.inl (v, j)) S)
      (fun ζ => matchedMeanU (roundSigned A H ζ) ρ T x) (Function.update τ (Sum.inl (v, j)) a) =
      ∫ ζ, f ζ ∂Q := by
    unfold partialInt
    apply integral_congr_ae
    exact ae_of_all _ fun ζ => congrArg (fun z => matchedMeanU (roundSigned A H z) ρ T x) (he ζ)
  rw [havg, ← integral_sub hfi hgi]
  refine ⟨integral_nonneg (fun ζ => (hvb ζ).1), ?_⟩
  have hb := integral_mono (hfi.sub hgi) (integrable_const (fullGreen d (v + stepVec a - x)))
    (fun ζ => (hvb ζ).2)
  simpa only [Pi.sub_apply, integral_const, probReal_univ, one_smul] using hb
end Parking
