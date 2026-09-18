/- Expected counts with a bounded random horizon independent of each trial. -/
import Mathlib

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory Finset
open scoped Classical

theorem count_below_eq_sum (n M : ℕ) (hn : n ≤ M) (P : ℕ → Prop) :
    ((range n).filter P).card = ∑ j ∈ range M, if j < n ∧ P j then 1 else 0 := by
  rw [card_filter]
  calc
    (∑ j ∈ range n, if P j then 1 else 0) =
        ∑ j ∈ range n, if j < n ∧ P j then 1 else 0 := by
          apply sum_congr rfl
          intro j hj
          simp only [mem_range.mp hj, true_and]
    _ = _ := sum_subset (range_mono hn) (fun j _ hj => if_neg (fun h => hj (mem_range.mpr h.1)))

theorem integral_event_indicator {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {S : Set Ω} (hS : MeasurableSet S) :
    (∫ ω, (if ω ∈ S then (1 : ℝ) else 0) ∂μ) = μ.real S := by
  simpa only [Set.indicator_apply, Pi.one_apply] using integral_indicator_one (μ := μ) hS

theorem integral_random_count {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℕ) (hN : Measurable N) (Y : ℕ → Ω → X) (hY : ∀ j, Measurable (Y j))
    (a : X) (M : ℕ) (hNM : ∀ᵐ ω ∂μ, N ω ≤ M) (p : ℝ)
    (hind : ∀ j, j < M → IndepFun N (Y j) μ)
    (hp : ∀ j, j < M → μ.real {ω | Y j ω = a} = p) :
    Integrable (fun ω => (((range (N ω)).filter fun j => Y j ω = a).card : ℝ)) μ ∧
      (∫ ω, (((range (N ω)).filter fun j => Y j ω = a).card : ℝ) ∂μ) =
        p * ∫ ω, (N ω : ℝ) ∂μ := by
  let C : ℕ → Set Ω := fun j => {ω | j < N ω}
  let D : ℕ → Set Ω := fun j => {ω | j < N ω ∧ Y j ω = a}
  have hC (j : ℕ) : MeasurableSet (C j) := hN (Set.to_countable {k : ℕ | j < k}).measurableSet
  have hD (j : ℕ) : MeasurableSet (D j) := (hC j).inter ((hY j) (measurableSet_singleton a))
  let f : ℕ → Ω → ℝ := fun j => Set.indicator (D j) (fun _ => 1)
  let g : ℕ → Ω → ℝ := fun j => Set.indicator (C j) (fun _ => 1)
  have hf (j : ℕ) : Integrable (f j) μ := (integrable_const (1 : ℝ)).indicator (hD j)
  have hg (j : ℕ) : Integrable (g j) μ := (integrable_const (1 : ℝ)).indicator (hC j)
  have hfi : Integrable (fun ω => ∑ j ∈ range M, f j ω) μ := integrable_finsetSum _ (fun j _ => hf j)
  have hgi : Integrable (fun ω => ∑ j ∈ range M, g j ω) μ := integrable_finsetSum _ (fun j _ => hg j)
  have heF : (fun ω => (((range (N ω)).filter fun j => Y j ω = a).card : ℝ)) =ᵐ[μ]
      fun ω => ∑ j ∈ range M, f j ω := hNM.mono fun ω hω => by
    have h := count_below_eq_sum (N ω) M hω (fun j => Y j ω = a)
    simp only [f, D, Set.indicator_apply, Set.mem_setOf_eq]
    exact_mod_cast h
  have heG : (fun ω => (N ω : ℝ)) =ᵐ[μ] fun ω => ∑ j ∈ range M, g j ω := hNM.mono fun ω hω => by
    have h := count_below_eq_sum (N ω) M hω (fun _ => True)
    simp only [filter_true, card_range, and_true] at h
    simp only [g, C, Set.indicator_apply, Set.mem_setOf_eq]
    exact_mod_cast h
  have hterm (j : ℕ) (hj : j < M) : (∫ ω, f j ω ∂μ) = p * ∫ ω, g j ω ∂μ := by
    have h := (hind j hj).measure_inter_preimage_eq_mul {k : ℕ | j < k} {a}
      (Set.to_countable _).measurableSet (measurableSet_singleton a)
    change μ (D j) = μ (C j) * μ {ω | Y j ω = a} at h
    have hr := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_mul] at hr
    change μ.real (D j) = μ.real (C j) * μ.real {ω | Y j ω = a} at hr
    rw [hp j hj] at hr
    calc (∫ ω, f j ω ∂μ) = μ.real (D j) := integral_indicator_one (hD j)
      _ = p * μ.real (C j) := hr.trans (mul_comm _ _)
      _ = _ := congrArg (fun z : ℝ => p * z) (integral_indicator_one (μ := μ) (hC j)).symm
  refine ⟨hfi.congr heF.symm, ?_⟩
  rw [integral_congr_ae heF, integral_congr_ae heG,
    integral_finsetSum _ (fun j _ => hf j), integral_finsetSum _ (fun j _ => hg j), mul_sum]
  exact sum_congr rfl (fun j hj => hterm j (mem_range.mp hj))

end Parking
