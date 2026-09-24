/- Exponential moments of the maximum over finitely many time points. -/
import Parking.Support.FinitePathMoment

noncomputable section
namespace Parking
open MeasureTheory Finset

theorem finitePathMax_exponential {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : ℕ → Ω → ℝ) (hm : ∀ j, Measurable (F j))
    (n : ℕ) (τ B : ℝ)
    (hi : ∀ j, j ≤ n → Integrable (fun ω => Real.exp (τ * |F j ω|)) μ)
    (hb : ∀ j, j ≤ n → (∫ ω, Real.exp (τ * |F j ω|) ∂μ) ≤ B) :
    Integrable (fun ω => Real.exp (τ * finitePathMax (fun j => F j ω) n)) μ ∧
      (∫ ω, Real.exp (τ * finitePathMax (fun j => F j ω) n) ∂μ) ≤ ((n : ℝ) + 1) * B := by
  have hsum : Integrable (fun ω => ∑ j ∈ range (n + 1), Real.exp (τ * |F j ω|)) μ := by
    apply integrable_finsetSum
    intro j hj
    exact hi j (by have := mem_range.mp hj; omega)
  have hpt (ω : Ω) : Real.exp (τ * finitePathMax (fun j => F j ω) n) ≤
      ∑ j ∈ range (n + 1), Real.exp (τ * |F j ω|) := by
    obtain ⟨j, hj, he⟩ := exists_mem_eq_sup' (s := range (n + 1)) (by simp)
      (fun j => |F j ω|)
    change (range (n + 1)).sup' (by simp) (fun j => |F j ω|) = |F j ω| at he
    rw [show finitePathMax (fun j => F j ω) n = |F j ω| from he]
    exact single_le_sum (f := fun k => Real.exp (τ * |F k ω|))
      (fun k _ => (Real.exp_pos _).le) hj
  have hMi : Integrable (fun ω => Real.exp (τ * finitePathMax (fun j => F j ω) n)) μ := by
    refine hsum.mono' (((measurable_finitePathMax F hm n).const_mul τ).exp.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hpt ω
  refine ⟨hMi, (integral_mono hMi hsum hpt).trans ?_⟩
  rw [integral_finsetSum _ (fun j hj => hi j (by have := mem_range.mp hj; omega))]
  calc (∑ j ∈ range (n + 1), ∫ ω, Real.exp (τ * |F j ω|) ∂μ) ≤ ∑ _j ∈ range (n + 1), B :=
      sum_le_sum fun j hj => hb j (by have := mem_range.mp hj; omega)
    _ = _ := by simp

end Parking
