/- `prop:oriented-scaling` from the truncated optimal-stopping problems alone.

This is the end of the reduction.  `Parking.oriented_scaling_of_weak_one` takes the whole
frozen proposition down to the weak convergence of the laws of `n^{-1/4} u_n(0)`, and
`Parking.exists_weak_limit_of_cutoff` takes that down to the convergence of the truncated
variables at each fixed spatial cutoff level, which is the level at which the cited stability
estimate of `parking.tex:3199-3203` can be applied at all.  The uniform bound on the means is
the mean bound of `thm:oriented`; the uniform `L¹` smallness of the truncation error as the
cutoff level grows, and the convergence at each fixed level, are what remains to be proved
about the model.
-/
import Parking.Support.WeakLimit

noncomputable section
namespace Parking
open MeasureTheory Filter Topology LatticeProb
open scoped ENNReal NNReal

theorem oriented_scaling_of_cutoff (ν : Measure ℤ) (hν : CriticalLaw ν)
    (Y : ℕ → ℕ → Data 2 → ℝ)
    (hY : ∀ A n, Measurable (Y A n)) (hYi : ∀ A n, Integrable (Y A n) (orientedLaw 2 ν))
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (happ : ∀ A n : ℕ, ∫ w, |(n : ℝ) ^ (-(1 : ℝ) / 4) *
        uOriented (fun y => (w.1 y : ℝ)) n 0 - Y A n w| ∂(orientedLaw 2 ν) ≤ e A)
    (hYconv : ∀ A : ℕ, ∀ f : ℝ → ℝ, (∃ C : ℝ, ∀ x y, dist (f x) (f y) ≤ C) →
      (∃ K, LipschitzWith K f) →
      ∃ c : ℝ, Tendsto (fun n => ∫ w, f (Y A n w) ∂(orientedLaw 2 ν)) atTop (𝓝 c)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
      (Uc : ℝ → Ω → ℝ) (μ : ℝ),
      (∀ T : ℝ, 0 < T → Measurable (Uc T)) ∧
      (∀ T : ℝ, 0 < T → ∀ F : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n : ℕ => ∫ w, F ((n : ℝ) ^ (-(1 : ℝ) / 4) *
              uOriented (fun y => (w.1 y : ℝ)) ⌊(n : ℝ) * T⌋₊ 0)
            ∂(orientedLaw 2 ν)) atTop (𝓝 (∫ ω, F (Uc T ω) ∂Q))) ∧
      (∀ T : ℝ, 0 < T → Q.map (Uc T) = Q.map fun ω => T ^ ((1 : ℝ) / 4) * Uc 1 ω) ∧
      Integrable (Uc 1) Q ∧ μ = ∫ ω, Uc 1 ω ∂Q ∧ 0 < μ ∧
      Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 4) *
        meanuOriented (orientedLaw 2 ν) n) atTop (𝓝 μ) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (orientedLaw 2 ν) := orientedLaw_isProbability (by norm_num) ν
  obtain ⟨C8, _hC8pos, hC8⟩ := exists_rescaled_uOriented_eighth ν hν
  obtain ⟨C1, hC1pos, hC1⟩ := exists_meanuOriented_two_upper ν hν.mean 8 (by norm_num)
    (hν.integrable_rpow (by norm_num))
  have hXm : ∀ n : ℕ, Measurable (fun w : Data 2 => (n : ℝ) ^ (-(1 : ℝ) / 4) *
      uOriented (fun y => (w.1 y : ℝ)) n 0) :=
    fun n => measurable_const.mul ((measurable_uOriented n 0).comp measurable_confReal)
  have hXi : ∀ n : ℕ, Integrable (fun w : Data 2 => (n : ℝ) ^ (-(1 : ℝ) / 4) *
      uOriented (fun y => (w.1 y : ℝ)) n 0) (orientedLaw 2 ν) := fun n => (hC8 n).1
  have hC : ∀ n : ℕ, ∫ w, |(n : ℝ) ^ (-(1 : ℝ) / 4) *
      uOriented (fun y => (w.1 y : ℝ)) n 0| ∂(orientedLaw 2 ν) ≤ C1 := by
    intro n
    have hnn : ∀ w : Data 2, 0 ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) *
        uOriented (fun y => (w.1 y : ℝ)) n 0 :=
      fun w => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (uOriented_nonneg _ n 0)
    have habs : ∫ w, |(n : ℝ) ^ (-(1 : ℝ) / 4) *
        uOriented (fun y => (w.1 y : ℝ)) n 0| ∂(orientedLaw 2 ν)
        = (n : ℝ) ^ (-(1 : ℝ) / 4) * meanuOriented (orientedLaw 2 ν) n := by
      rw [integral_congr_ae (Filter.Eventually.of_forall fun w => abs_of_nonneg (hnn w))]
      rw [integral_const_mul]
      rfl
    rw [habs]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero]
      rw [Real.zero_rpow (by norm_num), zero_mul]
      exact hC1pos.le
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hA : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg hn0.le _
      have hfin : (n : ℝ) ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4) = 1 := by
        rw [← Real.rpow_add hn0]; norm_num
      calc (n : ℝ) ^ (-(1 : ℝ) / 4) * meanuOriented (orientedLaw 2 ν) n
          ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) * (C1 * (n : ℝ) ^ ((1 : ℝ) / 4)) :=
            mul_le_mul_of_nonneg_left (hC1 n hn) hA
        _ = C1 * ((n : ℝ) ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4)) := by ring
        _ = C1 := by rw [hfin, mul_one]
  obtain ⟨L, hL, hone⟩ := exists_weak_limit_of_cutoff (orientedLaw 2 ν) _ Y hXm hY hXi hYi
    hC e he happ hYconv
  exact oriented_scaling_of_weak_one ν hν L hL hone

end Parking
end
