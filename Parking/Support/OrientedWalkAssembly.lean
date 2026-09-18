/- The assembly of `thm:oriented-walk` from its five steps: given the directed
moment inequality of Step 1 (with `kappa` replaced by one), the particle-error
bound of Step 3 and the scaling limit of `prop:oriented-scaling`, the frozen
statement follows. -/
import Parking.Support.OrientedTwoLower
import Parking.Support.OrientedTwoUpper
import Parking.Support.OrientedLogBounds
import Parking.Support.OrientedRatio

noncomputable section
namespace Parking
open MeasureTheory Filter Topology

/-- The assembly of `thm:oriented-walk` from its five steps: given the directed
moment inequality of Step 1 (with `kappa` replaced by one), the particle-error
bound of Step 3 and the scaling limit of `prop:oriented-scaling`, the frozen
statement follows. -/
theorem oriented_walk_of_steps (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hmom : ∀ n : ℕ, 1 ≤ n →
      (∫ ω : Data d, (U ω n 0 : ℝ) ^ (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ) ∂(orientedLaw d ν)) ^
          ((1 : ℝ) / (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ)) ≤
        C₁ * Real.log ((n : ℝ) + 1) +
          C₁ * (Real.sqrt ((2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ) *
            (∫ ω : Data d, (U ω n 0 : ℝ) ^ (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ) ∂(orientedLaw d ν)) ^
              ((1 : ℝ) / (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ))) +
            (2 ⊔ ⌈Real.log ((n : ℝ) + 1)⌉₊ : ℝ)))
    (hmom2 : ∀ n : ℕ, 1 ≤ n →
      (∫ ω : Data 2, (U ω n 0 : ℝ) ^ (8 : ℝ) ∂(orientedLaw 2 ν)) ^ ((1 : ℝ) / 8) ≤
        C₁ * (n : ℝ) ^ ((1 : ℝ) / 4) +
          C₁ * (n : ℝ) ^ ((1 : ℝ) / 8) *
            ((∫ ω : Data 2, (U ω n 0 : ℝ) ^ (8 : ℝ) ∂(orientedLaw 2 ν)) ^ ((1 : ℝ) / 16) + 1))
    (herr : ∀ n : ℕ, 1 ≤ n →
      |meanU (orientedLaw 2 ν) n - meanuOriented (orientedLaw 2 ν) n| ≤
        C₁ * (n : ℝ) ^ ((1 : ℝ) / 8) * Real.log ((n : ℝ) + 1) ^ ((3 : ℝ) / 4))
    (μ : ℝ) (hμ : 0 < μ)
    (hμlim : Tendsto (fun n : ℕ => meanuOriented (orientedLaw 2 ν) n /
      ((n : ℝ) ^ ((1 : ℝ) / 4))) atTop (𝓝 μ))
    (hS : Tendsto (fun t : ℕ => S (orientedLaw 2 ν) t /
      (μ / 4 * (t : ℝ) ^ (-(3 : ℝ) / 4))) atTop (𝓝 1)) :
    (d = 2 → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ meanU (orientedLaw d ν) n ∧
        meanU (orientedLaw d ν) n ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4)) ∧
    (3 ≤ d → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * Real.log n ≤ meanU (orientedLaw d ν) n ∧
        meanU (orientedLaw d ν) n ≤ C * Real.log n) ∧
    (d = 2 →
      Tendsto (fun n : ℕ => meanU (orientedLaw d ν) n /
        meanuOriented (orientedLaw d ν) n) atTop (𝓝 1) ∧
      ∃ μ' : ℝ, 0 < μ' ∧
        Tendsto (fun n : ℕ => meanU (orientedLaw d ν) n /
          (μ' * (n : ℝ) ^ ((1 : ℝ) / 4))) atTop (𝓝 1) ∧
        Tendsto (fun t : ℕ => S (orientedLaw d ν) t /
          (μ' / 4 * (t : ℝ) ^ (-(3 : ℝ) / 4))) atTop (𝓝 1)) := by
  haveI := hν.prob
  obtain ⟨c₂, hc₂, hlo₂⟩ := exists_meanU_oriented_two_lower ν hν
  obtain ⟨c₂', hc₂', hlo₂'⟩ := exists_meanuOriented_two_lower ν hν.nonconst hν.integrable_abs hν.mean
  obtain ⟨C₂, hC₂, hup₂⟩ := meanU_oriented_two_upper_of_moment ν hν C₁ hC₁ hmom2
  have hratio := tendsto_meanU_div_meanuOriented ν hν c₂' C₁ hc₂' (fun n _ => hlo₂' n) herr
  refine ⟨?_, ?_, ?_⟩
  · intro hd2
    subst hd2
    refine ⟨c₂, max c₂ C₂, hc₂, le_max_left _ _, fun n hn => ⟨hlo₂ n, ?_⟩⟩
    have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc meanU (orientedLaw 2 ν) n ≤ C₂ * (n : ℝ) ^ ((1 : ℝ) / 4) := hup₂ n (by omega)
      _ ≤ max c₂ C₂ * (n : ℝ) ^ ((1 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hn0
  · intro hd3
    obtain ⟨c₃, C₃, hc₃, hc₃C₃, hlog⟩ :=
      exists_meanU_oriented_log_bounds d hd3 ν hν C₁ hC₁ hmom
    exact ⟨c₃, C₃, hc₃, hc₃C₃, fun n hn => hlog n hn⟩
  · intro hd2
    subst hd2
    refine ⟨hratio, μ, hμ, ?_, hS⟩
    have h1 : Tendsto (fun n : ℕ => (meanU (orientedLaw 2 ν) n /
        meanuOriented (orientedLaw 2 ν) n) *
        (meanuOriented (orientedLaw 2 ν) n / ((n : ℝ) ^ ((1 : ℝ) / 4)))) atTop (𝓝 (1 * μ)) :=
      hratio.mul hμlim
    rw [one_mul] at h1
    have h2 : Tendsto (fun n : ℕ => (1 / μ) * ((meanU (orientedLaw 2 ν) n /
        meanuOriented (orientedLaw 2 ν) n) *
        (meanuOriented (orientedLaw 2 ν) n / ((n : ℝ) ^ ((1 : ℝ) / 4))))) atTop
        (𝓝 ((1 / μ) * μ)) := h1.const_mul (1 / μ)
    rw [one_div_mul_cancel (ne_of_gt hμ)] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hdpos : meanuOriented (orientedLaw 2 ν) n ≠ 0 := by
      have hpos : 0 < c₂' * (n : ℝ) ^ ((1 : ℝ) / 4) := by
        have : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
        positivity
      exact ne_of_gt (lt_of_lt_of_le hpos (hlo₂' n))
    have hn0 : (n : ℝ) ^ ((1 : ℝ) / 4) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)
    field_simp

end Parking
end
