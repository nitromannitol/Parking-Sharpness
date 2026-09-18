/-
The growth corollary: mean estimates, the activity mass-transport identity,
and monotonicity of survivor density.
-/
import Parking.Support.GrowthMeans
import Parking.Support.GrowthSequence
import Parking.Support.DensitySequence

noncomputable section
namespace Parking
open MeasureTheory Filter

/-- The power and logarithmic bounds on both cumulative and current activity. -/
theorem growth_of_master (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration)
    (hGreenNorms : Parking.External.GreenNorms)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν) :
    (d ≤ 3 → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      (∀ n : ℕ, 2 ≤ n →
        c * (n : ℝ) ^ ((4 - (d : ℝ)) / 4) ≤ meanU (law d ν) n ∧
          meanU (law d ν) n ≤ C * (n : ℝ) ^ ((4 - (d : ℝ)) / 4)) ∧
      (∀ t : ℕ,
        c * ((t : ℝ) + 1) ^ (-((d : ℝ) / 4)) ≤ S (law d ν) t ∧
          S (law d ν) t ≤ C * ((t : ℝ) + 1) ^ (-((d : ℝ) / 4)))) ∧
    (4 ≤ d → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      (∀ n : ℕ, 2 ≤ n →
        c * Real.log n ≤ meanU (law d ν) n ∧
          meanU (law d ν) n ≤ C * Real.log n) ∧
      (∀ t : ℕ,
        c / ((t : ℝ) + 1) ≤ S (law d ν) t ∧
          S (law d ν) t ≤ C * Real.log ((t : ℝ) + 2) / ((t : ℝ) + 1))) := by
  haveI := hν.prob
  have hint := hν.integrable_abs
  have hdec := S_antitone hd ν hint
  have hpos : ∀ t : ℕ, 0 ≤ S (law d ν) t := fun t => S_nonneg _ t
  have hsum := (Parking.Frozen.transport d hd ν hν.prob hint).2.1
  have hmeans := meanU_growth hGrowth hBernstein hConcentration hGreenNorms d hd ν hν
  constructor
  · intro hd3
    obtain ⟨a, A, ha, hA, hm⟩ := hmeans.1 hd3
    have hβ : 0 < (4 - (d : ℝ)) / 4 := by
      have : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
      linarith
    have hβ1 : (4 - (d : ℝ)) / 4 ≤ 1 := by
      have := Nat.cast_nonneg (α := ℝ) d
      linarith
    obtain ⟨b, B, hb, _hB, hf⟩ := antitone_power_bounds (S (law d ν)) hdec hpos
      hβ hβ1 ha hA (fun n hn => by rw [← hsum n]; exact hm n hn)
    have hexp : (4 - (d : ℝ)) / 4 - 1 = -((d : ℝ) / 4) := by ring
    simp only [hexp] at hf
    refine ⟨min a b, max (max A B) (min a b), lt_min ha hb, le_max_right _ _, ?_, ?_⟩
    · intro n hn
      have hn0 : 0 ≤ (n : ℝ) ^ ((4 - (d : ℝ)) / 4) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      exact ⟨(mul_le_mul_of_nonneg_right (min_le_left a b) hn0).trans (hm n hn).1,
        (hm n hn).2.trans (mul_le_mul_of_nonneg_right
          ((le_max_left A B).trans (le_max_left _ _)) hn0)⟩
    · intro t
      have ht0 : 0 ≤ ((t : ℝ) + 1) ^ (-((d : ℝ) / 4)) := Real.rpow_nonneg (by positivity) _
      exact ⟨(mul_le_mul_of_nonneg_right (min_le_right a b) ht0).trans (hf t).1,
        (hf t).2.trans (mul_le_mul_of_nonneg_right
          ((le_max_right A B).trans (le_max_left _ _)) ht0)⟩
  · intro hd4
    obtain ⟨a, A, ha, hA, hm⟩ := hmeans.2 hd4
    obtain ⟨B, _hB, hu⟩ := antitone_log_upper (S (law d ν)) hdec hA
      (fun n hn => by rw [← hsum n]; exact (hm n hn).2)
    obtain ⟨c₀, hc₀, hcd⟩ := Parking.Frozen.critical_density
    obtain ⟨b, hb, hl⟩ := antitone_reciprocal_lower (S (law d ν)) hdec hpos hc₀
      (hcd d hd ν hν.prob hν.nonconst hint hν.mean).1
    refine ⟨min a b, max (max A B) (min a b), lt_min ha hb, le_max_right _ _, ?_, ?_⟩
    · intro n hn
      have hn0 : 0 ≤ Real.log n := (log_pos_of_two_le hn).le
      exact ⟨(mul_le_mul_of_nonneg_right (min_le_left a b) hn0).trans (hm n hn).1,
        (hm n hn).2.trans (mul_le_mul_of_nonneg_right
          ((le_max_left A B).trans (le_max_left _ _)) hn0)⟩
    · intro t
      have ht0 : 0 ≤ (t : ℝ) + 1 := by positivity
      have hl0 : 0 ≤ Real.log ((t : ℝ) + 2) := by
        apply Real.log_nonneg
        have := Nat.cast_nonneg (α := ℝ) t
        linarith
      exact ⟨(div_le_div_of_nonneg_right (min_le_right a b) ht0).trans (hl t),
        (hu t).trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          ((le_max_right A B).trans (le_max_left _ _)) hl0) ht0)⟩
end Parking
