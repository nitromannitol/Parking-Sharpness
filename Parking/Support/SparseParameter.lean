/- A positive sparse comparison parameter for every centered nonconstant integer law. -/
import Parking.Support.IntegerSparseComparison
import Parking.Support.MasterChain

noncomputable section
namespace Parking
open MeasureTheory LatticeProb

theorem measure_positive_integers_pos (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hnc : ∀ k : ℤ, ν {k} ≠ 1) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k : ℤ, (k : ℝ) ∂ν = 0) : 0 < ν.real {k : ℤ | 1 ≤ k} := by
  have hpos := integral_toNat_pos ν hnc hint hmean
  have hν : ν {k : ℤ | 1 ≤ k} ≠ 0 := by
    intro hz
    have he : (fun k : ℤ => ((k.toNat : ℕ) : ℝ)) =ᵐ[ν] 0 := by
      apply ae_iff_of_countable.mpr
      intro k hk
      have hkn : ¬1 ≤ k := by
        intro h
        have hle := measure_mono (μ := ν) (show ({k} : Set ℤ) ⊆ {k : ℤ | 1 ≤ k} by simpa using h)
        exact hk (le_zero_iff.mp (hle.trans_eq hz))
      simp only [Pi.zero_apply, Int.toNat_of_nonpos (show k ≤ 0 by omega), Nat.cast_zero]
    rw [integral_congr_ae he] at hpos
    simp only [Pi.zero_apply, integral_zero] at hpos
    exact (lt_irrefl 0) hpos
  exact ENNReal.toReal_pos hν (measure_ne_top _ _)

theorem exists_sparse_comparison_parameter (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hnc : ∀ k : ℤ, ν {k} ≠ 1) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k : ℤ, (k : ℝ) ∂ν = 0) :
    ∃ p : ℝ, 0 < p ∧ 2 * p ≤ 1 ∧ p ≤ ν.real {k : ℤ | 1 ≤ k} := by
  have hp := measure_positive_integers_pos ν hnc hint hmean
  refine ⟨ν.real {k : ℤ | 1 ≤ k} / 2, by positivity, ?_, by linarith⟩
  have hle : ν.real {k : ℤ | 1 ≤ k} ≤ 1 := measureReal_le_one
  linarith

end Parking
