import Parking.Support.IntegerSparseComparison
import Parking.Support.MasterChain

/-!
# A sparse comparison parameter for centered nonconstant integer laws

A positive sparse comparison parameter for every centered nonconstant integer law. This
file shows every centered, nonconstant, integrable integer law puts positive mass on the
positive integers, and extracts from this a positive `p ≤ 1/2` bounded above by that mass,
serving as a sparse three-point comparison parameter.
-/

noncomputable section
namespace Parking
open MeasureTheory LatticeProb

/-- Every centered, nonconstant, integrable integer law `ν` places positive mass on the
positive integers, since otherwise the mean-zero condition would force the negative part
of the identity to have zero integral as well. -/
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

/-- Every centered, nonconstant, integrable integer law `ν` admits a comparison parameter
`p` with `0 < p`, `2p ≤ 1`, and `p` no greater than the mass `ν` places on the positive
integers, obtained by halving that positive mass. -/
theorem exists_sparse_comparison_parameter (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hnc : ∀ k : ℤ, ν {k} ≠ 1) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k : ℤ, (k : ℝ) ∂ν = 0) :
    ∃ p : ℝ, 0 < p ∧ 2 * p ≤ 1 ∧ p ≤ ν.real {k : ℤ | 1 ≤ k} := by
  have hp := measure_positive_integers_pos ν hnc hint hmean
  refine ⟨ν.real {k : ℤ | 1 ≤ k} / 2, by positivity, ?_, by linarith⟩
  have hle : ν.real {k : ℤ | 1 ≤ k} ≤ 1 := measureReal_le_one
  linarith

end Parking
