/-
Positive atoms of the initial law and of the direction law.
-/
import Parking.Support.MeanPos
import Parking.Support.AtomUpdate

noncomputable section
namespace Parking
open MeasureTheory
open scoped ENNReal

theorem CriticalLaw.exists_positive_atom {ν : Measure ℤ} (hν : CriticalLaw ν) :
    ∃ k : ℤ, 1 ≤ k ∧ ν {k} ≠ 0 := by
  haveI := hν.prob
  by_contra h
  push Not at h
  have hz : (fun k : ℤ => ((k.toNat : ℕ) : ℝ)) =ᵐ[ν] 0 := by
    apply ae_iff_of_countable.mpr
    intro k hk
    have hk0 : k ≤ 0 := by
      by_contra hn
      exact hk (h k (by omega))
    simp [Int.toNat_of_nonpos hk0]
  have hpos := integral_toNat_pos ν hν.nonconst hν.integrable_abs hν.mean
  rw [integral_congr_ae hz] at hpos
  simp only [Pi.zero_apply, integral_zero] at hpos
  exact (lt_irrefl 0) hpos

theorem stepLaw_singleton_ne_zero {d : ℕ} (a : Fin d × Bool) : stepLaw d {a} ≠ 0 := by
  classical
  simp [stepLaw, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.dirac_apply', ENNReal.mul_eq_top]
end Parking
