import Parking.Support.MeanPos
import Parking.Support.AtomUpdate

/-!
# Positive atoms of the initial and direction laws

This file proves two positivity results used elsewhere in the parking construction.
`CriticalLaw.exists_positive_atom` shows that a one-site law satisfying `CriticalLaw`
(integer-valued, nonconstant, mean zero, with an exponential moment) must place positive
mass on some strictly positive integer, by combining `integral_toNat_pos` with the fact
that a law supported entirely on nonpositive integers would force the mean of its
positive part to vanish. `stepLaw_singleton_ne_zero` shows that the uniform law on signed
lattice directions gives every singleton direction a nonzero mass.
-/

noncomputable section
namespace Parking
open MeasureTheory
open scoped ENNReal

/-- A `CriticalLaw` puts positive mass on some strictly positive integer `k`, since
otherwise `k.toNat` would vanish `ν`-a.e., contradicting `integral_toNat_pos`. -/
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

/-- Every singleton `{a}` of a signed lattice direction carries nonzero mass under the
uniform direction law `stepLaw`, since `stepLaw` is a positive scalar multiple of a sum
of Dirac masses including the one at `a`. -/
theorem stepLaw_singleton_ne_zero {d : ℕ} (a : Fin d × Bool) : stepLaw d {a} ≠ 0 := by
  classical
  simp [stepLaw, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.dirac_apply', ENNReal.mul_eq_top]
end Parking
