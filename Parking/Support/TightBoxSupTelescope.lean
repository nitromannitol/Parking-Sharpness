/-
The telescoping assembly: it connects the dyadic-level moment bounds of
`TightBoxSupTail.lean`/`TightBoxSupChain.lean` to the ACTUAL VALUE of `Parking.Yfield` at every
point, via the shared library's deterministic chaining lemmas
`LatticeProb.dlimPi_sub_dtruncPi_le` (which needs exactly the a.e. summability
`Parking.ae_summable_levelInc` supplies) and `LatticeProb.dlimPi_eq_of_continuous` (which
identifies the chained limit with `Yfield`'s own value, since `Parking.continuous_Yfield` is
already proved).
-/
import Parking.Support.TightBoxSupChain

open MeasureTheory LatticeProb Filter Topology

noncomputable section

namespace Parking

/-- **The value of `Yfield` at any point within the level-`n1` box is within `2 · dtail(levelInc,
n1)` of its own level-`n1` dyadic truncation, for a.e. scenery, uniformly in the scale `n`.** -/
theorem ae_abs_Yfield_sub_dtruncPi_le (ν : Measure ℤ) (hν : CriticalLaw ν) {A : ℝ} (hA : 0 ≤ A)
    (n : ℕ) (hn : 1 ≤ n) (n1 : ℕ) :
    ∀ᵐ η ∂(iidLaw 2 (realLaw ν)), ∀ z : Fin 2 → ℝ, (∀ i, |z i| ≤ (n1 : ℝ)) →
      |Yfield A hA n η z - Yfield A hA n η (LatticeProb.dtruncPi n1 z)| ≤
        2 * LatticeProb.dtail (fun m => levelInc A hA n m η) n1 := by
  filter_upwards [ae_summable_levelInc ν hν hA n hn n1] with η hsummable z hz
  have hb := dyadicIncBoundPi_Yfield A hA n η
  have key := LatticeProb.dlimPi_sub_dtruncPi_le hb (fun m => levelInc_nonneg A hA n m η)
    hsummable (Nat.zero_le n1) hz
  rwa [LatticeProb.dlimPi_eq_of_continuous (continuous_Yfield hA n η) z] at key

end Parking

end
