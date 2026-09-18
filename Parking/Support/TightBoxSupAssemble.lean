/-
Assembles `TightBoxSupBase.lean`/`TightBoxSupBaseMoment.lean`/`TightBoxSupBaseSum.lean`/
`TightBoxSupBaseZero.lean`/`TightBoxSupTailMoment.lean` into a bound, a.e. and for EVERY point
of the cutoff box simultaneously, of `|Yfield|` by a sum of three pieces whose `p`-th moment is
polynomial in the box radius `R`.  The final Lyapunov step is carried out separately
(`TightBoxSupLp.lean`).

The three pieces, combining `Yfield(z)`'s value with `Yfield(dtruncPi R z)` (level-`R`, upward
chain to `Yfield(z)` via `Parking.ae_abs_Yfield_sub_dtruncPi_le`) and with
`Yfield(dtruncPi 0 z)` (level-`0`, downward chain via `Parking.yfield_dtruncPi_dist_le_fixed`):
  |Yfield(z)| ≤ |Yfield(z) - Yfield(dtruncPi R z)| + |Yfield(dtruncPi R z) - Yfield(dtruncPi 0 z)|
              + |Yfield(dtruncPi 0 z)|
            ≤ 2·dtail(levelInc, R) + 2·Σ_{k<R} levelIncFixed(R, k+1) + level0Max(R).
The right side does not depend on `z`, so it bounds the SUPREMUM over the whole box.
-/
import Parking.Support.TightBoxSupBaseSum
import Parking.Support.TightBoxSupBaseZero
import Parking.Support.TightBoxSupTailMoment
import Parking.Support.TightBoxSupTelescope

open MeasureTheory LatticeProb Filter Topology

noncomputable section

namespace Parking

/-- **The sum of the three pieces**, a single nonnegative random variable whose value bounds
`|Yfield(z)|` for every `z` in the box of radius `R`. -/
def yfieldSup3 (A : ℝ) (hA : 0 ≤ A) (R n : ℕ) (η : Site 2 → ℝ) : ℝ :=
  level0Max A hA R n η + 2 * (∑ k ∈ Finset.range R, levelIncFixed A hA R n (k + 1) η) +
    2 * LatticeProb.dtail (fun m => levelInc A hA n m η) R

theorem yfieldSup3_nonneg (A : ℝ) (hA : 0 ≤ A) (R n : ℕ) (η : Site 2 → ℝ) :
    0 ≤ yfieldSup3 A hA R n η := by
  unfold yfieldSup3
  have h1 := level0Max_nonneg A hA R n η
  have h2 : 0 ≤ ∑ k ∈ Finset.range R, levelIncFixed A hA R n (k + 1) η :=
    Finset.sum_nonneg fun k _ => levelIncFixed_nonneg A hA R n (k + 1) η
  have h3 := LatticeProb.dtail_nonneg (fun m => levelInc_nonneg A hA n m η) R
  linarith

/-- **`|Yfield(z)| ≤ yfieldSup3 R`, for a.e. `η`, for EVERY `z` in the box of radius `R`,
uniformly in the scale `n`.** -/
theorem ae_abs_Yfield_le_yfieldSup3 (ν : Measure ℤ) (hν : CriticalLaw ν) {A : ℝ} (hA : 0 ≤ A)
    (n : ℕ) (hn : 1 ≤ n) (R : ℕ) :
    ∀ᵐ η ∂(iidLaw 2 (realLaw ν)), ∀ z : Fin 2 → ℝ, (∀ i, |z i| ≤ (R : ℝ)) →
      |Yfield A hA n η z| ≤ yfieldSup3 A hA R n η := by
  filter_upwards [ae_abs_Yfield_sub_dtruncPi_le ν hν hA n hn R] with η hη z hz
  have hmid := yfield_dtruncPi_dist_le_fixed A hA n η R hz R
  have hzero := abs_Yfield_dtruncPi_zero_le A hA n R η hz
  have hηz := hη z hz
  set a := Yfield A hA n η z with hadef
  set b := Yfield A hA n η (LatticeProb.dtruncPi R z) with hbdef
  set c := Yfield A hA n η (LatticeProb.dtruncPi 0 z) with hcdef
  have htri : |a| ≤ |a - b| + |b - c| + |c| := by
    have h1 : |a - c| ≤ |a - b| + |b - c| := abs_sub_le a b c
    have h2 : |a - 0| ≤ |a - c| + |c - 0| := abs_sub_le a c 0
    simp only [sub_zero] at h2
    linarith
  unfold yfieldSup3
  linarith [htri, hηz, hmid, hzero]

end Parking

end
