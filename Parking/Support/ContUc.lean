/-
**The continuum spatial value field `Uc`**, BP's Lemma 2.5 read at the continuum limit:

    𝒰(s,x) = Z(s,x) + sup_{τ≤s} E_0^{B}[ -Z(s-τ, x+B_τ) ],

for a jointly continuous field `Z` (an instance of `Parking.External.LinearFieldScaling`'s
existential witness) and a `(Fin d → ℝ)`-valued driving process `B` on an independent
probability space, `LatticeProb.IsBrownianSpace d 0 B PB`. This is the discrete
`Parking.u_eq_potential_add_stoppingSup` (`u_n(x) = V_n(x) + sup_{σ≤n} E_x[-V_{n-σ}(X_σ)]`,
`Parking/Support/Terminal.lean`) with the driving walk replaced by Brownian motion and the
linear field `V` replaced by its continuum limit `Z`, matching `parking.tex`'s own frozen
existential clause `Uc`.

The value `Parking.spatialContValue` is built (`Parking/Support/ContSpatialValue.lean`) for a
GENERAL `(Fin d → ℝ)`-valued driving process; this module supplies the reward `Uc` needs and
closes one clause of `Parking.Frozen.spatial_scaling`'s existential in full: `Uc _ 0 _ = 0`
(`Parking.contUc_zero`).

Comparing `contUc` at two nearby points is not a direct application of
`Parking.abs_spatialContValue_sub_le` (`Parking/Support/ContValueLipschitz.lean`): that bound
needs a GLOBAL bound `∀ s y, |G s y| ≤ M` on the reward, but `Uc`'s own reward
`k y ↦ -Z ω' (s-k) (x+y)` reads `Z` at EVERY real `k` (the function type is total, even though
only `k ∈ [0,s]` is read by an admissible rule), and `Z` is only LOCALLY bounded (by continuity),
not globally. The remedy is a cutoff comparison of the kind used for the discrete walk
(`Parking.Support.SpatialStoppingCutoff`): compare `contUc` to a CUTOFF version (reward truncated
outside a compact time-space box) via `abs_spatialContValue_sub_le`, which is then applicable
because the cutoff reward IS globally bounded, and control the cutoff error by the Brownian
motion's OWN exit probability from a growing box (`LatticeProb.brownian_exit_tail_closed`, used
in `Parking/Support/ContSpatialCutoff.lean`).
-/
import Parking.Support.ContSpatialValue
import Parking.Support.ContValueLipschitz

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace Parking

variable {d : ℕ} {Ω' : Type}

/-- **The continuum spatial value field.** `Z`'s own value at `(s,x)` plus the Brownian
optimal-stopping value, at the reward `k y ↦ -Z ω' (s-k) (x+y)`, started at the origin and
bounded by the horizon `s`. -/
def contUc {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → (Fin d → ℝ)) (PB : Measure ΩB)
    (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ) (ω' : Ω') (s : ℝ) (x : Fin d → ℝ) : ℝ :=
  Z ω' s x + spatialContValue B PB (fun k y => -Z ω' (s - k) (x + y)) s

/-- **`Uc _ 0 _ = 0`**, the frozen clause's fourth: at `s = 0`, both `Z`'s own value and the
Brownian optimal-stopping value (whose only admissible rule is the trivial one) vanish. -/
theorem contUc_zero {ΩB : Type*} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → (Fin d → ℝ))
    (PB : Measure ΩB) (Z : Ω' → ℝ → (Fin d → ℝ) → ℝ) (hZ0 : ∀ ω' x, Z ω' 0 x = 0)
    (ω' : Ω') (x : Fin d → ℝ) :
    contUc B PB Z ω' 0 x = 0 := by
  unfold contUc
  rw [hZ0 ω' x]
  have hGzero : ∀ y : Fin d → ℝ, -Z ω' (0 - 0 : ℝ) (x + y) = 0 := by
    intro y; rw [sub_zero, hZ0 ω' (x + y)]; ring
  have hG0 : ∀ y : Fin d → ℝ, (fun k y => -Z ω' (0 - k) (x + y)) 0 y = 0 := hGzero
  rw [spatialContValue_eq_zero_of_zero B PB _ hG0]
  ring

end Parking

end
