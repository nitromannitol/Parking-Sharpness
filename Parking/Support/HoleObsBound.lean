/-
The hole count of the range is dominated by the holes present at time zero.

`lem:product` asks that `Z` be integrable (`parking.tex:2321-2332`).  Hole counts
never grow, so the number of unfilled holes of `R_t` at time `t` is at most the
number of holes the initial configuration puts on `R_t`, a finite sum of
`(-\eta(x))^+`; the first moment of the count is what the setting of Section 9
assumes.
-/
import Parking.Support.SurvivorTransfer

noncomputable section

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-- The holes at time zero are the negative part of the configuration. -/
theorem pHoleCount_zero_eq (D : PDriver d) (x : Site d) :
    pHoleCount D 0 x = (-(D.eta x)).toNat := rfl

/-- **`Z` is dominated by the holes the initial configuration puts on the
range.** -/
theorem holeObs_le_initial (w : ℕ → Fin d × Bool) (t : ℕ) (ω : PData d) :
    holeObs w t ω ≤ ∑ x ∈ rangeFinset (0 : Site d) w t, (((-(ω.1 x)).toNat : ℕ) : ℝ) := by
  unfold holeObs
  refine Finset.sum_le_sum fun x _ => ?_
  have hle : pHoleCount (toPDriver ω) t x ≤ ((-(ω.1 x)).toNat : ℕ) := by
    have h0 : pHoleCount (toPDriver ω) 0 x = ((-(ω.1 x)).toNat : ℕ) := rfl
    rw [← h0]
    exact pHoleCount_antitone (toPDriver ω) x (Nat.zero_le t)
  exact_mod_cast hle

end Parking

end
