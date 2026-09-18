/-
The reduction of `happ` from a pathwise maximal inequality to a box-supremum moment bound.

`happ` reduces to a bound on `E_{η,p}[max_{k≤n} |G_Y(k, orientedPath 0 p k)|^2]`, the CLAMPED
reward read along the walk's own random trajectory, uniform in `n`.  This module proves the
trivial half of that reduction: since `G_Y(k, z) := Parking.rewardOfBox
hT hA G (k/n) (Parking.orientedScaledSite n z)` is, for EVERY `k` and `z` (not just those the
walk visits), the value of the SAME `G : C(Parking.rewardBox T A, ℝ)` at a point of the box, it is
bounded by `‖G‖` UNCONDITIONALLY (`Parking.abs_rewardOfBox_le`) — the walk's own trajectory plays
no role at all in this half.  So the pathwise maximum is bounded by `‖G‖`, and the remaining
content is entirely the DETERMINISTIC, `p`-independent bound `E_η[‖G_n η‖^2]` uniform in `n`
(`Parking/Support/TightBoxSupMoment.lean`).
-/
import Parking.Support.TightBoxLaw
import Parking.Support.OrientedCutoffValue

open MeasureTheory LatticeProb

noncomputable section

namespace Parking

/-- **The clamped reward, read at ANY space-time point, is bounded by the norm of the box
reward.**  In particular this holds along the walk's own trajectory, uniformly over the walk's
own randomness `p` — the trajectory plays no role in this bound at all. -/
theorem abs_rewardOfBox_orientedScaledSite_le {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A)
    (G : C(rewardBox T A, ℝ)) (n : ℕ) (k : ℕ) (z : Site 2) :
    |rewardOfBox hT hA G ((k : ℝ) / n) (orientedScaledSite n z)| ≤ ‖G‖ :=
  abs_rewardOfBox_le hT hA G _ _

/-- **The pathwise maximum of the clamped reward along the walk's own trajectory, at every
time `k ≤ n` and every driving sequence `p`, is bounded by `‖G‖`.**  This is the trivial half of
the reduction of `happ`: the deterministic supremum of `G` over the whole box dominates the
pathwise maximum, with no probability and no walk-specific argument needed. -/
theorem sup'_abs_rewardOfBox_orientedPath_le {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A)
    (G : C(rewardBox T A, ℝ)) (n : ℕ) (p : ℕ → Fin 2 × Bool) :
    (Finset.range (n + 1)).sup'
      (Finset.nonempty_range_add_one)
      (fun k => |rewardOfBox hT hA G ((k : ℝ) / n)
        (orientedScaledSite n (orientedPath (0 : Site 2) p k))|) ≤ ‖G‖ :=
  Finset.sup'_le _ _ fun k _ =>
    abs_rewardOfBox_orientedScaledSite_le hT hA G n k (orientedPath (0 : Site 2) p k)

/-- **Hence the squared pathwise maximum is bounded by `‖G‖ ^ 2`, pointwise in `η` and `p`.**
Integrating over the walk's own randomness `p` (and, separately, over the scenery `η`) is
therefore reduced entirely to bounding `E_η[‖G_n η‖^2]`, the content of
`Parking.exists_boxRewardMap_norm_sq_moment`. -/
theorem sq_sup'_abs_rewardOfBox_orientedPath_le {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A)
    (G : C(rewardBox T A, ℝ)) (n : ℕ) (p : ℕ → Fin 2 × Bool) :
    ((Finset.range (n + 1)).sup'
      (Finset.nonempty_range_add_one)
      (fun k => |rewardOfBox hT hA G ((k : ℝ) / n)
        (orientedScaledSite n (orientedPath (0 : Site 2) p k))|)) ^ 2 ≤ ‖G‖ ^ 2 := by
  have hnn : (0 : ℝ) ≤ (Finset.range (n + 1)).sup'
      (Finset.nonempty_range_add_one)
      (fun k => |rewardOfBox hT hA G ((k : ℝ) / n)
        (orientedScaledSite n (orientedPath (0 : Site 2) p k))|) :=
    le_trans (abs_nonneg _) (Finset.le_sup'
      (f := fun k : ℕ => |rewardOfBox hT hA G ((k : ℝ) / n)
        (orientedScaledSite n (orientedPath (0 : Site 2) p k))|)
      (Finset.self_mem_range_succ n))
  exact pow_le_pow_left₀ hnn (sup'_abs_rewardOfBox_orientedPath_le hT hA G n p) 2

end Parking

end
