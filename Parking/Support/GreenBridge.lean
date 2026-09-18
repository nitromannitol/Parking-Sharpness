/-
The truncated Green function of this repository is the library's.

`Parking.heat` and `Parking.green` were written before the shared library had
the simple random walk, and `LatticeProb.srwHeat` and `LatticeProb.srwGreen`
are the same recursions verbatim, so the two agree definitionally.  Recording
that makes every estimate the library proves for `srwGreen` available to
`lem:gamma-sum` and to `lem:w-martingale` without re-freezing a statement.

Also here: the symmetry of the heat kernel, and the exact form of `Γ_m` in
dimension one, where a site has exactly two neighbours and the variance of
`g_m` at a uniform neighbour is a square of one gradient.
-/
import Parking.Support.Walk
import LatticeProb.Walk.SRW

noncomputable section

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### The bridge -/

theorem heat_eq_srwHeat (d j : ℕ) (x : Site d) : heat d j x = LatticeProb.srwHeat d j x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
      have hfun : heat d j = LatticeProb.srwHeat d j := funext fun y => ih y
      show walkOp (heat d j) x = LatticeProb.srwHeat d (j + 1) x
      rw [hfun, LatticeProb.srwHeat_succ]

theorem green_eq_srwGreen (d m : ℕ) (x : Site d) :
    green d m x = LatticeProb.srwGreen d m x := by
  unfold green LatticeProb.srwGreen
  exact Finset.sum_congr rfl fun j _ => heat_eq_srwHeat d j x

/-! ### The heat kernel is symmetric -/

theorem heat_neg (d j : ℕ) (x : Site d) : heat d j (-x) = heat d j x := by
  induction j generalizing x with
  | zero =>
      show (if -x = 0 then (1 : ℝ) else 0) = if x = 0 then 1 else 0
      by_cases hx : x = 0
      · simp [hx]
      · rw [if_neg (fun hc => hx (by simpa using neg_eq_zero.mp hc)), if_neg hx]
  | succ j ih =>
      show walkOp (heat d j) (-x) = walkOp (heat d j) x
      unfold walkOp nbrSum
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : heat d j (-x + unit i) = heat d j (x - unit i) := by
        rw [show -x + unit i = -(x - unit i) by abel, ih]
      have h2 : heat d j (-x - unit i) = heat d j (x + unit i) := by
        rw [show -x - unit i = -(x + unit i) by abel, ih]
      rw [h1, h2]
      ring

theorem green_neg (d m : ℕ) (x : Site d) : green d m (-x) = green d m x := by
  unfold green
  exact Finset.sum_congr rfl fun j _ => heat_neg d j x

/-! ### Dimension one -/

theorem nbrFinset_one (y : Site 1) : nbrFinset y = {y + unit 0, y - unit 0} := by
  unfold nbrFinset
  rw [show (Finset.univ : Finset (Fin 1)) = {0} from rfl, Finset.singleton_biUnion]

theorem unit_zero_ne (y : Site 1) : y + unit (0 : Fin 1) ≠ y - unit (0 : Fin 1) := by
  intro h
  have := congrFun h 0
  simp [unit, Pi.single_eq_same] at this
  omega

/-- In dimension one the variance of `g_m` at a uniform neighbour of `y` is a
quarter of the square of the gradient across `y`. -/
theorem gamma_one (m : ℕ) (y : Site 1) :
    gamma 1 m y = (green 1 m (y + unit 0) - green 1 m (y - unit 0)) ^ 2 / 4 := by
  have hkern : ∀ z ∈ nbrFinset y, kern 1 y z = 1 / 2 := by
    intro z hz
    rw [kern, if_pos hz]
    norm_num
  have hw : walkOp (green 1 m) y
      = (green 1 m (y + unit 0) + green 1 m (y - unit 0)) / 2 := by
    unfold walkOp nbrSum
    rw [show (Finset.univ : Finset (Fin 1)) = {0} from rfl, Finset.sum_singleton]
    norm_num
  unfold gamma
  rw [Finset.sum_congr rfl fun z hz => by rw [hkern z hz], nbrFinset_one y,
    Finset.sum_pair (unit_zero_ne y), hw]
  ring

theorem gamma_one_zero (m : ℕ) : gamma 1 m 0 = 0 := by
  rw [gamma_one]
  have h : green 1 m ((0 : Site 1) - unit 0) = green 1 m ((0 : Site 1) + unit 0) := by
    rw [show (0 : Site 1) - unit 0 = -((0 : Site 1) + unit 0) by abel, green_neg]
  rw [h]
  ring

end Parking

end
