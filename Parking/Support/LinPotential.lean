/-
The linear membrane field `V` of the simple random walk (BP eq. 3 and 13 and the
docstring of `Parking/Support/Walk.lean`; `parking.tex` does not name `V`, since
the paper works with `u` directly): `V_0 = 0`, `V_{n+1} = η + PV_n`,
the recursion with the reflection `(\cdot)_+` of the divisible odometer
removed.  Because the recursion has no reflection, `V` is LINEAR in `η`,
exactly, with no one-sided obstruction of the kind present for the nonlinear
odometer `u`: the response of `V_n(x)` to a unit source at `z` is EXACTLY
`green d n (x - z)`, in both directions, not merely bounded by it.
-/
import Parking.Support.Walk
import Parking.Support.GammaSum
import Parking.Support.WBound
import Parking.Support.ErrorUnroll

noncomputable section

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-- The linear membrane field: `V_0 = 0`, `V_{n+1}(x) = η(x) + (PV_n)(x)`. -/
def linPotential {d : ℕ} (η : Site d → ℝ) : ℕ → Site d → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => η x + walkOp (linPotential η n) x

theorem linPotential_zero (η : Site d → ℝ) (x : Site d) : linPotential η 0 x = 0 := rfl

theorem linPotential_succ (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    linPotential η (n + 1) x = η x + walkOp (linPotential η n) x := rfl

/-! ### `walkOp` is additive -/

theorem walkOp_add (f g : Site d → ℝ) (x : Site d) :
    walkOp (fun y => f y + g y) x = walkOp f x + walkOp g x := by
  have h : nbrSum (fun y => f y + g y) x = nbrSum f x + nbrSum g x := by
    unfold nbrSum
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold walkOp
  rw [h, add_div]

theorem walkOp_const_mul (c : ℝ) (f : Site d → ℝ) (x : Site d) :
    walkOp (fun y => c * f y) x = c * walkOp f x := by
  have h : nbrSum (fun y => c * f y) x = c * nbrSum f x := by
    unfold nbrSum
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold walkOp
  rw [h]
  ring

/-! ### `V` is linear in `η` -/

theorem linPotential_add (η ξ : Site d → ℝ) (n : ℕ) (x : Site d) :
    linPotential (fun y => η y + ξ y) n x = linPotential η n x + linPotential ξ n x := by
  induction n generalizing x with
  | zero => simp [linPotential_zero]
  | succ n ih =>
      rw [linPotential_succ, linPotential_succ, linPotential_succ]
      have heq : walkOp (linPotential (fun y => η y + ξ y) n) x
          = walkOp (linPotential η n) x + walkOp (linPotential ξ n) x := by
        rw [show linPotential (fun y => η y + ξ y) n
            = fun x => linPotential η n x + linPotential ξ n x from funext (ih)]
        exact walkOp_add _ _ x
      rw [heq]
      ring

theorem linPotential_const_mul (c : ℝ) (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    linPotential (fun y => c * η y) n x = c * linPotential η n x := by
  induction n generalizing x with
  | zero => simp [linPotential_zero]
  | succ n ih =>
      rw [linPotential_succ, linPotential_succ]
      have heq : walkOp (linPotential (fun y => c * η y) n) x
          = c * walkOp (linPotential η n) x := by
        rw [show linPotential (fun y => c * η y) n = fun x => c * linPotential η n x
          from funext (ih)]
        exact walkOp_const_mul c _ x
      rw [heq]
      ring

theorem linPotential_sub (η ξ : Site d → ℝ) (n : ℕ) (x : Site d) :
    linPotential (fun y => η y - ξ y) n x = linPotential η n x - linPotential ξ n x := by
  have h1 : (fun y => η y - ξ y) = fun y => η y + (fun y => (-1 : ℝ) * ξ y) y := by
    funext y; ring
  rw [h1, linPotential_add, linPotential_const_mul]
  ring

/-! ### The recursion of `green` -/

theorem green_succ (n : ℕ) (y : Site d) :
    green d (n + 1) y = (if y = 0 then (1 : ℝ) else 0) + walkOp (green d n) y := by
  show (∑ j ∈ Finset.range (n + 1), heat d j y) = _
  rw [Finset.sum_range_succ']
  have hop : ∀ j, heat d (j + 1) = walkOp (heat d j) := fun j => rfl
  have hsum : (∑ j ∈ Finset.range n, heat d (j + 1) y) = walkOp (green d n) y := by
    have heq : (∑ j ∈ Finset.range n, heat d (j + 1) y)
        = (∑ j ∈ Finset.range n, walkOp (heat d j) y) :=
      Finset.sum_congr rfl fun j _ => by rw [hop]
    rw [heq]
    have hws := congrFun (walkOp_sum (Finset.range n) (heat d)) y
    rw [← hws]
    rfl
  rw [hsum]
  have h0 : heat d 0 y = if y = 0 then (1:ℝ) else 0 := rfl
  rw [h0]
  ring

/-! ### The exact response of `V` to a unit source -/

theorem linPotential_single (n : ℕ) (z x : Site d) :
    linPotential (fun w => if w = z then (1 : ℝ) else 0) n x = green d n (x - z) := by
  induction n generalizing x with
  | zero => rw [linPotential_zero]; simp [green]
  | succ n ih =>
      rw [linPotential_succ, green_succ]
      have heq : walkOp (linPotential (fun w => if w = z then (1:ℝ) else 0) n) x
          = walkOp (fun w => green d n (w - z)) x := by
        congr 1
        exact funext ih
      rw [heq]
      have hshift : walkOp (fun w => green d n (w - z)) x = walkOp (green d n) (x - z) := by
        have h := walkOp_shift (-z) (green d n) x
        simpa only [sub_eq_add_neg] using h
      rw [hshift]
      by_cases hxz : x = z
      · rw [if_pos hxz, if_pos (by rw [hxz]; abel)]
      · rw [if_neg hxz, if_neg (fun hc => hxz (sub_eq_zero.mp hc))]

/-- **The exact coordinatewise sensitivity of `V`.**  Changing `η` at one site
`z` by `δ` changes `V_n(x)` by EXACTLY `δ * green d n (x - z)`: no one-sided
obstruction, unlike the nonlinear odometer `u`. -/
theorem linPotential_update (η : Site d → ℝ) (n : ℕ) (x z : Site d) (v : ℝ) :
    linPotential (Function.update η z v) n x - linPotential η n x
      = (v - η z) * green d n (x - z) := by
  have hdiff : (Function.update η z v) = fun w => η w + (v - η z) * (if w = z then (1:ℝ) else 0) := by
    funext w
    by_cases hw : w = z
    · subst hw; simp [Function.update_self]
    · simp [hw]
  rw [hdiff]
  have hfun : (fun w => η w + (v - η z) * (if w = z then (1:ℝ) else 0))
      = fun w => η w + (fun w => (v - η z) * (if w = z then (1:ℝ) else 0)) w := rfl
  rw [hfun, linPotential_add, linPotential_const_mul, linPotential_single]
  ring

end Parking

end
