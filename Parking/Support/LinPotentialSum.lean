import Parking.Support.LinBox

/-!
# Explicit finite-sum representation of the linear membrane field

`Parking.linPotential η n x` reads only `η` on the box of radius `n` about `x`
(`Parking.linPotential_eq_of_eqOn_box`, `Parking/Support/LinBox.lean`) and responds to a
single unit source exactly by the truncated Green function
(`Parking.linPotential_single`, `Parking/Support/LinPotential.lean`). Combining the two by
linearity (`Parking.linPotential_add`/`_const_mul`) gives the closed form

    V_n(x) = Σ_{z ∈ s} η(z) · g_n(x - z)

for any finite `s` containing the box of radius `n` about `x` — in particular for
`s = boxFinset x n` itself. This is the ingredient needed for the covariance
`Cov(V_n(x), V_m(y))`: expanding the product of two such finite sums and taking expectations
under an i.i.d. law reduces the covariance to a finite bilinear form, which
`LatticeProb.iidLaw_map_restrict`, Mathlib's
`ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral` and
`LatticeProb.tsum_srwGreen_mul_shift` can then close. This module supplies only the
deterministic finite-sum identity.
-/

noncomputable section

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-- **`V` restricted to an indicator-weighted field is the corresponding finite sum of
Green-function translates, over any finite index set.**  The deterministic core of the
closed form, before specializing `s` to a box. -/
theorem linPotential_indicator_eq_sum (η : Site d → ℝ) (s : Finset (Site d)) (n : ℕ)
    (x : Site d) :
    linPotential (fun w => if w ∈ s then η w else 0) n x
      = ∑ z ∈ s, η z * green d n (x - z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero : (fun w : Site d => if w ∈ (∅ : Finset (Site d)) then η w else 0)
          = fun _ => (0 : ℝ) := by
        funext w; simp
      rw [hzero, Finset.sum_empty]
      have h0 : (fun _ : Site d => (0:ℝ)) = fun w => (0:ℝ) * η w := by funext w; ring
      rw [h0, linPotential_const_mul, zero_mul]
  | @insert a t hat ih =>
      have hsplit : (fun w : Site d => if w ∈ insert a t then η w else 0)
          = fun w => (if w = a then η w else 0) + (if w ∈ t then η w else 0) := by
        funext w
        by_cases hwa : w = a
        · subst hwa
          rw [ite_eq_left (Finset.mem_insert_self w t), ite_eq_left rfl]
          by_cases hwt : w ∈ t
          · exact absurd hwt hat
          · rw [ite_eq_right hwt]; ring
        · rw [ite_eq_right hwa]
          by_cases hwt : w ∈ t
          · rw [ite_eq_left (Finset.mem_insert_of_mem hwt), ite_eq_left hwt]; ring
          · rw [ite_eq_right (by simp [Finset.mem_insert, hwa, hwt]), ite_eq_right hwt]; ring
      rw [hsplit, linPotential_add]
      have hsingle : linPotential (fun w => if w = a then η w else 0) n x
          = η a * green d n (x - a) := by
        have heq : (fun w : Site d => if w = a then η w else 0)
            = fun w => η a * (if w = a then (1:ℝ) else 0) := by
          funext w
          by_cases hwa : w = a
          · subst hwa; rw [ite_eq_left rfl, ite_eq_left rfl]; ring
          · rw [ite_eq_right hwa, ite_eq_right hwa]; ring
        rw [heq, linPotential_const_mul, linPotential_single]
      rw [hsingle, ih, Finset.sum_insert hat]

/-- **`V_n(x)` is the explicit finite sum of `η`-weighted Green-function translates over the
box of radius `n` about `x`.** -/
theorem linPotential_eq_sum (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    linPotential η n x = ∑ z ∈ boxFinset x n, η z * green d n (x - z) := by
  rw [← linPotential_extendField_restrict η n x]
  have heq : extendField (boxFinset x n) ((boxFinset x n).restrict η)
      = fun w => if w ∈ boxFinset x n then η w else 0 := by
    funext w
    by_cases hw : w ∈ boxFinset x n
    · simp only [extendField, dite_eq_left hw, Finset.restrict]; rw [ite_eq_left hw]
    · simp only [extendField, dite_eq_right hw]; rw [ite_eq_right hw]
  rw [heq, linPotential_indicator_eq_sum]

/-- **`V_n(x)` is the explicit finite sum over ANY finite index set containing the box of
radius `n` about `x`.** -/
theorem linPotential_eq_sum_of_boxFinset_subset {s : Finset (Site d)} {n : ℕ} {x : Site d}
    (hs : boxFinset x n ⊆ s) (η : Site d → ℝ) :
    linPotential η n x = ∑ z ∈ s, η z * green d n (x - z) := by
  rw [linPotential_eq_extendField_of_boxFinset_subset hs η]
  have heq : extendField s (s.restrict η) = fun w => if w ∈ s then η w else 0 := by
    funext w
    by_cases hw : w ∈ s
    · simp only [extendField, dite_eq_left hw, Finset.restrict]; rw [ite_eq_left hw]
    · simp only [extendField, dite_eq_right hw]; rw [ite_eq_right hw]
  rw [heq, linPotential_indicator_eq_sum]

end Parking

end
