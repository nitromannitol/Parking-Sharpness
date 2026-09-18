/-
Locality and finite-dimensional regularity of the linear membrane field `V`
(`Parking.linPotential`), needed to apply the shared library's weighted
exponential concentration (`LatticeProb.weighted_exp_conc_tail`) to a
two-point, two-time increment of `V`.

`Parking.linPotential_eq_of_eqOn_box` is `Parking.u_eq_of_eqOn_box`
(`Parking/Support/UFinite.lean`) without the reflection: `V_n(x)` reads only
the field on the box of radius `n` about `x`, by the same induction on the
neighbour recursion.  `Parking.abs_linPotential_le` is the un-reflected
analogue of `Parking.u_le_mul_of_le`, giving a crude but sufficient Lipschitz
bound on `V` as a function of a finite restriction of the field, exactly as
`Parking.lipschitzWith_u_extendField` does for `u`.  `Parking.extendField_update`
identifies updating a finite field with updating its zero-extension, so that
`Parking.linPotential_update`'s EXACT one-coordinate response transports to
the finite-dimensional field with no loss.
-/
import Parking.Support.LinPotential
import Parking.Support.UFinite

noncomputable section

namespace Parking

open LatticeProb Finset
open scoped NNReal

variable {d : ℕ}

/-! ### `V` reads only the box -/

/-- **`V` reads only the time-radius box.**  The un-reflected analogue of
`Parking.u_eq_of_eqOn_box`. -/
theorem linPotential_eq_of_eqOn_box {η ξ : Site d → ℝ} (n : ℕ) (x : Site d)
    (heq : ∀ y ∈ boxFinset x n, η y = ξ y) : linPotential η n x = linPotential ξ n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have hx : x ∈ boxFinset x (n + 1) := mem_boxFinset_iff.mpr (fun i => by simp; positivity)
      have hnbr : ∀ y ∈ nbrFinset x, linPotential η n y = linPotential ξ n y := by
        intro y hy
        apply ih y
        intro z hz
        apply heq z
        have h := mem_boxFinset_add (nbrFinset_subset_box x hy) hz
        simpa only [Nat.add_comm 1 n] using h
      have hw : walkOp (linPotential η n) x = walkOp (linPotential ξ n) x := by
        unfold walkOp nbrSum
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [hnbr _ (mem_nbrFinset_add x i), hnbr _ (mem_nbrFinset_sub x i)]
      show η x + walkOp (linPotential η n) x = ξ x + walkOp (linPotential ξ n) x
      rw [heq x hx, hw]

/-- Restriction to the time-radius box preserves `V`. -/
theorem linPotential_extendField_restrict (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    linPotential (extendField (boxFinset x n) ((boxFinset x n).restrict η)) n x
      = linPotential η n x :=
  linPotential_eq_of_eqOn_box n x (fun _ hy => extendField_restrict _ _ hy)

/-- `V` at `x` and horizon `n` is unchanged by restricting the field to any finite set
containing the box of radius `n` about `x`. -/
theorem linPotential_eq_extendField_of_boxFinset_subset {s : Finset (Site d)} {n : ℕ} {x : Site d}
    (hs : boxFinset x n ⊆ s) (η : Site d → ℝ) :
    linPotential η n x = linPotential (extendField s (s.restrict η)) n x :=
  linPotential_eq_of_eqOn_box n x (fun _ hy => (extendField_restrict s η (hs hy)).symm)

/-! ### A crude but sufficient Lipschitz bound -/

/-- A uniform field bound bounds `V`, by the un-reflected recursion (the analogue of
`Parking.u_le_mul_of_le`). -/
theorem abs_linPotential_le (hd : 1 ≤ d) {ζ : Site d → ℝ} {B : ℝ}
    (_hB : 0 ≤ B) (hζ : ∀ y, |ζ y| ≤ B) (n : ℕ) (x : Site d) :
    |linPotential ζ n x| ≤ n * B := by
  induction n generalizing x with
  | zero => simp [linPotential_zero]
  | succ n ih =>
      rw [linPotential_succ]
      have hub : walkOp (linPotential ζ n) x ≤ walkOp (fun _ => (n : ℝ) * B) x :=
        walkOp_mono hd (fun y => (abs_le.mp (ih y)).2) x
      have hlb : walkOp (fun _ => -((n : ℝ) * B)) x ≤ walkOp (linPotential ζ n) x :=
        walkOp_mono hd (fun y => (abs_le.mp (ih y)).1) x
      rw [walkOp_const hd] at hub
      rw [walkOp_const hd] at hlb
      have hζx := abs_le.mp (hζ x)
      rw [abs_le]
      constructor
      · push_cast; nlinarith [hζx.1, hlb]
      · push_cast; nlinarith [hζx.2, hub]

/-- A uniform field perturbation gives a linear-in-time `V`-perturbation, from the exact
linearity `Parking.linPotential_sub`. -/
theorem abs_linPotential_sub_le (hd : 1 ≤ d) {ζ ξ : Site d → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hζξ : ∀ y, |ζ y - ξ y| ≤ B) (n : ℕ) (x : Site d) :
    |linPotential ζ n x - linPotential ξ n x| ≤ n * B := by
  rw [← linPotential_sub]
  exact abs_linPotential_le hd hB hζξ n x

/-- **`V` at a finite field is Lipschitz**, with constant equal to the horizon: the same crude
bound `Parking.lipschitzWith_u_extendField` gives for `u`. -/
theorem lipschitzWith_linPotential_extendField (hd : 1 ≤ d) (s : Finset (Site d)) (n : ℕ)
    (x : Site d) :
    LipschitzWith (n : ℝ≥0) (fun ζ : s → ℝ => linPotential (extendField s ζ) n x) := by
  apply LipschitzWith.of_dist_le_mul
  intro ζ ξ
  simp only [Real.dist_eq, NNReal.coe_natCast]
  apply abs_linPotential_sub_le hd dist_nonneg
  intro y
  by_cases hy : y ∈ s
  · simp only [extendField, dif_pos hy]
    exact dist_le_pi_dist ζ ξ ⟨y, hy⟩
  · simp [extendField, hy]

/-! ### Updating a finite field is updating its zero-extension -/

/-- Updating a finite field at one coordinate is updating its zero-extension at the
corresponding site. -/
theorem extendField_update {s : Finset (Site d)} (ζ : s → ℝ) (i : s) (v : ℝ) :
    extendField s (Function.update ζ i v) = Function.update (extendField s ζ) (i : Site d) v := by
  funext w
  by_cases hw : w = (i : Site d)
  · subst hw
    rw [Function.update_self]
    simp only [extendField, dif_pos i.2]
    exact Function.update_self i v ζ
  · rw [Function.update_of_ne hw]
    by_cases hws : w ∈ s
    · simp only [extendField, dif_pos hws]
      rw [Function.update_of_ne]
      intro hcontra
      exact hw (congrArg Subtype.val hcontra)
    · simp [extendField, hws]

end Parking

end
