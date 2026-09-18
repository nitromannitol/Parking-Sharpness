/-
**The optimal-stopping value scales with a positive constant multiple of the reward.**

Needed for the Dynkin-decomposition rescaling of `Parking.u_eq_potential_add_stoppingSup`:
`barDivisible`'s own prefactor `R^{d/2-2}` must be pulled INTO `Parking.stoppingSup`'s reward,
since the value-transfer machine (`Parking.Support.ExtendedMapping.extended_continuous_mapping`)
is applied to the RESCALED reward directly, not to `R^{d/2-2}` times the unscaled value.
-/
import Parking.Support.Terminal
import Parking.Support.ValueLipschitz

open MeasureTheory

noncomputable section

namespace Parking

variable {d : ℕ}

/-- **The expected terminal reward scales linearly with a constant multiple of the
reward.** -/
theorem terminalValue_const_mul (c : ℝ) (F : ℕ → Site d → ℝ) (x : Site d)
    (σ : (ℕ → Fin d × Bool) → ℕ) :
    terminalValue (fun k y => c * F k y) x σ = c * terminalValue F x σ := by
  unfold terminalValue
  exact MeasureTheory.integral_const_mul c _

/-- **The set of terminal values at `c·F` is the image of the set of terminal values at
`F` under multiplication by `c`, for `c ≥ 0`.** -/
theorem terminalValues_const_mul (_hd : 1 ≤ d) {c : ℝ} (_hc : 0 ≤ c) (F : ℕ → Site d → ℝ)
    (n : ℕ) (x : Site d) :
    terminalValues d (fun k y => c * F k y) n x = (fun a => c * a) '' terminalValues d F n x := by
  ext a
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨terminalValue F x σ, ⟨σ, hσ, rfl⟩, (terminalValue_const_mul c F x σ).symm⟩
  · rintro ⟨b, ⟨σ, hσ, rfl⟩, rfl⟩
    exact ⟨σ, hσ, (terminalValue_const_mul c F x σ).symm⟩

/-- **A least upper bound scales with a positive constant multiple.** General purpose, no
content specific to the stopping problem. -/
theorem isLUB_image_const_mul {S : Set ℝ} {v c : ℝ} (hc : 0 < c) (hv : IsLUB S v) :
    IsLUB ((fun a => c * a) '' S) (c * v) := by
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    exact mul_le_mul_of_nonneg_left (hv.1 ha) hc.le
  · intro b hb
    have hbdd : v ≤ b / c := by
      refine hv.2 fun a ha => ?_
      have hab : c * a ≤ b := hb ⟨a, ha, rfl⟩
      rw [le_div_iff₀ hc]
      linarith
    rw [le_div_iff₀ hc] at hbdd
    linarith

/-- **`stoppingSup` scales with a positive constant multiple of a BOUNDED reward.**  The
boundedness hypothesis matches every other fact about `stoppingSup` in this repository
(`Parking.stoppingSup_le`, `Parking.bddAbove_terminalValues`): `Real.sSup` of an unbounded
set is the junk value `0`, so the identity needs a genuine upper bound on `F` to rule out
the junk case for both sides. -/
theorem stoppingSup_const_mul (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) (F : ℕ → Site d → ℝ)
    (n : ℕ) (x : Site d) {M : ℝ} (hbound : ∀ (k : ℕ) (y : Site d), |F k y| ≤ M) :
    stoppingSup d (fun k y => c * F k y) n x = c * stoppingSup d F n x := by
  unfold stoppingSup
  rw [terminalValues_const_mul hd hc.le F n x]
  have hBdd : BddAbove (terminalValues d F n x) := bddAbove_terminalValues hd F n x hbound
  have hLUB : IsLUB (terminalValues d F n x) (sSup (terminalValues d F n x)) :=
    isLUB_csSup (terminalValues_nonempty d F n x) hBdd
  exact (isLUB_image_const_mul hc hLUB).csSup_eq
    ((terminalValues_nonempty d F n x).image _)

end Parking

end
