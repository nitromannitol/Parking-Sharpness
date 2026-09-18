/-
**Translation covariance of the divisible sandpile odometer, and shift-invariance in
law of the discrepancy `U_n - u_n` between the particle and divisible odometers.**

`Parking.U_shiftData` (`Parking/Support/Equivariance.lean`) already gives the particle
odometer's translation covariance, `U (shiftData v ω) n x = U ω n (x + v)`.  This file
proves the analogous fact for the divisible odometer `u`/`uOf` (a short induction on
`n` through `walkOp`'s own translation covariance, since `u`'s recursion is built from
`walkOp` alone), and combines the two with `Parking.law_map_shiftData` (the pushforward
invariance of the i.i.d. law under a spatial shift) to show that the LAW of the
discrepancy `U_n(z) - u_n(z)` does not depend on the site `z`.  This is the ingredient
for transferring the SEALED `prop:discrepancy` (a bound at the single site `0`) to a bound
at every site of a mesh, via a union bound, towards the vanishing-distance clause of
`prop:spatial-scaling`.
-/
import Parking.Support.Equivariance
import Parking.Support.DiscrepancyTail
import Parking.Support.WBound
import Parking.Support.UBound

noncomputable section

namespace Parking

open LatticeProb MeasureTheory

variable {d : ℕ}

/-! ### Translation covariance of the divisible odometer, from `walkOp`'s (`WBound.lean`) -/

/-- **`u`'s recursion is translation covariant.**  `u (η ∘ (· + v)) n x = u η n (x + v)`,
by induction on `n` through `walkOp_shift`. -/
theorem u_shift_real (v : Site d) (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    u (fun y => η (y + v)) n x = u η n (x + v) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      show max 0 ((fun y => η (y + v)) x + walkOp (u (fun y => η (y + v)) n) x)
        = max 0 (η (x + v) + walkOp (u η n) (x + v))
      have hop : walkOp (u (fun y => η (y + v)) n) x = walkOp (u η n) (x + v) := by
        rw [← walkOp_shift v (u η n) x]
        congr 1
        exact funext fun y => ih y
      rw [hop]

/-- **`uOf`'s translation covariance for a shifted realization.** -/
theorem uOf_shiftData (v : Site d) (ω : Data d) (n : ℕ) (x : Site d) :
    uOf (shiftData v ω) n x = uOf ω n (x + v) := by
  unfold uOf
  have hconf : (fun y => (((shiftData v ω).1 y : ℤ) : ℝ)) = fun y => ((ω.1 (y + v) : ℤ) : ℝ) := by
    funext y
    rw [shiftData_eq_prodMap]
    rfl
  rw [hconf]
  exact u_shift_real v (fun y => ((ω.1 y : ℤ) : ℝ)) n x

/-! ### The discrepancy at a shifted site, pathwise -/

/-- **The discrepancy at `x + v` under `ω` is the discrepancy at `x` under the
`v`-shifted realization.** -/
theorem discrepancy_shiftData (v : Site d) (ω : Data d) (n : ℕ) (x : Site d) :
    (U ω n (x + v) : ℝ) - uOf ω n (x + v)
      = (U (shiftData v ω) n x : ℝ) - uOf (shiftData v ω) n x := by
  rw [U_shiftData, uOf_shiftData]

/-! ### Shift-invariance in law of the discrepancy event -/

/-- **The law of the discrepancy `|U_n(z) - u_n(z)|` does not depend on the site `z`.**
Combines `discrepancy_shiftData` with the pushforward invariance of the i.i.d. law under
a spatial shift, `Parking.law_map_shiftData`. -/
theorem law_discrepancy_shift (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (z : Site d) (n : ℕ) (r : ℝ) :
    (law d ν) {ω | r < |(U ω n z : ℝ) - uOf ω n z|}
      = (law d ν) {ω | r < |(U ω n (0 : Site d) : ℝ) - uOf ω n (0 : Site d)|} := by
  have hz : z = (0 : Site d) + z := by abel
  have hmeasT : MeasurableSet {ω : Data d | r < |(U ω n (0 : Site d) : ℝ) - uOf ω n (0 : Site d)|} :=
    measurableSet_lt measurable_const
      ((((measurable_from_countable' (fun k : ℕ => (k : ℝ))).comp
        (measurable_U n (0 : Site d))).sub (measurable_uOf n (0 : Site d))).abs)
  have hset : {ω : Data d | r < |(U ω n z : ℝ) - uOf ω n z|}
      = (shiftData z) ⁻¹' {ω : Data d | r < |(U ω n (0 : Site d) : ℝ) - uOf ω n (0 : Site d)|} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    conv_lhs => rw [hz, discrepancy_shiftData]
  rw [hset, ← Measure.map_apply (measurable_shiftData z) hmeasT, law_map_shiftData hd ν z]

end Parking

end
