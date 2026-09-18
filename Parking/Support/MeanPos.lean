/-
Positive mean odometers at every positive horizon.
-/
import Parking.Support.MasterChain
import Parking.Support.DensitySequence

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

theorem u_real_nonneg (η : Site d → ℝ) (n : ℕ) (x : Site d) : 0 ≤ u η n x := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

/-- The divisible odometer increases with the time horizon. -/
theorem u_monotone_time (hd : 1 ≤ d) (η : Site d → ℝ) (x : Site d) :
    Monotone (fun n : ℕ => u η n x) := by
  have hs : ∀ n : ℕ, ∀ y, u η n y ≤ u η (n + 1) y := by
    intro n
    induction n with
    | zero => exact fun y => u_real_nonneg η 1 y
    | succ n ih =>
        intro y
        change max 0 (η y + walkOp (u η n) y) ≤ max 0 (η y + walkOp (u η (n + 1)) y)
        exact max_le_max le_rfl (add_le_add_right (walkOp_mono hd ih y) _)
  exact monotone_nat_of_le_succ (fun n => hs n x)

/-- The two odometers agree at the first horizon in expectation. -/
theorem meanu_one_eq_S_zero (ν : Measure ℤ) : meanu (law d ν) 1 = S (law d ν) 0 := by
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  change u (fun y => (ω.1 y : ℝ)) 1 0 =
    (LatticeProb.survivorsFrom (toDriver ω) 0 0 : ℝ)
  rw [survivorsFrom_zero]
  change u (fun y => (ω.1 y : ℝ)) 1 0 = ((ω.1 0).toNat : ℝ)
  simp [u, walkOp, nbrSum, toNat_cast_eq_max, max_comm]

theorem meanU_one_eq_S_zero (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hi : Integrable (fun k : ℤ => |(k : ℝ)|) ν) :
    meanU (law d ν) 1 = S (law d ν) 0 := by
  rw [(Parking.Frozen.transport d hd ν inferInstance hi).2.1 1]
  simp

/-- The mean divisible odometer is positive at every positive horizon under a critical law. -/
theorem meanu_pos (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (n : ℕ) (hn : 1 ≤ n) : 0 < meanu (law d ν) n := by
  haveI := hν.prob
  have hm : 0 < meanu (law d ν) 1 := by
    rw [meanu_one_eq_S_zero, S_zero_eq hd]
    exact integral_toNat_pos ν hν.nonconst hν.integrable_abs hν.mean
  refine hm.trans_le ?_
  apply integral_mono (integrable_uOf hd ν hν.integrable_abs 1 0)
    (integrable_uOf hd ν hν.integrable_abs n 0)
  intro ω
  exact u_monotone_time hd (fun y => (ω.1 y : ℝ)) 0 hn
end Parking
