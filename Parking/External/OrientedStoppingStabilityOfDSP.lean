import Parking.External.OrientedStoppingStability
import Parking.Support.OrientedHorizonShift
import Parking.Support.OrientedRewardApprox

/-!
# Oriented stopping stability from continuum stopping stability

The oriented path projects to the one-dimensional simple walk, and backward
induction removes the unused Boolean randomness. The sandpile stability input
then gives the oriented stability statement after Brownian scaling, control of
the horizon floor, and uniform approximation of the rewards.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

/-- The oriented stopping stability statement follows from the one-dimensional
    case of the divisible sandpile continuum stopping stability. -/
theorem Parking.External.orientedStoppingStability_of_continuumStoppingStability
    (hStab : Sandpile.External.ContinuumStoppingStability.{0}) :
    Parking.External.OrientedStoppingStability := by
  intro Ω _ P _ B hB T hT _hWalk M hM G hG hGM G' hG'M hconv ε hε
  obtain ⟨N₁, hN₁⟩ := hconv (ε / 3) (by positivity)
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.1
    (Parking.orientedStoppingSup_horizonShift_tendsto_zero hT.le hM G hG hGM))
      (ε / 3) (by positivity)
  obtain ⟨N₃, hN₃⟩ := Parking.orientedStoppingSup_shifted_of_continuumStoppingStability
    hStab Ω P B hB hT hM G hG hGM (ε / 3) (by positivity)
  refine ⟨max (max N₁ N₂) (max N₃ 1), ?_⟩
  intro n hn
  have hn1 : N₁ ≤ n := by omega
  have hn2 : N₂ ≤ n := by omega
  have hn3 : N₃ ≤ n := by omega
  have hn0 : 0 < n := by omega
  let V' := Parking.orientedStoppingSup 2
    (fun k z => G' n ((k : ℝ) / n) (Parking.orientedScaledSite n z)) ⌊(n : ℝ) * T⌋₊ 0
  let V := Parking.orientedStoppingSup 2
    (fun k z => G ((k : ℝ) / n) (Parking.orientedScaledSite n z)) ⌊(n : ℝ) * T⌋₊ 0
  let W := Parking.orientedStoppingSup 2
    (fun k z => G ((k : ℝ) / n + Parking.orientedHorizonShift n T)
      (Parking.orientedScaledSite n z)) ⌊(n : ℝ) * T⌋₊ 0
  have h₁ : |V' - V| ≤ ε / 3 :=
    Parking.abs_orientedStoppingSup_sub_le_of_uniform_reward hn0 hT.le G (G' n)
      hGM (hG'M n) (hN₁ n hn1)
  have h₂ : |V - W| ≤ ε / 3 := by
    have h := hN₂ n hn2
    rw [Real.dist_eq, sub_zero] at h
    exact h.le
  have h₃ : |W - Parking.contValue B P G T| ≤ ε / 3 := hN₃ n hn3
  calc
    |V' - Parking.contValue B P G T| ≤ |V' - V| + |V - W| + |W - Parking.contValue B P G T| := by
      calc
        |V' - Parking.contValue B P G T| ≤ |V' - V| + |V - Parking.contValue B P G T| :=
          abs_sub_le _ _ _
        _ ≤ |V' - V| + (|V - W| + |W - Parking.contValue B P G T|) :=
          add_le_add le_rfl (abs_sub_le V W (Parking.contValue B P G T))
        _ = _ := by ring
    _ ≤ ε := by linarith
