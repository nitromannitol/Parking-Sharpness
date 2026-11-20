import Parking.External.SpatialStoppingStability
import Parking.Support.SpatialHorizonShift

/-!
# Spatial stopping stability from continuum stopping stability

The lattice path of the simple random walk has the law of the walk of the divisible sandpile
stopping problem, so the continuum stopping stability of the divisible sandpile, applied at the
scale `√n` to the remaining-time form of the reward, gives the spatial stability statement once
the horizon floor is controlled and the rewards are approximated uniformly.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

/-- The spatial stopping stability statement follows from the continuum stopping stability of
the divisible sandpile. -/
theorem Parking.External.spatialStoppingStability_of_continuumStoppingStability
    (hStab : Sandpile.External.ContinuumStoppingStability.{0}) :
    Parking.External.SpatialStoppingStability := by
  intro d hd _hd3 ΩB _ PB _ B hB T hT _hWalk M hM G hG hGM G' hG'M hconv ε hε
  obtain ⟨N₁, hN₁⟩ := hconv (ε / 3) (by positivity)
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.1
    (Parking.stoppingSup_horizonShift_tendsto_zero hd hT.le hM G hG hGM)) (ε / 3) (by positivity)
  obtain ⟨N₃, hN₃⟩ := Parking.stoppingSup_shifted_of_continuumStoppingStability
    hStab hd ΩB PB B hB hT G hG hGM (ε / 3) (by positivity)
  refine ⟨max (max N₁ N₂) (max N₃ 1), ?_⟩
  intro n hn
  have hn1 : N₁ ≤ n := by omega
  have hn2 : N₂ ≤ n := by omega
  have hn3 : N₃ ≤ n := by omega
  have hn0 : 0 < n := by omega
  let V' := Parking.stoppingSup d
    (fun k z => G' n ((k : ℝ) / n) (Parking.spatialScaledSite n z)) ⌊(n : ℝ) * T⌋₊ 0
  let V := Parking.stoppingSup d
    (fun k z => G ((k : ℝ) / n) (Parking.spatialScaledSite n z)) ⌊(n : ℝ) * T⌋₊ 0
  let W := Parking.stoppingSup d
    (fun k z => G ((k : ℝ) / n + Parking.orientedHorizonShift n T)
      (Parking.spatialScaledSite n z)) ⌊(n : ℝ) * T⌋₊ 0
  let C := Parking.spatialContValue (Parking.ofBrownianSpace B) PB G T
  have h₁ : |V' - V| ≤ ε / 3 :=
    Parking.abs_stoppingSup_sub_le_of_le hd _ _ _ 0 (fun k y => hG'M n _ _)
      (fun k y => hGM _ _) (fun k hk y =>
        hN₁ n hn1 _ (Parking.orientedHorizonShift_time_mem hn0 hT.le hk).1 _)
  have h₂ : |V - W| ≤ ε / 3 := by
    have h := hN₂ n hn2
    rw [Real.dist_eq, sub_zero] at h
    exact h.le
  have h₃ : |W - C| ≤ ε / 3 := hN₃ n hn3
  have h₄ : |V' - C| ≤ |V' - V| + |V - W| + |W - C| := by
    calc |V' - C| ≤ |V' - V| + |V - C| := abs_sub_le _ _ _
      _ ≤ |V' - V| + (|V - W| + |W - C|) := add_le_add le_rfl (abs_sub_le V W C)
      _ = _ := by ring
  change |V' - C| ≤ ε
  linarith
