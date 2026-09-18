/-
`hYconv` of `Parking.oriented_scaling_of_cutoff`, parametrized by the three ingredients
`Parking.tendsto_integral_orientedCutoffValuePot` itself needs: the cited stability External,
a concrete quarter-Brownian motion, and the finite-dimensional convergence of the rescaled
oriented walk to it (`hWalk`).

`Parking.tendsto_integral_Y_of_hWalk` rewrites `Parking.tendsto_integral_orientedCutoffValuePot`'s
conclusion, at `T := 1` and `ν := Parking.contBoxRewardLaw`/`νs := Parking.boxRewardLaw` (fed
by `Parking.hlaw_orientedBoxReward`, already SEALED), from an integral against
`Parking.boxRewardLaw` back to an integral against the oriented law itself: `boxRewardLaw`
is the pushforward of `iidLaw 2 (realLaw ν)` along `Parking.boxRewardMap` (`integral_map`), and
`iidLaw 2 (realLaw ν)` is itself the pushforward of `Parking.orientedLaw 2 ν` along
`Parking.confReal` (`Parking.integral_oriented_confReal`) — the SAME two bridges `Parking.Y`
itself was built from.  This is EXACTLY `hYconv`, with no new probability.
-/
import Parking.Support.TightYCutoff
import Parking.Support.TightHlawAssembly
import Parking.External.OrientedStoppingStability
import Parking.Support.OrientedCutoffValuePot

open MeasureTheory LatticeProb Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking

local instance instMeasurableSpaceRewardBoxTightYConv (T A : ℝ) :
    MeasurableSpace C(rewardBox T A, ℝ) := borel _
local instance instBorelSpaceRewardBoxTightYConv (T A : ℝ) :
    BorelSpace C(rewardBox T A, ℝ) := ⟨rfl⟩

/-- **`hYconv`, given the stability External, a concrete quarter-Brownian motion, and the
finite-dimensional convergence of the rescaled walk to it.** -/
theorem tendsto_integral_Y_of_hWalk (ν : Measure ℤ) (hν : CriticalLaw ν)
    (hBinomial : External.BinomialLocalCLT) (hStability : External.OrientedStoppingStability)
    {ΩB : Type} [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → ℝ) (hB : IsQuarterBrownian B PB) (A : ℕ)
    (hWalk : ∀ (m : ℕ) (ts : Fin m → ℝ), (∀ i, ts i ∈ Set.Icc (0 : ℝ) (1 : ℝ)) →
      ∀ F : BoundedContinuousFunction (Fin m → ℝ) ℝ,
        Tendsto (fun n : ℕ =>
            ∫ p, F (fun i => orientedScaledSite n
                (orientedPath (0 : Site 2) p ⌊(n : ℝ) * ts i⌋₊)) ∂(walkLaw 2)) atTop
          (𝓝 (∫ β, F (fun i => B (Real.toNNReal (ts i)) β) ∂PB)))
    {Yfield : (Fin 2 → ℝ) → contNoiseSpace → ℝ} (hYmeas : ∀ z, Measurable (Yfield z))
    (hYcont : ∀ ω, ContinuousOn (fun z => Yfield z ω) (orientedBox 1 (A : ℝ)))
    (hYmod : ∀ z ∈ orientedBox 1 (A : ℝ),
      contZ (∫ x : ℝ, x ^ 2 ∂(realLaw ν)) 1 (z 0) (z 1) =ᵐ[contNoiseLaw] Yfield z)
    (f : ℝ → ℝ) (hfb : ∃ C : ℝ, ∀ x y, dist (f x) (f y) ≤ C) (hflip : ∃ K, LipschitzWith K f) :
    ∃ c : ℝ, Tendsto (fun n => ∫ w, f (Y A n w) ∂(orientedLaw 2 ν)) atTop (𝓝 c) := by
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  obtain ⟨K, hK⟩ := hflip
  set F : BoundedContinuousFunction ℝ ℝ := ⟨⟨f, hK.continuous⟩, hfb⟩ with hFdef
  have hFcoe : ∀ x, F x = f x := fun _ => rfl
  refine ⟨∫ G, F (brownianCutoffValuePot B PB (zero_le_one) (Nat.cast_nonneg A) G)
      ∂(contBoxRewardLaw 1 (zero_le_one) (A : ℝ) (Nat.cast_nonneg A) Yfield hYmeas hYcont), ?_⟩
  have hconv := tendsto_integral_orientedCutoffValuePot hStability PB B hB
    (T := (1 : ℝ)) (A := (A : ℝ)) one_pos (Nat.cast_nonneg A) hWalk
    (contBoxRewardLaw 1 (zero_le_one) (A : ℝ) (Nat.cast_nonneg A) Yfield hYmeas hYcont)
    (fun n => boxRewardLaw 1 ν (zero_le_one) (A : ℝ) (Nat.cast_nonneg A) n)
    (hlaw_orientedBoxReward ν hν hBinomial (zero_le_one) (Nat.cast_nonneg A)
      hYmeas hYcont hYmod) F
  have heq : ∀ n, (∫ G, F (orientedCutoffValuePot (zero_le_one) (Nat.cast_nonneg A) n G)
      ∂(boxRewardLaw 1 ν (zero_le_one) (A : ℝ) (Nat.cast_nonneg A) n))
      = ∫ w, f (Y A n w) ∂(orientedLaw 2 ν) := by
    intro n
    have hstep1 : (∫ G, F (orientedCutoffValuePot (zero_le_one) (Nat.cast_nonneg A) n G)
        ∂(boxRewardLaw 1 ν (zero_le_one) (A : ℝ) (Nat.cast_nonneg A) n))
        = ∫ η, F (orientedCutoffValuePot (zero_le_one) (Nat.cast_nonneg A) n
            (boxRewardMap 1 (zero_le_one) (A : ℝ) (Nat.cast_nonneg A) n η))
          ∂(iidLaw 2 (realLaw ν)) :=
      integral_map
        (measurable_boxRewardMap 1 (zero_le_one) (A : ℝ) (Nat.cast_nonneg A) n).aemeasurable
        (F.continuous.measurable.comp
          (measurable_orientedCutoffValuePot (zero_le_one) (Nat.cast_nonneg A) n)).aestronglyMeasurable
    have hGmeas : Measurable fun η : Site 2 → ℝ =>
        F (orientedCutoffValuePot (zero_le_one) (Nat.cast_nonneg A) n
          (boxRewardMap 1 (zero_le_one) (A : ℝ) (Nat.cast_nonneg A) n η)) :=
      F.continuous.measurable.comp
        ((measurable_orientedCutoffValuePot (zero_le_one) (Nat.cast_nonneg A) n).comp
          (measurable_boxRewardMap 1 (zero_le_one) (A : ℝ) (Nat.cast_nonneg A) n))
    have hstep2 := integral_oriented_confReal (d := 2) (by norm_num) ν hGmeas
    have hpt : ∀ w : Data 2, F (orientedCutoffValuePot (zero_le_one) (Nat.cast_nonneg A) n
        (boxRewardMap 1 (zero_le_one) (A : ℝ) (Nat.cast_nonneg A) n (confReal w)))
        = f (Y A n w) := fun w => hFcoe _
    rw [hstep1, ← hstep2]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hfeq : (fun n => ∫ G, F (orientedCutoffValuePot (zero_le_one) (Nat.cast_nonneg A) n G)
      ∂(boxRewardLaw 1 ν (zero_le_one) (A : ℝ) (Nat.cast_nonneg A) n))
      = fun n => ∫ w, f (Y A n w) ∂(orientedLaw 2 ν) := funext heq
  rwa [hfeq] at hconv

end Parking

end
