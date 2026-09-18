/-
The per-`σ` bound on the two terminal-reward values, continuing the reduction:
integrating `Parking.abs_Ftrue_sub_Fcut_orientedPath_le` over the walk's own randomness gives a
bound on `|Parking.orientedTerminalValue Ftrue 0 σ - Parking.orientedTerminalValue Fcut 0 σ|`,
the SAME for every admissible stopping rule `σ` (the bound does not mention `σ` at all), which
is exactly `Parking.abs_orientedStoppingSup_sub_le_of_terminal`'s hypothesis.
-/
import Parking.Support.TightHappBound

open MeasureTheory Filter Topology LatticeProb

noncomputable section

namespace Parking

/-- The unscaled true reward: minus the potential of the remaining horizon. -/
def FtrueReward (η : Site 2 → ℝ) (n : ℕ) : ℕ → Site 2 → ℝ :=
  fun k z => -orientedPotential η (n - k) z

/-- **`Ftrue`**, the rescaled true reward. -/
def FtrueScaled (η : Site 2 → ℝ) (n : ℕ) : ℕ → Site 2 → ℝ :=
  fun k z => (n : ℝ) ^ (-(1 : ℝ) / 4) * FtrueReward η n k z

/-- **`Fcut`**, the box-clamped reward that `Parking.orientedCutoffValue` itself uses. -/
def FcutReward {A : ℝ} (hA : 0 ≤ A) (n : ℕ) (η : Site 2 → ℝ) : ℕ → Site 2 → ℝ :=
  fun k z => rewardOfBox (zero_le_one) hA (boxRewardMap 1 (zero_le_one) A hA n η)
    ((k : ℝ) / n) (orientedScaledSite n z)

theorem FtrueScaled_eq_const_mul (η : Site 2 → ℝ) (n : ℕ) :
    FtrueScaled η n = fun k z => (n : ℝ) ^ (-(1 : ℝ) / 4) * FtrueReward η n k z := rfl

/-! ### Integrability of the bad-event bound -/

theorem integrable_happBadBound {A : ℝ} (hA : 0 ≤ A) (n : ℕ) (η : Site 2 → ℝ) :
    Integrable (happBadBound hA n η) (walkLaw 2) := by
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  unfold happBadBound
  exact (integrable_orientedMax (by norm_num) (orientedPotential η) n 0).const_mul _
    |>.add (integrable_const _)

theorem integrable_indicator_happBadBound {A : ℝ} (hA : 0 ≤ A) (n : ℕ) (η : Site 2 → ℝ) :
    Integrable (Set.indicator (walkBad n A) (happBadBound hA n η)) (walkLaw 2) := by
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  exact (integrable_happBadBound hA n η).indicator (measurableSet_walkBad n A)

/-! ### The per-`σ` terminal-value bound -/

/-- **The terminal values of `Ftrue` and `Fcut` differ by at most the integral of the
bad-event bound, THE SAME for every admissible stopping rule.** -/
theorem abs_orientedTerminalValue_Ftrue_sub_Fcut_le {A : ℝ} (hA : 0 < A) (n : ℕ) (hn : 1 ≤ n)
    (η : Site 2 → ℝ) {σ : (ℕ → Fin 2 × Bool) → ℕ} (hσ : IsStoppingTimeLE n σ) :
    |orientedTerminalValue (FtrueScaled η n) 0 σ - orientedTerminalValue (FcutReward hA.le n η) 0 σ|
      ≤ ∫ p, Set.indicator (walkBad n A) (happBadBound hA.le n η) p ∂(walkLaw 2) := by
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  have hF := integrable_orientedTerminalReward (by norm_num : (1:ℕ) ≤ 2) hσ (FtrueScaled η n) 0
  have hG := integrable_orientedTerminalReward (by norm_num : (1:ℕ) ≤ 2) hσ (FcutReward hA.le n η) 0
  have hsub : orientedTerminalValue (FtrueScaled η n) 0 σ
      - orientedTerminalValue (FcutReward hA.le n η) 0 σ
      = ∫ p, (FtrueScaled η n (σ p) (orientedPath (0 : Site 2) p (σ p))
          - FcutReward hA.le n η (σ p) (orientedPath (0 : Site 2) p (σ p))) ∂(walkLaw 2) := by
    rw [orientedTerminalValue, orientedTerminalValue, ← integral_sub hF hG]
  rw [hsub]
  have hbound : ∀ p, |FtrueScaled η n (σ p) (orientedPath (0 : Site 2) p (σ p))
        - FcutReward hA.le n η (σ p) (orientedPath (0 : Site 2) p (σ p))|
      ≤ Set.indicator (walkBad n A) (happBadBound hA.le n η) p :=
    fun p => abs_Ftrue_sub_Fcut_orientedPath_le hA n hn η p (σ p) (hσ.1 p)
  calc |∫ p, (FtrueScaled η n (σ p) (orientedPath (0 : Site 2) p (σ p))
          - FcutReward hA.le n η (σ p) (orientedPath (0 : Site 2) p (σ p))) ∂(walkLaw 2)|
      ≤ ∫ p, |FtrueScaled η n (σ p) (orientedPath (0 : Site 2) p (σ p))
          - FcutReward hA.le n η (σ p) (orientedPath (0 : Site 2) p (σ p))| ∂(walkLaw 2) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ p, Set.indicator (walkBad n A) (happBadBound hA.le n η) p ∂(walkLaw 2) :=
        integral_mono (hF.sub hG).abs (integrable_indicator_happBadBound hA.le n η) hbound

end Parking

end
