import Parking.Support.OrientedValueLipschitz
import Parking.Support.OrientedScalingTail

/-!
# Local comparison of oriented stopping values

A reward comparison valid inside a spatial interval controls the stopping
values up to the maximal probability of exiting that interval.
-/

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

/-- A local reward comparison and the exit probability bound the difference of
    oriented stopping values. -/
theorem abs_orientedStoppingSup_sub_le_of_local_reward
    {n : ℕ} {T A δ M : ℝ} (hδ : 0 ≤ δ)
    (F G : ℕ → Site 2 → ℝ)
    (hF : ∀ k z, |F k z| ≤ M) (hG : ∀ k z, |G k z| ≤ M)
    (hlocal : ∀ p ∉ orientedScaledExit n T A, ∀ k ≤ ⌊(n : ℝ) * T⌋₊,
      |F k (orientedPath 0 p k) - G k (orientedPath 0 p k)| ≤ δ) :
    |orientedStoppingSup 2 F ⌊(n : ℝ) * T⌋₊ 0 -
      orientedStoppingSup 2 G ⌊(n : ℝ) * T⌋₊ 0| ≤
      δ + 2 * M * (walkLaw 2).real (orientedScaledExit n T A) := by
  have := stepLaw_isProbability (d := 2) (by norm_num)
  have : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  let K := ⌊(n : ℝ) * T⌋₊
  let E := orientedScaledExit n T A
  let c := δ + 2 * M * (walkLaw 2).real E
  have hE : MeasurableSet E := measurableSet_orientedScaledExit n T A
  have hterminal : ∀ {σ : (ℕ → Fin 2 × Bool) → ℕ}, IsStoppingTimeLE K σ →
      |orientedTerminalValue F 0 σ - orientedTerminalValue G 0 σ| ≤ c := by
    intro σ hσ
    have hFi := integrable_orientedTerminalReward (by norm_num) hσ F 0
    have hGi := integrable_orientedTerminalReward (by norm_num) hσ G 0
    have hpoint : ∀ p, |F (σ p) (orientedPath 0 p (σ p)) - G (σ p) (orientedPath 0 p (σ p))|
        ≤ δ + E.indicator (fun _ => 2 * M) p := by
      intro p
      by_cases hp : p ∈ E
      · rw [Set.indicator_of_mem hp]
        have hb := abs_sub (F (σ p) (orientedPath 0 p (σ p)))
          (G (σ p) (orientedPath 0 p (σ p)))
        have hf := hF (σ p) (orientedPath 0 p (σ p))
        have hg := hG (σ p) (orientedPath 0 p (σ p))
        linarith
      · rw [Set.indicator_of_notMem hp, add_zero]
        exact hlocal p hp (σ p) (hσ.1 p)
    have hi : Integrable (fun p => δ + E.indicator (fun _ => 2 * M) p) (walkLaw 2) :=
      (integrable_const δ).add ((integrable_const (2 * M)).indicator hE)
    rw [orientedTerminalValue, orientedTerminalValue, ← integral_sub hFi hGi]
    calc
      |∫ p, (F (σ p) (orientedPath 0 p (σ p)) - G (σ p) (orientedPath 0 p (σ p)))
          ∂(walkLaw 2)| ≤ ∫ p, |F (σ p) (orientedPath 0 p (σ p)) - G (σ p) (orientedPath 0 p (σ p))|
            ∂(walkLaw 2) := abs_integral_le_integral_abs
      _ ≤ ∫ p, (δ + E.indicator (fun _ => 2 * M) p) ∂(walkLaw 2) :=
        integral_mono (hFi.sub hGi).abs hi hpoint
      _ = c := by
        rw [integral_add (integrable_const δ) ((integrable_const (2 * M)).indicator hE),
          integral_indicator_const _ hE]
        simp [c, smul_eq_mul, mul_comm]
  have hbF := bddAbove_orientedTerminalValues (by norm_num) F K 0 hF
  have hbG := bddAbove_orientedTerminalValues (by norm_num) G K 0 hG
  have hneF := orientedTerminalValues_nonempty 2 F K 0
  have hneG := orientedTerminalValues_nonempty 2 G K 0
  have hFG : orientedStoppingSup 2 F K 0 ≤ orientedStoppingSup 2 G K 0 + c := by
    apply csSup_le hneF
    rintro a ⟨σ, hσ, rfl⟩
    have h1 : orientedTerminalValue G 0 σ ≤ orientedStoppingSup 2 G K 0 :=
      le_csSup hbG ⟨σ, hσ, rfl⟩
    have h2 := (abs_sub_le_iff.mp (hterminal hσ)).1
    linarith
  have hGF : orientedStoppingSup 2 G K 0 ≤ orientedStoppingSup 2 F K 0 + c := by
    apply csSup_le hneG
    rintro a ⟨σ, hσ, rfl⟩
    have h1 : orientedTerminalValue F 0 σ ≤ orientedStoppingSup 2 F K 0 :=
      le_csSup hbF ⟨σ, hσ, rfl⟩
    have h2 := (abs_sub_le_iff.mp (hterminal hσ)).2
    linarith
  rw [abs_sub_le_iff]
  constructor <;> linarith

end Parking
