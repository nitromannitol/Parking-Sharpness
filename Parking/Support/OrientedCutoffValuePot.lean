/-
The cutoff optimal-stopping value TOGETHER WITH the potential at the origin
(`parking.tex:3186-3190`): `Parking.uOriented_eq_potential_add_stoppingSup` writes the
oriented odometer as `Φ_n(x) + sup_σ E_x[-Φ_{n-σ}(X_σ)]`, the discrete mirror of
`U(T) = Z_T(0,0) + sup_τ E_0[-Z_T(τ,B_τ)]`, and `Parking.OrientedCutoffValue`'s cutoff
value reads only the SECOND (stopping-sup) term.  This module adds the FIRST term back
in, as a functional of the SAME reward field: `Parking.orientedCutoffValuePot hT hA n G :=
Parking.orientedCutoffValue hT hA n G - G (Parking.boxPoint hT hA 0 0)`, since (by
`Parking.rewardOfBox_boxRewardMap_eq_orientedGridReward` at `k = 0`, `z = 0`) the box
reward at the origin is exactly `Parking.orientedGridReward n n η 0 0 = -n^{-1/4}Φ_n(0)`.

The origin-evaluation `G ↦ G (boxPoint hT hA 0 0)` is `1`-Lipschitz (an evaluation on
`C(K)` with the supremum norm), so `orientedCutoffValuePot` is `2`-Lipschitz in `G`, and
the extended continuous mapping theorem applies to it exactly as it does to the plain
cutoff value in `Parking.OrientedCutoffValue`, with the same sole cited input
`Parking.External.OrientedStoppingStability`.
-/
import Parking.Support.OrientedCutoffValue

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking

local instance instMeasurableSpaceRewardBoxOrientedCutoffValuePot (T A : ℝ) :
    MeasurableSpace C(rewardBox T A, ℝ) := borel _
local instance instBorelSpaceRewardBoxOrientedCutoffValuePot (T A : ℝ) :
    BorelSpace C(rewardBox T A, ℝ) := ⟨rfl⟩

/-- **The cutoff value together with the potential at the origin, read at the box
reward.** -/
def orientedCutoffValuePot {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (n : ℕ)
    (G : C(rewardBox T A, ℝ)) : ℝ :=
  orientedCutoffValue hT hA n G - G (boxPoint hT hA 0 0)

/-- **The Brownian value together with the field value at the origin.** -/
def brownianCutoffValuePot {ΩB : Type} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ)
    (PB : Measure ΩB) {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (G : C(rewardBox T A, ℝ)) : ℝ :=
  brownianCutoffValue B PB hT hA G - G (boxPoint hT hA 0 0)

/-- **`orientedCutoffValuePot` is `2`-Lipschitz in the reward.** -/
theorem abs_orientedCutoffValuePot_sub_le {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (n : ℕ)
    (G H : C(rewardBox T A, ℝ)) :
    |orientedCutoffValuePot hT hA n G - orientedCutoffValuePot hT hA n H| ≤ 2 * dist G H := by
  unfold orientedCutoffValuePot
  have h1 : |orientedCutoffValue hT hA n G - orientedCutoffValue hT hA n H| ≤ dist G H :=
    abs_orientedCutoffValue_sub_le hT hA n G H
  have h2 : |G (boxPoint hT hA 0 0) - H (boxPoint hT hA 0 0)| ≤ dist G H := by
    simpa [Real.dist_eq] using ContinuousMap.dist_apply_le_dist (f := G) (g := H)
      (boxPoint hT hA 0 0)
  calc |orientedCutoffValue hT hA n G - G (boxPoint hT hA 0 0) -
        (orientedCutoffValue hT hA n H - H (boxPoint hT hA 0 0))|
      = |(orientedCutoffValue hT hA n G - orientedCutoffValue hT hA n H) -
          (G (boxPoint hT hA 0 0) - H (boxPoint hT hA 0 0))| := by ring_nf
    _ ≤ |orientedCutoffValue hT hA n G - orientedCutoffValue hT hA n H| +
          |G (boxPoint hT hA 0 0) - H (boxPoint hT hA 0 0)| := abs_sub _ _
    _ ≤ dist G H + dist G H := add_le_add h1 h2
    _ = 2 * dist G H := by ring

/-- **The plain cutoff value at the zero reward vanishes.** -/
theorem orientedCutoffValue_zero {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (n : ℕ) :
    orientedCutoffValue hT hA n (0 : C(rewardBox T A, ℝ)) = 0 := by
  have hF0 : (fun (k : ℕ) (z : Site 2) => rewardOfBox hT hA (0 : C(rewardBox T A, ℝ))
      ((k : ℝ) / n) (orientedScaledSite n z)) = fun _ _ => (0 : ℝ) := by
    funext k z
    show (0 : C(rewardBox T A, ℝ)) (boxPoint hT hA ((k : ℝ) / n) (orientedScaledSite n z)) = 0
    simp
  show orientedStoppingSup 2 _ ⌊(n : ℝ) * T⌋₊ (0 : Site 2) = 0
  rw [hF0]
  apply le_antisymm
  · exact orientedStoppingSup_le (by norm_num) _ _ _ le_rfl (fun _ _ => le_refl 0)
  · have hmem : (0 : ℝ) ∈ orientedTerminalValues 2 (fun _ _ => (0 : ℝ)) ⌊(n : ℝ) * T⌋₊ (0 : Site 2) :=
      ⟨fun _ => 0, ⟨fun _ => Nat.zero_le _, fun _ _ _ => rfl⟩, by simp [orientedTerminalValue]⟩
    exact le_csSup (bddAbove_orientedTerminalValues (M := 0) (by norm_num) _ _ _
      (fun _ _ => by simp)) hmem

/-- **The potential-inclusive value at the zero reward also vanishes**: the plain cutoff
value is `0` and the zero reward's evaluation at the origin is `0`. -/
theorem orientedCutoffValuePot_zero {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (n : ℕ) :
    orientedCutoffValuePot hT hA n (0 : C(rewardBox T A, ℝ)) = 0 := by
  unfold orientedCutoffValuePot
  rw [orientedCutoffValue_zero]
  simp

/-- **The potential-inclusive value is bounded by twice the norm of the reward.** -/
theorem abs_orientedCutoffValuePot_le {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (n : ℕ)
    (G : C(rewardBox T A, ℝ)) : |orientedCutoffValuePot hT hA n G| ≤ 2 * ‖G‖ := by
  have h := abs_orientedCutoffValuePot_sub_le hT hA n G 0
  rwa [orientedCutoffValuePot_zero, sub_zero, dist_zero_right] at h

/-- **`orientedCutoffValuePot` is measurable in the reward.** -/
theorem measurable_orientedCutoffValuePot {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (n : ℕ) :
    Measurable (fun G : C(rewardBox T A, ℝ) => orientedCutoffValuePot hT hA n G) := by
  refine (LipschitzWith.continuous (K := 2) ?_).measurable
  intro G H
  have h := abs_orientedCutoffValuePot_sub_le hT hA n G H
  rw [edist_dist, edist_dist, Real.dist_eq]
  calc ENNReal.ofReal |orientedCutoffValuePot hT hA n G - orientedCutoffValuePot hT hA n H|
      ≤ ENNReal.ofReal (2 * dist G H) := ENNReal.ofReal_le_ofReal h
    _ = ((2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (dist G H) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]; norm_num

/-- **The `2`-Lipschitz reward-value map converges pointwise from the plain cutoff-value
convergence, minus the same origin evaluation on both sides.** -/
theorem tendsto_orientedCutoffValuePot (hStability : External.OrientedStoppingStability)
    {ΩB : Type} [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → ℝ) (hB : IsQuarterBrownian B PB)
    {T A : ℝ} (hT : 0 < T) (hA : 0 ≤ A)
    (hWalk : ∀ (m : ℕ) (ts : Fin m → ℝ), (∀ i, ts i ∈ Set.Icc (0 : ℝ) T) →
      ∀ F : BoundedContinuousFunction (Fin m → ℝ) ℝ,
        Tendsto (fun n : ℕ =>
            ∫ p, F (fun i => orientedScaledSite n
                (orientedPath (0 : Site 2) p ⌊(n : ℝ) * ts i⌋₊)) ∂(walkLaw 2)) atTop
          (𝓝 (∫ β, F (fun i => B (Real.toNNReal (ts i)) β) ∂PB)))
    (G : C(rewardBox T A, ℝ)) :
    Tendsto (fun n => orientedCutoffValuePot hT.le hA n G) atTop
      (𝓝 (brownianCutoffValuePot B PB hT.le hA G)) := by
  unfold orientedCutoffValuePot brownianCutoffValuePot
  exact (tendsto_orientedCutoffValue hStability PB B hB hT hA hWalk G).sub_const _

/-- **The convergence in law of the potential-inclusive cutoff values**, by the extended
continuous mapping theorem applied to `Parking.orientedCutoffValuePot` in place of the
plain cutoff value: the only cited input is still `Parking.External.OrientedStoppingStability`,
read at a deterministic reward. -/
theorem tendsto_integral_orientedCutoffValuePot
    (hStability : External.OrientedStoppingStability)
    {ΩB : Type} [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → ℝ) (hB : IsQuarterBrownian B PB)
    {T A : ℝ} (hT : 0 < T) (hA : 0 ≤ A)
    (hWalk : ∀ (m : ℕ) (ts : Fin m → ℝ), (∀ i, ts i ∈ Set.Icc (0 : ℝ) T) →
      ∀ F : BoundedContinuousFunction (Fin m → ℝ) ℝ,
        Tendsto (fun n : ℕ =>
            ∫ p, F (fun i => orientedScaledSite n
                (orientedPath (0 : Site 2) p ⌊(n : ℝ) * ts i⌋₊)) ∂(walkLaw 2)) atTop
          (𝓝 (∫ β, F (fun i => B (Real.toNNReal (ts i)) β) ∂PB)))
    [MeasurableSpace C(rewardBox T A, ℝ)] [OpensMeasurableSpace C(rewardBox T A, ℝ)]
    (ν : Measure C(rewardBox T A, ℝ)) [IsProbabilityMeasure ν]
    (νs : ℕ → Measure C(rewardBox T A, ℝ)) [∀ n, IsProbabilityMeasure (νs n)]
    (hlaw : ∀ Φ : BoundedContinuousFunction C(rewardBox T A, ℝ) ℝ,
      Tendsto (fun n => ∫ G, Φ G ∂(νs n)) atTop (𝓝 (∫ G, Φ G ∂ν)))
    (F : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n => ∫ G, F (orientedCutoffValuePot hT.le hA n G) ∂(νs n)) atTop
      (𝓝 (∫ G, F (brownianCutoffValuePot B PB hT.le hA G) ∂ν)) := by
  have hLip : ∀ (n : ℕ) (G H : C(rewardBox T A, ℝ)),
      |orientedCutoffValuePot hT.le hA n G - orientedCutoffValuePot hT.le hA n H| ≤
        2 * dist G H :=
    fun n G H => abs_orientedCutoffValuePot_sub_le hT.le hA n G H
  have hmeas : ∀ n : ℕ, Measurable (fun G => orientedCutoffValuePot hT.le hA n G) := by
    intro n
    refine (LipschitzWith.continuous (K := 2) ?_).measurable
    intro G H
    have h := abs_orientedCutoffValuePot_sub_le hT.le hA n G H
    rw [edist_dist, edist_dist, Real.dist_eq]
    calc ENNReal.ofReal |orientedCutoffValuePot hT.le hA n G - orientedCutoffValuePot hT.le hA n H|
        ≤ ENNReal.ofReal (2 * dist G H) := ENNReal.ofReal_le_ofReal h
      _ = ((2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (dist G H) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  have hmeasf : Measurable (fun G => brownianCutoffValuePot B PB hT.le hA G) := by
    have h1 : Measurable (fun G : C(rewardBox T A, ℝ) => brownianCutoffValue B PB hT.le hA G) := by
      refine (LipschitzWith.continuous (K := 1) ?_).measurable
      intro G H
      rw [edist_dist, edist_dist]
      have := abs_brownianCutoffValue_sub_le hStability PB B hB hT hA hWalk G H
      rw [Real.dist_eq]
      simp only [ENNReal.coe_one, one_mul]
      exact ENNReal.ofReal_le_ofReal this
    have h2 : Measurable (fun G : C(rewardBox T A, ℝ) => G (boxPoint hT.le hA 0 0)) := by
      refine (LipschitzWith.continuous (K := 1) ?_).measurable
      intro G H
      rw [edist_dist, edist_dist]
      have := abs_rewardOfBox_sub_le hT.le hA G H 0 0
      rw [Real.dist_eq]
      simp only [ENNReal.coe_one, one_mul]
      refine ENNReal.ofReal_le_ofReal ?_
      simpa [rewardOfBox, boxPoint] using this
    exact h1.sub h2
  refine tendsto_integral_comp_of_locally_uniform ν νs hlaw _ _ hmeas hmeasf ?_ F
  intro G ε hε
  exact locallyUniform_of_lipschitz_const (by norm_num : (0:ℝ) < 2) _ _
    (fun n H G' => hLip n H G')
    (fun H => tendsto_orientedCutoffValuePot hStability PB B hB hT hA hWalk H) G hε

end Parking

end
