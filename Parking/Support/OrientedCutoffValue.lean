/-
The cutoff optimal-stopping values of `parking.tex:3199-3203` as functions on a
space of continuous rewards, and their convergence in law.

At a fixed cutoff level `A` the two rewards of the cited stability estimate
differ only on the compact box `K = [0,T] × [-2A, 2A]`, so both values are
functions of the restriction of the reward to `K`, i.e. of a point of `C(K)`.
This module builds that reading:

- `Parking.rewardBox T A` is `K`, and `Parking.rewardOfBox` extends a point of
  `C(K)` to a bounded continuous reward on `[0,∞) × ℝ` by clamping the argument
  to `K`.  The extension is an isometry for the supremum norm.
- `Parking.orientedCutoffValue` is the value of the discrete problem at that
  reward, and `Parking.brownianCutoffValue` the value of the Brownian problem.
- The discrete value is `1`-Lipschitz in the reward
  (`Parking.abs_orientedStoppingSup_sub_le`), and the cited stability estimate
  says that at each FIXED reward the discrete values converge to the Brownian
  one.  Those two facts are the local uniform hypothesis of the extended
  continuous mapping theorem, so the values converge in law as soon as the
  rewards do, in `C(K)`.

This is the step of `parking.tex:3199-3203` executed with no coupling and no
Skorokhod representation: the only cited input is
`Parking.External.OrientedStoppingStability`, read at a deterministic reward.
-/
import Parking.Support.ExtendedMapping
import Parking.Support.OrientedValueLipschitz
import Parking.External.OrientedStoppingStability
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- The compact box `[0,T] × [-2A, 2A]` on which the two cutoff rewards of
`parking.tex:3199-3203` differ. -/
abbrev rewardBox (T A : ℝ) : Type :=
  ↥(Set.Icc (0 : ℝ) T) × ↥(Set.Icc (-(2 * A)) (2 * A))

/-- The box is nonempty in its space coordinate. -/
theorem neg_two_mul_le_two_mul {A : ℝ} (hA : 0 ≤ A) : -(2 * A) ≤ 2 * A := by linarith

/-- The point of the box that a point of the plane is clamped to. -/
def boxPoint {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (s y : ℝ) : rewardBox T A :=
  (Set.projIcc (0 : ℝ) T hT s, Set.projIcc (-(2 * A)) (2 * A) (neg_two_mul_le_two_mul hA) y)

/-- A continuous reward on the box, extended to the whole of `ℝ × ℝ` by
clamping the argument to the box. -/
def rewardOfBox {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (G : C(rewardBox T A, ℝ)) :
    ℝ → ℝ → ℝ :=
  fun s y => G (boxPoint hT hA s y)

/-- **The extension is continuous on the plane.** -/
theorem continuous_rewardOfBox {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A)
    (G : C(rewardBox T A, ℝ)) :
    Continuous (fun p : ℝ × ℝ => rewardOfBox hT hA G p.1 p.2) :=
  G.continuous.comp
    (((continuous_projIcc).comp continuous_fst).prodMk
      ((continuous_projIcc).comp continuous_snd))

/-- **The extension is bounded by the norm of the reward.** -/
theorem abs_rewardOfBox_le {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A)
    (G : C(rewardBox T A, ℝ)) (s y : ℝ) : |rewardOfBox hT hA G s y| ≤ ‖G‖ := by
  show |G (boxPoint hT hA s y)| ≤ ‖G‖
  simpa [Real.norm_eq_abs] using G.norm_coe_le_norm (boxPoint hT hA s y)

/-- **The extension is an isometry for the supremum norm**: the extensions of
two rewards differ by at most their distance in `C(K)`. -/
theorem abs_rewardOfBox_sub_le {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A)
    (G H : C(rewardBox T A, ℝ)) (s y : ℝ) :
    |rewardOfBox hT hA G s y - rewardOfBox hT hA H s y| ≤ dist G H := by
  show |G (boxPoint hT hA s y) - H (boxPoint hT hA s y)| ≤ dist G H
  simpa [Real.dist_eq] using
    (ContinuousMap.dist_apply_le_dist (f := G) (g := H) (boxPoint hT hA s y))

/-- **The value of the discrete problem at the cutoff reward**, as a function of
the reward's restriction to the box: the supremum of `E_0 G(k/n, X_k/(2√n))`
over the stopping rules of the oriented walk bounded by `⌊nT⌋`. -/
def orientedCutoffValue {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (n : ℕ)
    (G : C(rewardBox T A, ℝ)) : ℝ :=
  orientedStoppingSup 2
    (fun (k : ℕ) (z : Site 2) => rewardOfBox hT hA G ((k : ℝ) / n) (orientedScaledSite n z))
    ⌊(n : ℝ) * T⌋₊ (0 : Site 2)

/-- **The value of the Brownian problem at the same reward.** -/
def brownianCutoffValue {ΩB : Type} [MeasurableSpace ΩB] (B : ℝ≥0 → ΩB → ℝ)
    (PB : Measure ΩB) {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A)
    (G : C(rewardBox T A, ℝ)) : ℝ :=
  contValue B PB (rewardOfBox hT hA G) T

/-- **The discrete cutoff value is `1`-Lipschitz in the reward**, uniformly in
the index `n`. -/
theorem abs_orientedCutoffValue_sub_le {T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (n : ℕ)
    (G H : C(rewardBox T A, ℝ)) :
    |orientedCutoffValue hT hA n G - orientedCutoffValue hT hA n H| ≤ dist G H :=
  abs_orientedStoppingSup_sub_le (d := 2) (by norm_num) _ _ _ _
    (M := max ‖G‖ ‖H‖)
    (fun k y => le_trans (abs_rewardOfBox_le hT hA G _ _) (le_max_left _ _))
    (fun k y => le_trans (abs_rewardOfBox_le hT hA H _ _) (le_max_right _ _))
    (fun k y => abs_rewardOfBox_sub_le hT hA G H _ _)

/-- **The cited stability estimate, read at one fixed reward.**  For each point
of `C(K)` the discrete cutoff values converge to the Brownian one. -/
theorem tendsto_orientedCutoffValue (hStability : External.OrientedStoppingStability)
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
    Tendsto (fun n => orientedCutoffValue hT.le hA n G) atTop
      (𝓝 (brownianCutoffValue B PB hT.le hA G)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hStability ΩB PB B hB T hT hWalk ‖G‖ (norm_nonneg G)
    (rewardOfBox hT.le hA G) (continuous_rewardOfBox hT.le hA G)
    (fun s y => abs_rewardOfBox_le hT.le hA G s y)
    (fun _ => rewardOfBox hT.le hA G)
    (fun _ s y => abs_rewardOfBox_le hT.le hA G s y)
    (fun δ hδ => ⟨0, fun n _ s _ y => by simpa using hδ.le⟩) (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  rw [Real.dist_eq]
  calc |orientedCutoffValue hT.le hA n G - brownianCutoffValue B PB hT.le hA G|
      ≤ ε / 2 := this
    _ < ε := by linarith

/-- **The Brownian cutoff value is `1`-Lipschitz in the reward**, because it is
the pointwise limit of the `1`-Lipschitz discrete values. -/
theorem abs_brownianCutoffValue_sub_le (hStability : External.OrientedStoppingStability)
    {ΩB : Type} [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → ℝ) (hB : IsQuarterBrownian B PB)
    {T A : ℝ} (hT : 0 < T) (hA : 0 ≤ A)
    (hWalk : ∀ (m : ℕ) (ts : Fin m → ℝ), (∀ i, ts i ∈ Set.Icc (0 : ℝ) T) →
      ∀ F : BoundedContinuousFunction (Fin m → ℝ) ℝ,
        Tendsto (fun n : ℕ =>
            ∫ p, F (fun i => orientedScaledSite n
                (orientedPath (0 : Site 2) p ⌊(n : ℝ) * ts i⌋₊)) ∂(walkLaw 2)) atTop
          (𝓝 (∫ β, F (fun i => B (Real.toNNReal (ts i)) β) ∂PB)))
    (G H : C(rewardBox T A, ℝ)) :
    |brownianCutoffValue B PB hT.le hA G - brownianCutoffValue B PB hT.le hA H| ≤ dist G H := by
  have hG := tendsto_orientedCutoffValue hStability PB B hB hT hA hWalk G
  have hH := tendsto_orientedCutoffValue hStability PB B hB hT hA hWalk H
  have hlim : Tendsto (fun n => |orientedCutoffValue hT.le hA n G
      - orientedCutoffValue hT.le hA n H|) atTop
      (𝓝 |brownianCutoffValue B PB hT.le hA G - brownianCutoffValue B PB hT.le hA H|) :=
    (hG.sub hH).abs
  exact le_of_tendsto hlim
    (Eventually.of_forall fun n => abs_orientedCutoffValue_sub_le hT.le hA n G H)

/-- **The convergence in law of the cutoff values from the convergence in law of
the cutoff rewards**, by the extended continuous mapping theorem.  This is the
step of `parking.tex:3199-3203`: the only cited input is the stability estimate,
read at a deterministic reward, and the only thing left to the repository is the
convergence in law of the rewards themselves in `C(K)`. -/
theorem tendsto_integral_orientedCutoffValue
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
    Tendsto (fun n => ∫ G, F (orientedCutoffValue hT.le hA n G) ∂(νs n)) atTop
      (𝓝 (∫ G, F (brownianCutoffValue B PB hT.le hA G) ∂ν)) := by
  have hLip : ∀ (n : ℕ) (G H : C(rewardBox T A, ℝ)),
      |orientedCutoffValue hT.le hA n G - orientedCutoffValue hT.le hA n H| ≤ dist G H :=
    fun n G H => abs_orientedCutoffValue_sub_le hT.le hA n G H
  have hmeas : ∀ n : ℕ, Measurable (fun G => orientedCutoffValue hT.le hA n G) := by
    intro n
    refine (LipschitzWith.continuous (K := 1) ?_).measurable
    intro G H
    rw [edist_dist, edist_dist]
    have := hLip n G H
    rw [Real.dist_eq]
    simp only [ENNReal.coe_one, one_mul]
    exact ENNReal.ofReal_le_ofReal this
  have hmeasf : Measurable (fun G => brownianCutoffValue B PB hT.le hA G) := by
    refine (LipschitzWith.continuous (K := 1) ?_).measurable
    intro G H
    rw [edist_dist, edist_dist]
    have := abs_brownianCutoffValue_sub_le hStability PB B hB hT hA hWalk G H
    rw [Real.dist_eq]
    simp only [ENNReal.coe_one, one_mul]
    exact ENNReal.ofReal_le_ofReal this
  refine tendsto_integral_comp_of_locally_uniform ν νs hlaw _ _ hmeas hmeasf ?_ F
  intro G ε hε
  exact locallyUniform_of_lipschitz _ _ (fun n H G' => hLip n H G')
    (fun H => tendsto_orientedCutoffValue hStability PB B hB hT hA hWalk H) G hε

end Parking

end
