import Parking.Support.RangeResolvent
import LatticeProb.Graph.ExitTime
import LatticeProb.Graph.WalkAverage
import LatticeProb.Walk.GreenTwoSided.Kernels
import LatticeProb.Walk.SRWSup

/-!
# Confinement to a fixed finite set

The heat-kernel upper bound and the Markov property bound the probability that
the signed-direction walk stays inside a fixed finite set.
-/

open MeasureTheory LatticeProb

noncomputable section

namespace Parking

variable {d : ℕ}

/-- The position-path law assigns the finite-set survival probability to the
confinement event. -/
private theorem measureReal_siteWalkLaw_stayIn (hd : 1 ≤ d) (B : Finset (Site d))
    (n : ℕ) (x : Site d) :
    (siteWalkLaw d x).real (Graph.stayIn (B : Set (Site d)) n) =
      Network.survival (lattice d) B n x := by
  have : NeZero d := ⟨by omega⟩
  let S : Set (ℕ → Site d) := Graph.stayIn (B : Set (Site d)) n
  let F : (ℕ → Site d) → ℝ := S.indicator 1
  have hS : MeasurableSet S := Graph.measurableSet_stayIn _ n
  have hFm : Measurable F := (measurable_const : Measurable (1 : (ℕ → Site d) → ℝ)).indicator hS
  have hFb : ∀ X, ‖F X‖ ≤ 1 := by
    intro X
    by_cases hX : X ∈ S <;> simp [F, hX]
  have hdep : ∀ X Y : ℕ → Site d, (∀ k ≤ n, X k = Y k) → F X = F Y := by
    intro X Y hXY
    have hiff : X ∈ S ↔ Y ∈ S := by
      change (∀ k ≤ n, X k ∈ B) ↔ ∀ k ≤ n, Y k ∈ B
      constructor <;> intro h k hk
      · rw [← hXY k hk]; exact h k hk
      · rw [hXY k hk]; exact h k hk
    by_cases hX : X ∈ S
    · simp [F, Set.indicator_of_mem hX, Set.indicator_of_mem (hiff.mp hX)]
    · simp [F, Set.indicator_of_notMem hX,
        Set.indicator_of_notMem (fun h => hX (hiff.mpr h))]
  have hdeg : ∀ y : Site d, 0 < (lattice d).degree y := by
    intro y
    rw [Graph.Zd.degree_eq]
    omega
  have hint : (∫ X, F X ∂(siteWalkLaw d x)) =
      ∫ X, F X ∂(Graph.walkLaw (lattice d) x) := by
    calc ∫ X, F X ∂(siteWalkLaw d x) = Graph.walkExp (lattice d) n x F :=
          (LatticeProb.walkExp_eq_integral n x F hdep).symm
      _ = ∫ X, F X ∂(Graph.walkLaw (lattice d) x) :=
          Graph.walkExp_eq_integral hdeg n x F hFm 1 hFb hdep
  rw [← integral_indicator_one hS, hint, integral_indicator_one hS, measureReal_def,
    Graph.walkLaw_stayIn hdeg, ENNReal.toReal_ofReal (Network.survival_nonneg B n x)]

/-- If the one-block heat-kernel bound is at most one half, the probability of
confinement to the fixed set decays geometrically over successive blocks. -/
theorem measureReal_walkLaw_stayIn_le_half_pow (hd : 1 ≤ d) (B : Finset (Site d))
    (n : ℕ) (hn : 1 ≤ n)
    (hB : (B.card : ℝ) * (Real.sqrt 2 ^ d * greenConst d * (n : ℝ) ^ (-(d : ℝ) / 2))
      ≤ 1 / 2) (j k : ℕ) :
    (walkLaw d).real {p | ∀ i ≤ k + j * n, walkPath (0 : Site d) p i ∈ B}
      ≤ (1 / 2 : ℝ) ^ j := by
  have hsurv (x : Site d) : Network.survival (lattice d) B n x ≤ 1 / 2 := by
    have hkernel : Network.survival (lattice d) B n x ≤
        (B.card : ℝ) * (Real.sqrt 2 ^ d * greenConst d * (n : ℝ) ^ (-(d : ℝ) / 2)) := by
      rw [Network.survival]
      exact le_trans
        (Finset.sum_le_sum fun v _ => le_trans
          (GreenTwoSided.killedHeat_le_srwHeat_sub (B : Set (Site d)) n x v)
          (srwHeat_sup_bound hd hn (x - v)))
        (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul]))
    exact hkernel.trans hB
  have hpath : Measurable (walkPath (0 : Site d)) :=
    Measurable.of_eval fun i => measurable_walkPath 0 i
  have hS := Graph.measurableSet_stayIn (B : Set (Site d)) (k + j * n)
  have heq : (walkLaw d).real {p | ∀ i ≤ k + j * n, walkPath (0 : Site d) p i ∈ B} =
      (siteWalkLaw d 0).real (Graph.stayIn (B : Set (Site d)) (k + j * n)) := by
    rw [← map_walkLaw_walkPath hd (0 : Site d)]
    change ((walkLaw d) {p | ∀ i ≤ k + j * n, walkPath (0 : Site d) p i ∈ B}).toReal =
      (((walkLaw d).map (walkPath (0 : Site d)))
        (Graph.stayIn (B : Set (Site d)) (k + j * n))).toReal
    rw [Measure.map_apply hpath hS]
    rfl
  rw [heq, measureReal_siteWalkLaw_stayIn hd]
  exact Network.survival_le_pow (by norm_num : (0 : ℝ) ≤ 1 / 2) hsurv j k 0

end Parking

end
