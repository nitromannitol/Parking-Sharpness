/-
The `p`-th moment of `Parking.levelIncFixed R n m η` (`TightBoxSupBase.lean`'s fixed-radius
dyadic increment), bounded uniformly in the scale `n`, for a FIXED radius `R` at every level `m`
— the polynomial-in-`R` (not exponential-in-`m`) analogue of `TightBoxSupMoment.lean`'s
`exists_levelInc_moment`.  Same proof shape; the only change is the index set
(`Parking.levelPairsFixed R m` in place of `Parking.levelPairs m`) and its EXACT cardinality
`LatticeProb.card_boxIdx (R + 1) m = (2 * ((R + 1) * 2 ^ m) + 1) ^ 2`.
-/
import Parking.Support.TightBoxSupBase

open MeasureTheory LatticeProb Filter Topology

noncomputable section

namespace Parking

theorem measurable_levelIncFixed (A : ℝ) (hA : 0 ≤ A) (R n m : ℕ) :
    Measurable (fun η : Site 2 → ℝ => levelIncFixed A hA R n m η) := by
  have heq : (fun η : Site 2 → ℝ => levelIncFixed A hA R n m η) =
      (levelPairsFixed R m).sup' (levelPairsFixed_nonempty R m)
        (fun idx (η : Site 2 → ℝ) => levelIncTermFixed A hA n m η idx) := by
    funext η
    rw [levelIncFixed, Finset.sup'_apply]
  rw [heq]
  apply Finset.measurable_sup'
  intro idx _
  exact ((measurable_Yfield hA n
    (LatticeProb.gridPt m (idx.1 + Pi.single idx.2 1))).sub
    (measurable_Yfield hA n (LatticeProb.gridPt m idx.1))).abs

theorem card_levelPairsFixed (R m : ℕ) :
    ((levelPairsFixed R m).card : ℝ) = 2 * (2 * (((R : ℝ) + 1) * 2 ^ m) + 1) ^ 2 := by
  unfold levelPairsFixed
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  have hc := LatticeProb.card_boxIdx (k := 2) (R + 1) m
  rw [hc]
  push_cast
  ring

/-- **The `p`-th moment of `levelIncFixed` at level `m`, for ANY FIXED radius `R`, bounded by a
SINGLE constant `M` uniform in BOTH the radius `R` and the scale `n`** (the constant comes
entirely from `Parking.exists_Yfield_kolmogorov`'s own global bound, which does not depend on
`R` at all), with `M` itself bounded by
`Parking.orientedBoxRewardKolmogorovK ν hν p _ 1 * (1 + A) ^ (p / 2)`. -/
theorem exists_levelIncFixed_moment (ν : Measure ℤ) (hν : CriticalLaw ν) (p : ℝ) (hp8 : 8 < p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ) (hA : 0 ≤ A), ∃ M : ℝ, 0 ≤ M ∧ M ≤ K * (1 + A) ^ (p / 2) ∧
      ∀ (R n : ℕ), 1 ≤ n → ∀ m : ℕ,
      Integrable (fun η : Site 2 → ℝ => (levelIncFixed A hA R n m η) ^ p)
        (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, (levelIncFixed A hA R n m η) ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        M * (2 * (2 * (((R : ℝ) + 1) * 2 ^ m) + 1) ^ 2) * ((1 : ℝ) / 2 ^ m) ^ (p / 4) := by
  have hp2 : (2 : ℝ) ≤ p := by linarith
  obtain ⟨K, hKnn, hKall⟩ := exists_Yfield_kolmogorov ν hν p hp2
  refine ⟨K, hKnn, fun A hA => ?_⟩
  obtain ⟨M0, hM0, hM0bd, hb⟩ := hKall A hA
  refine ⟨M0, hM0, hM0bd, fun R n hn m => ?_⟩
  have hterm : ∀ idx ∈ levelPairsFixed R m,
      Integrable (fun η : Site 2 → ℝ => (levelIncTermFixed A hA n m η idx) ^ p)
        (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, (levelIncTermFixed A hA n m η idx) ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        M0 * ((1 : ℝ) / 2 ^ m) ^ (p / 4) := by
    rintro ⟨j, i⟩ -
    unfold levelIncTermFixed
    have hd := dist_gridPt_step m j i
    obtain ⟨hint, hbound⟩ := hb n hn (LatticeProb.gridPt m (j + Pi.single i 1))
      (LatticeProb.gridPt m j)
    rw [hd] at hbound
    exact ⟨hint, hbound⟩
  have hintSum : Integrable (fun η : Site 2 → ℝ =>
      ∑ idx ∈ levelPairsFixed R m, (levelIncTermFixed A hA n m η idx) ^ p)
        (iidLaw 2 (realLaw ν)) :=
    integrable_finsetSum (levelPairsFixed R m) fun idx hidx => (hterm idx hidx).1
  have hmeasPow : Measurable (fun η : Site 2 → ℝ => (levelIncFixed A hA R n m η) ^ p) := by
    have heq : (fun η : Site 2 → ℝ => (levelIncFixed A hA R n m η) ^ p) =
        (fun η : Site 2 → ℝ => |levelIncFixed A hA R n m η| ^ p) := by
      funext η
      rw [abs_of_nonneg (levelIncFixed_nonneg A hA R n m η)]
    rw [heq]
    exact LatticeProb.measurable_abs_rpow (measurable_levelIncFixed A hA R n m) p
  have hrpow_le : ∀ η : Site 2 → ℝ, (levelIncFixed A hA R n m η) ^ p ≤
      ∑ idx ∈ levelPairsFixed R m, (levelIncTermFixed A hA n m η idx) ^ p := by
    intro η
    obtain ⟨idx, hidx, heq⟩ :=
      Finset.exists_mem_eq_sup' (levelPairsFixed_nonempty R m) (levelIncTermFixed A hA n m η)
    rw [levelIncFixed, heq]
    exact Finset.single_le_sum
      (fun idx _ => Real.rpow_nonneg (levelIncTermFixed_nonneg A hA n m η idx) p) hidx
  have hintPow : Integrable (fun η : Site 2 → ℝ => (levelIncFixed A hA R n m η) ^ p)
      (iidLaw 2 (realLaw ν)) := by
    refine hintSum.mono' hmeasPow.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun η => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg
      (Real.rpow_nonneg (levelIncFixed_nonneg A hA R n m η) p)]
    exact hrpow_le η
  refine ⟨hintPow, ?_⟩
  calc (∫ η : Site 2 → ℝ, (levelIncFixed A hA R n m η) ^ p ∂(iidLaw 2 (realLaw ν)))
      ≤ ∫ η : Site 2 → ℝ, ∑ idx ∈ levelPairsFixed R m, (levelIncTermFixed A hA n m η idx) ^ p
          ∂(iidLaw 2 (realLaw ν)) :=
        integral_mono_ae hintPow hintSum (Filter.Eventually.of_forall hrpow_le)
    _ = ∑ idx ∈ levelPairsFixed R m, ∫ η : Site 2 → ℝ, (levelIncTermFixed A hA n m η idx) ^ p
          ∂(iidLaw 2 (realLaw ν)) :=
        integral_finsetSum (levelPairsFixed R m) fun idx hidx => (hterm idx hidx).1
    _ ≤ ∑ _idx ∈ levelPairsFixed R m, M0 * ((1 : ℝ) / 2 ^ m) ^ (p / 4) :=
        Finset.sum_le_sum fun idx hidx => (hterm idx hidx).2
    _ = ((levelPairsFixed R m).card : ℝ) * (M0 * ((1 : ℝ) / 2 ^ m) ^ (p / 4)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = M0 * (2 * (2 * (((R : ℝ) + 1) * 2 ^ m) + 1) ^ 2) * ((1 : ℝ) / 2 ^ m) ^ (p / 4) := by
        rw [card_levelPairsFixed]; ring

end Parking

end
