/-
The finite-range sum of `Parking.levelIncFixed`'s per-level moments, from level `1` to level
`R`, bounded by a constant TIMES `(R + 1) ^ 2` — polynomial in `R`, not exponential — via
`Parking.rpow_sum_range_le_geometric_weighted_sum` (`TightWeightedJensen.lean`), reused exactly
as built (no Fatou or summability needed: the range is finite once `R` is fixed).  This
completes `TightBoxSupBase.lean`'s route A: combined with `Parking.yfield_dtruncPi_dist_le_fixed`
(the deterministic telescoping bound), it gives a moment bound on `|Yfield(dtruncPi R z) -
Yfield(dtruncPi 0 z)|` uniform in the scale `n`, polynomial in `R`.
-/
import Parking.Support.TightBoxSupBaseMoment
import Parking.Support.TightWeightedJensen
import Parking.Support.TightBoxSupTail
import Parking.Generic.PolyGrowth

open MeasureTheory LatticeProb Filter Topology Parking.Generic.PolyGrowth

noncomputable section

namespace Parking

/-- **The finite-range geometric-tail moment bound**: for `p > 12`, the `p`-th moment of the
fixed-radius telescoping sum from level `1` to level `R` is bounded by a constant (depending
only on `p` and the underlying Kolmogorov constant) TIMES `(R + 1) ^ 2` — UNIFORM IN the scale
`n ≥ 1`, with the constant itself bounded by `K * (1 + A) ^ (p / 2)` for a SINGLE constant `K`,
chosen before `A` and independent of it. -/
theorem exists_levelIncFixed_sum_moment (ν : Measure ℤ) (hν : CriticalLaw ν) (p : ℝ)
    (hp : 12 < p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ) (hA : 0 ≤ A), ∃ C : ℝ, 0 ≤ C ∧
      C ≤ K * (1 + A) ^ (p / 2) ∧ ∀ (R n : ℕ), 1 ≤ n →
      Integrable (fun η : Site 2 → ℝ =>
          (∑ k ∈ Finset.range R, levelIncFixed A hA R n (k + 1) η) ^ p)
        (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, (∑ k ∈ Finset.range R, levelIncFixed A hA R n (k + 1) η) ^ p
          ∂(iidLaw 2 (realLaw ν))) ≤ C * (((R : ℝ) + 1) ^ 2) := by
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  set r : ℝ := jensenRatio p with hrdef
  have hr0 : 0 < r := jensenRatio_pos p
  have hr1 : r < 1 := jensenRatio_lt_one (by linarith)
  set θ0 : ℝ := (4 : ℝ) * (2 : ℝ) ^ (-(p / 4)) with hθ0def
  set θ : ℝ := r ^ (1 - p) * 4 * (2 : ℝ) ^ (-(p / 4)) with hθdef
  have hθeq : θ = 2 * θ0 := by
    rw [hθdef, hθ0def, jensenRatio_rpow_one_sub (by linarith : (1:ℝ) < p)]; ring
  have hθ1 : θ < 1 := jensenRatio_rpow_one_sub_mul_lt_one hp
  have hθpos : 0 < θ := by rw [hθeq]; positivity
  have hθ0pos : 0 < θ0 := by rw [hθ0def]; positivity
  obtain ⟨K0, hK0nn, hK0all⟩ := exists_levelIncFixed_moment ν hν p (by linarith : 8 < p)
  set K1 : ℝ := 18 with hK1def
  have hK1nn : 0 ≤ K1 := by rw [hK1def]; positivity
  have hsummable_geom : Summable (fun k : ℕ => θ ^ k) := summable_geometric_of_lt_one hθpos.le hθ1
  set S : ℝ := ∑' k : ℕ, θ ^ k with hSdef
  have hSnn : 0 ≤ S := tsum_nonneg fun k => by positivity
  have h1r_pos : (0:ℝ) < 1 - r := by linarith
  have hcoef_nn : (0 : ℝ) ≤ (1 - r) ^ (1 - p) * K1 * θ0 * S :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg h1r_pos.le _) hK1nn) hθ0pos.le) hSnn
  refine ⟨((1 - r) ^ (1 - p) * K1 * θ0 * S) * K0, mul_nonneg hcoef_nn hK0nn, fun A hA => ?_⟩
  obtain ⟨M0, hM0, hM0bd, hb⟩ := hK0all A hA
  set C : ℝ := (1 - r) ^ (1 - p) * (M0 * K1 * θ0 * S) with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  refine ⟨C, hCnn, ?_, fun R n hn => ?_⟩
  · -- The explicit polynomial-in-`A` bound on the witness `C`.
    have hstep : C ≤ ((1 - r) ^ (1 - p) * K1 * θ0 * S) *
        (K0 * (1 + A) ^ (p / 2)) := by
      rw [hCdef]
      have heq : (1 - r) ^ (1 - p) * (M0 * K1 * θ0 * S) =
          ((1 - r) ^ (1 - p) * K1 * θ0 * S) * M0 := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hM0bd hcoef_nn
    exact le_const_mul_of_le_one_add_rpow hstep
  set x : ℕ → (Site 2 → ℝ) → ℝ := fun k η => levelIncFixed A hA R n (k + 1) η with hxdef
  have hxnn : ∀ k η, 0 ≤ x k η := fun k η => levelIncFixed_nonneg A hA R n (k + 1) η
  rcases Nat.eq_zero_or_pos R with hR0 | hRpos
  · subst hR0
    simp only [Finset.range_zero, Finset.sum_empty]
    have hz : (0:ℝ) ^ p = 0 := Real.zero_rpow (by linarith)
    refine ⟨?_, ?_⟩
    · simp [hz]
    · simp only [hz, integral_zero]
      positivity
  have hpointwise : ∀ η : Site 2 → ℝ,
      (∑ k ∈ Finset.range R, x k η) ^ p ≤
        (1 - r) ^ (1 - p) * ∑ k ∈ Finset.range R, r ^ ((k : ℝ) * (1 - p)) * (x k η) ^ p := by
    intro η
    have hRcast : R - 1 + 1 = R := by omega
    have h := rpow_sum_range_le_geometric_weighted_sum (R - 1) (fun k => x k η)
      (fun k => hxnn k η) p (by linarith) r hr0 hr1
    rwa [hRcast] at h
  have hlevel : ∀ k : ℕ, Integrable (fun η => (x k η) ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η, (x k η) ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        M0 * (2 * (2 * (((R:ℝ) + 1) * 2 ^ (k+1)) + 1) ^ 2) * ((1 : ℝ) / 2 ^ (k+1)) ^ (p / 4) :=
    fun k => hb R n hn (k + 1)
  have hterm_int : ∀ k ∈ Finset.range R,
      Integrable (fun η => r ^ ((k : ℝ) * (1 - p)) * (x k η) ^ p) (iidLaw 2 (realLaw ν)) :=
    fun k _ => (hlevel k).1.const_mul _
  have hrhs_int : Integrable (fun η =>
      (1 - r) ^ (1 - p) * ∑ k ∈ Finset.range R, r ^ ((k : ℝ) * (1 - p)) * (x k η) ^ p)
      (iidLaw 2 (realLaw ν)) :=
    (integrable_finsetSum (Finset.range R) hterm_int).const_mul _
  have hmeas_x : ∀ k, Measurable (x k) := by
    intro k
    have heq : x k = (levelPairsFixed R (k+1)).sup' (levelPairsFixed_nonempty R (k+1))
        (fun idx (η : Site 2 → ℝ) => levelIncTermFixed A hA n (k+1) η idx) := by
      funext η
      simp only [hxdef, levelIncFixed, Finset.sup'_apply]
    rw [heq]
    apply Finset.measurable_sup'
    intro idx _
    exact ((measurable_Yfield hA n
      (LatticeProb.gridPt (k+1) (idx.1 + Pi.single idx.2 1))).sub
      (measurable_Yfield hA n (LatticeProb.gridPt (k+1) idx.1))).abs
  have hmeas_lhs : Measurable (fun η => (∑ k ∈ Finset.range R, x k η) ^ p) := by
    have hsummeas : Measurable (fun η => ∑ k ∈ Finset.range R, x k η) :=
      Finset.measurable_fun_sum (Finset.range R) fun k _ => hmeas_x k
    have heq : (fun η => (∑ k ∈ Finset.range R, x k η) ^ p) =
        (fun η => |∑ k ∈ Finset.range R, x k η| ^ p) := by
      funext η
      rw [abs_of_nonneg (Finset.sum_nonneg fun k _ => hxnn k η)]
    rw [heq]
    exact LatticeProb.measurable_abs_rpow hsummeas p
  have hlhs_int : Integrable (fun η => (∑ k ∈ Finset.range R, x k η) ^ p)
      (iidLaw 2 (realLaw ν)) := by
    refine hrhs_int.mono' hmeas_lhs.aestronglyMeasurable (Filter.Eventually.of_forall fun η => ?_)
    have hnn : (0:ℝ) ≤ (∑ k ∈ Finset.range R, x k η) ^ p :=
      Real.rpow_nonneg (Finset.sum_nonneg fun k _ => hxnn k η) p
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hpointwise η
  refine ⟨hlhs_int, ?_⟩
  have hrpow_eq : ∀ k : ℕ, r ^ ((k : ℝ) * (1 - p)) = (2:ℝ) ^ (k : ℕ) := by
    intro k
    rw [show (k:ℝ) * (1-p) = (1-p) * (k:ℝ) by ring, Real.rpow_mul hr0.le,
      jensenRatio_rpow_one_sub (by linarith : (1:ℝ) < p), Real.rpow_natCast]
  have hcard_le : ∀ k : ℕ, 2 * (2 * (((R:ℝ) + 1) * 2 ^ (k+1)) + 1) ^ 2 ≤
      18 * (((R:ℝ)+1)) ^ 2 * (4:ℝ)^(k+1) := by
    intro k
    have hy1 : (1:ℝ) ≤ ((R:ℝ)+1) * 2^(k+1) := by
      have hR1 : (1:ℝ) ≤ (R:ℝ)+1 := by
        have := Nat.cast_nonneg (α := ℝ) R
        linarith
      have h2 : (1:ℝ) ≤ (2:ℝ)^(k+1) := one_le_pow₀ (by norm_num)
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ ((R:ℝ)+1) * 2^(k+1) := mul_le_mul hR1 h2 (by norm_num) (by positivity)
    have hstep : 2 * (((R:ℝ)+1) * 2^(k+1)) + 1 ≤ 3 * (((R:ℝ)+1) * 2^(k+1)) := by linarith
    have hsq : (2 * (((R:ℝ) + 1) * 2 ^ (k+1)) + 1) ^ 2 ≤
        (3 * (((R:ℝ)+1) * 2^(k+1))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hstep 2
    calc 2 * (2 * (((R:ℝ) + 1) * 2 ^ (k+1)) + 1) ^ 2
        ≤ 2 * (3 * (((R:ℝ)+1) * 2^(k+1))) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = 18 * (((R:ℝ)+1)) ^ 2 * (4:ℝ)^(k+1) := by
          rw [show (4:ℝ)^(k+1) = (2:ℝ)^(k+1) * (2:ℝ)^(k+1) from by rw [← mul_pow]; norm_num]
          ring
  have hexp_eq : ∀ k : ℕ, (4:ℝ)^(k+1) * ((1:ℝ)/2^(k+1))^(p/4) = θ0 ^ (k+1) := by
    intro k
    have hA1 : ((1:ℝ) / 2 ^ (k+1)) ^ (p / 4) = (2:ℝ) ^ (-(p / 4) * ((k:ℝ)+1)) := by
      rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_natCast (2:ℝ) (k+1),
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      push_cast; ring
    have hA2 : ((2:ℝ) ^ (-(p/4))) ^ (k+1) = (2:ℝ) ^ (-(p/4) * ((k:ℝ)+1)) := by
      rw [← Real.rpow_natCast ((2:ℝ) ^ (-(p/4))) (k+1), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      push_cast; ring
    rw [hA1, hθ0def, mul_pow, hA2]
  have hrθ : ∀ k : ℕ, (2:ℝ)^k * θ0^(k+1) = θ0 * θ^k := by
    intro k
    have hsp : θ0 ^ (k+1) = θ0 * θ0^k := by ring
    rw [hsp, hθeq]
    ring
  have hterm_bound : ∀ k ∈ Finset.range R,
      (∫ η, r ^ ((k : ℝ) * (1 - p)) * (x k η) ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        M0 * K1 * θ0 * (((R:ℝ)+1)) ^ 2 * θ ^ k := by
    intro k _
    rw [integral_const_mul]
    calc r ^ ((k:ℝ)*(1-p)) * (∫ η, (x k η) ^ p ∂(iidLaw 2 (realLaw ν)))
        ≤ r ^ ((k:ℝ)*(1-p)) * (M0 * (2 * (2 * (((R:ℝ) + 1) * 2 ^ (k+1)) + 1) ^ 2) *
            ((1 : ℝ) / 2 ^ (k+1)) ^ (p / 4)) :=
          mul_le_mul_of_nonneg_left (hlevel k).2 (Real.rpow_nonneg hr0.le _)
      _ ≤ r ^ ((k:ℝ)*(1-p)) * (M0 * (18 * (((R:ℝ)+1)) ^ 2 * (4:ℝ)^(k+1)) *
            ((1 : ℝ) / 2 ^ (k+1)) ^ (p / 4)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hr0.le _)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (hcard_le k) hM0
      _ = r ^ ((k:ℝ)*(1-p)) * (M0 * 18 * (((R:ℝ)+1))^2 *
            ((4:ℝ)^(k+1) * ((1:ℝ)/2^(k+1))^(p/4))) := by
          ring
      _ = (2:ℝ)^k * (M0 * 18 * (((R:ℝ)+1))^2 * θ0^(k+1)) := by
          rw [hrpow_eq k, hexp_eq k]
      _ = M0 * K1 * (((R:ℝ)+1))^2 * ((2:ℝ)^k * θ0^(k+1)) := by
          rw [hK1def]; ring

      _ = M0 * K1 * θ0 * (((R:ℝ)+1)) ^ 2 * θ ^ k := by
          rw [hrθ k]; ring
  calc (∫ η, (∑ k ∈ Finset.range R, x k η) ^ p ∂(iidLaw 2 (realLaw ν)))
      ≤ ∫ η, (1 - r) ^ (1 - p) * ∑ k ∈ Finset.range R,
          r ^ ((k : ℝ) * (1 - p)) * (x k η) ^ p ∂(iidLaw 2 (realLaw ν)) :=
        integral_mono_ae hlhs_int hrhs_int (Filter.Eventually.of_forall hpointwise)
    _ = (1 - r) ^ (1 - p) * ∑ k ∈ Finset.range R,
          ∫ η, r ^ ((k : ℝ) * (1 - p)) * (x k η) ^ p ∂(iidLaw 2 (realLaw ν)) := by
        rw [integral_const_mul, integral_finsetSum _ hterm_int]
    _ ≤ (1 - r) ^ (1 - p) * ∑ k ∈ Finset.range R,
          M0 * K1 * θ0 * (((R:ℝ)+1)) ^ 2 * θ ^ k :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm_bound) (Real.rpow_nonneg h1r_pos.le _)
    _ = (1 - r) ^ (1 - p) * (M0 * K1 * θ0 * (((R:ℝ)+1)) ^ 2) *
          ∑ k ∈ Finset.range R, θ ^ k := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ ≤ (1 - r) ^ (1 - p) * (M0 * K1 * θ0 * (((R:ℝ)+1)) ^ 2) * S :=
        mul_le_mul_of_nonneg_left
          (hsummable_geom.sum_le_tsum (Finset.range R) (fun k _ => by positivity))
          (by positivity)
    _ = C * (((R:ℝ) + 1) ^ 2) := by
        rw [hCdef]; ring

end Parking

end
