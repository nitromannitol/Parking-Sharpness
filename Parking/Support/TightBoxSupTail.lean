/-
The geometric-tail moment bound on the dyadic increments of `Parking.Yfield`, from
`Parking/Support/TightBoxSupMoment.lean`'s `exists_levelInc_moment`.  The per-level moment
bounds are summed, via `Parking.rpow_sum_range_le_geometric_weighted_sum`
(`TightWeightedJensen.lean`), into a bound on `E[(Σ_{k < N} levelInc(n1 + 1 + k))^p]` UNIFORM IN
BOTH the scale `n` and the range `N`.  The argument needs no Minkowski inequality and no
`ENNReal`/`eLpNorm` bookkeeping.

The geometric ratio `Parking.jensenRatio p := 2 ^ (-1 / (p - 1))` is chosen so that, for
`p > 12`, the per-level decay `4 ^ m * (1 / 2 ^ m) ^ (p / 4)` of `exists_levelInc_moment`
combines with the weighted-Jensen ratio `r ^ (1 - p)` (at `r := jensenRatio p`) into an overall
geometric ratio `θ = 2 ^ (3 - p / 4) < 1`, making the resulting series
`Σ_k (k + 1) ^ 2 * θ ^ k` summable (`LatticeProb.summable_polynomial_geometric`).
-/
import Parking.Support.TightBoxSupMoment
import Parking.Support.TightWeightedJensen
import Parking.Generic.PolyGrowth

open MeasureTheory LatticeProb Filter Topology Parking.Generic.PolyGrowth

noncomputable section

namespace Parking

/-! ### The Jensen ratio -/

/-- **The geometric ratio used to weight the Jensen inequality.**  Chosen so that
`(jensenRatio p) ^ (1 - p) = 2` exactly. -/
def jensenRatio (p : ℝ) : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / (p - 1))

theorem jensenRatio_pos (p : ℝ) : 0 < jensenRatio p :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem jensenRatio_lt_one {p : ℝ} (hp : 1 < p) : jensenRatio p < 1 := by
  unfold jensenRatio
  refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  exact div_neg_of_neg_of_pos (by norm_num) hp1

theorem jensenRatio_rpow_one_sub {p : ℝ} (hp : 1 < p) :
    (jensenRatio p) ^ (1 - p) = 2 := by
  unfold jensenRatio
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hp1 : p - 1 ≠ 0 := by linarith
  have hexp : -(1 : ℝ) / (p - 1) * (1 - p) = 1 := by
    field_simp
    ring
  rw [hexp, Real.rpow_one]

/-- **The overall geometric decay ratio, `θ(p) = 2 ^ (3 - p / 4)`, is below `1` for `p > 12`.** -/
theorem jensenRatio_rpow_one_sub_mul_lt_one {p : ℝ} (hp : 12 < p) :
    (jensenRatio p) ^ (1 - p) * 4 * (2 : ℝ) ^ (-(p / 4)) < 1 := by
  have hval : (2:ℝ) * 4 * (2:ℝ) ^ (-(p/4)) = (2:ℝ) ^ (3 - p/4) := by
    have h8 : (2:ℝ) * 4 = (2:ℝ) ^ (3:ℝ) := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    rw [h8, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
  rw [jensenRatio_rpow_one_sub (by linarith : (1:ℝ) < p), hval]
  calc (2:ℝ) ^ (3 - p/4) < (2:ℝ) ^ (0:ℝ) :=
        (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr (by linarith)
    _ = 1 := Real.rpow_zero 2

/-! ### The tail moment bound -/

set_option maxHeartbeats 1000000 in
/-- **The geometric-tail moment bound**: for `p > 12`, the `p`-th moment of the partial sum of
`levelInc` starting after a fixed level `n1` is bounded UNIFORMLY IN BOTH the scale `n ≥ 1` and
the number of terms `N`, with the constant itself bounded by `K * (1 + A) ^ (p / 2)` for a
SINGLE constant `K`, chosen before `A` and independent of it. -/
theorem exists_levelInc_tail_moment (ν : Measure ℤ) (hν : CriticalLaw ν) (p : ℝ) (hp : 12 < p)
    (n1 : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ) (hA : 0 ≤ A), ∃ C : ℝ, 0 ≤ C ∧ C ≤ K * (1 + A) ^ (p / 2) ∧
      ∀ (n N : ℕ), 1 ≤ n →
      Integrable (fun η : Site 2 → ℝ =>
          (∑ k ∈ Finset.range (N + 1), levelInc A hA n (n1 + 1 + k) η) ^ p)
        (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ,
          (∑ k ∈ Finset.range (N + 1), levelInc A hA n (n1 + 1 + k) η) ^ p
          ∂(iidLaw 2 (realLaw ν))) ≤ C := by
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  set r : ℝ := jensenRatio p with hrdef
  have hr0 : 0 < r := jensenRatio_pos p
  have hr1 : r < 1 := jensenRatio_lt_one (by linarith)
  set θ : ℝ := r ^ (1 - p) * 4 * (2 : ℝ) ^ (-(p / 4)) with hθdef
  have hθ1 : θ < 1 := jensenRatio_rpow_one_sub_mul_lt_one hp
  have hθ0 : 0 < θ := by
    rw [hθdef]
    have := jensenRatio_pos p
    positivity
  obtain ⟨K0, hK0nn, hK0all⟩ := exists_levelInc_moment ν hν p (by linarith : 8 < p)
  set coef : ℝ := ((n1 : ℝ) + 2) ^ 2 * (1 - r) ^ (1 - p) *
      (2 * (3 ^ 2 * (4 : ℝ) ^ (n1 + 1) * ((1 : ℝ) / 2 ^ (n1 + 1)) ^ (p / 4))) with hcoefdef
  have h1r_pos : (0:ℝ) < 1 - r := by linarith
  have hcoefnn : (0 : ℝ) ≤ coef := by
    rw [hcoefdef]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg h1r_pos.le _)) (by positivity)
  have hsummable_geom : Summable (fun k : ℕ => θ ^ k) := summable_geometric_of_lt_one hθ0.le hθ1
  set S : ℝ := ∑' k : ℕ, ((k : ℝ) + 1) ^ 2 * θ ^ k with hSdef
  have hSnn : (0 : ℝ) ≤ S := tsum_nonneg fun k => by positivity
  refine ⟨(coef * S) * K0, mul_nonneg (mul_nonneg hcoefnn hSnn) hK0nn, fun A hA => ?_⟩
  obtain ⟨M0, hM0, hM0bd, hb⟩ := hK0all A hA
  set K0' : ℝ := (1 - r) ^ (1 - p) *
      (M0 * (2 * (3 ^ 2 * ((4:ℝ)) ^ (n1 + 1) * ((1:ℝ) / 2 ^ (n1 + 1)) ^ (p / 4)))) with hK0def
  set C0 : ℝ := ((n1 : ℝ) + 2) ^ 2 * K0' with hC0def
  have hC0nn : 0 ≤ C0 := by
    rw [hC0def, hK0def]
    positivity
  have hsummable : Summable (fun k : ℕ => C0 * ((k : ℝ) + 1) ^ 2 * θ ^ k) :=
    LatticeProb.summable_polynomial_geometric 2 hθ0 hθ1
  set C : ℝ := ∑' k : ℕ, C0 * ((k : ℝ) + 1) ^ 2 * θ ^ k with hCdef
  have hCnn : 0 ≤ C := tsum_nonneg fun k => by positivity
  refine ⟨C, hCnn, ?_, fun n N hn => ?_⟩
  · -- The explicit polynomial-in-`A` bound on the witness `C`.
    have hCeq : C = (coef * M0) * S := by
      rw [hCdef, hSdef, ← tsum_mul_left]
      refine tsum_congr fun k => ?_
      rw [hC0def, hK0def, hcoefdef]
      ring
    have hstep : C ≤ (coef * S) * (K0 * (1 + A) ^ (p / 2)) := by
      rw [hCeq]
      calc (coef * M0) * S
          ≤ (coef * (K0 * (1 + A) ^ (p / 2))) * S :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM0bd hcoefnn) hSnn
        _ = (coef * S) * (K0 * (1 + A) ^ (p / 2)) := by ring
    exact le_const_mul_of_le_one_add_rpow hstep
  set x : ℕ → (Site 2 → ℝ) → ℝ := fun k η => levelInc A hA n (n1 + 1 + k) η with hxdef
  have hxnn : ∀ k η, 0 ≤ x k η := fun k η => levelInc_nonneg A hA n (n1 + 1 + k) η
  have hpointwise : ∀ η : Site 2 → ℝ,
      (∑ k ∈ Finset.range (N + 1), x k η) ^ p ≤
        (1 - r) ^ (1 - p) * ∑ k ∈ Finset.range (N + 1), r ^ ((k : ℝ) * (1 - p)) * (x k η) ^ p :=
    fun η => rpow_sum_range_le_geometric_weighted_sum N (fun k => x k η) (fun k => hxnn k η)
      p (by linarith) r hr0 hr1
  -- Each level's `p`-th moment is integrable, and its integral is bounded.
  have hlevel : ∀ k : ℕ, Integrable (fun η => (x k η) ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η, (x k η) ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        M0 * (2 * (3 ^ 2 * (((n1 + 1 + k : ℕ) : ℝ) + 1) ^ 2 * (2 ^ 2) ^ (n1 + 1 + k))) *
          ((1 : ℝ) / 2 ^ (n1 + 1 + k)) ^ (p / 4) :=
    fun k => hb n hn (n1 + 1 + k)
  -- Integrability of each weighted term, and of the LHS/RHS finite sums.
  have hterm_int : ∀ k ∈ Finset.range (N + 1),
      Integrable (fun η => r ^ ((k : ℝ) * (1 - p)) * (x k η) ^ p) (iidLaw 2 (realLaw ν)) :=
    fun k _ => (hlevel k).1.const_mul _
  have hrhs_int : Integrable (fun η =>
      (1 - r) ^ (1 - p) * ∑ k ∈ Finset.range (N + 1), r ^ ((k : ℝ) * (1 - p)) * (x k η) ^ p)
      (iidLaw 2 (realLaw ν)) :=
    (integrable_finsetSum (Finset.range (N + 1)) hterm_int).const_mul _
  have hmeas_x : ∀ k, Measurable (x k) := by
    intro k
    have heq : x k = (levelPairs (n1 + 1 + k)).sup' (levelPairs_nonempty (n1 + 1 + k))
        (fun idx (η : Site 2 → ℝ) => levelIncTerm A hA n (n1 + 1 + k) η idx) := by
      funext η
      simp only [hxdef, levelInc_eq_sup', Finset.sup'_apply]
    rw [heq]
    apply Finset.measurable_sup'
    intro idx _
    exact ((measurable_Yfield hA n
      (LatticeProb.gridPt (n1 + 1 + k) (idx.1 + Pi.single idx.2 1))).sub
      (measurable_Yfield hA n (LatticeProb.gridPt (n1 + 1 + k) idx.1))).abs
  have hmeas_lhs : Measurable (fun η => (∑ k ∈ Finset.range (N + 1), x k η) ^ p) := by
    have hsummeas : Measurable (fun η => ∑ k ∈ Finset.range (N + 1), x k η) :=
      Finset.measurable_fun_sum (Finset.range (N + 1)) fun k _ => hmeas_x k
    have heq : (fun η => (∑ k ∈ Finset.range (N + 1), x k η) ^ p) =
        (fun η => |∑ k ∈ Finset.range (N + 1), x k η| ^ p) := by
      funext η
      rw [abs_of_nonneg (Finset.sum_nonneg fun k _ => hxnn k η)]
    rw [heq]
    exact LatticeProb.measurable_abs_rpow hsummeas p
  have hlhs_int : Integrable (fun η => (∑ k ∈ Finset.range (N + 1), x k η) ^ p)
      (iidLaw 2 (realLaw ν)) := by
    refine hrhs_int.mono' hmeas_lhs.aestronglyMeasurable (Filter.Eventually.of_forall fun η => ?_)
    have hnn : (0:ℝ) ≤ (∑ k ∈ Finset.range (N + 1), x k η) ^ p :=
      Real.rpow_nonneg (Finset.sum_nonneg fun k _ => hxnn k η) p
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hpointwise η
  refine ⟨hlhs_int, ?_⟩
  -- Bound each term's integral.
  have hrpow_eq : ∀ k : ℕ, r ^ ((k : ℝ) * (1 - p)) = (2:ℝ) ^ (k : ℕ) := by
    intro k
    rw [show (k:ℝ) * (1-p) = (1-p) * (k:ℝ) by ring, Real.rpow_mul hr0.le,
      jensenRatio_rpow_one_sub (by linarith : (1:ℝ) < p), Real.rpow_natCast]
  have hexpand : ∀ k : ℕ, (2 ^ 2 : ℝ) ^ (n1 + 1 + k) *
      ((1:ℝ) / 2 ^ (n1 + 1 + k)) ^ (p / 4) =
        ((4:ℝ) ^ (n1 + 1) * ((1:ℝ) / 2 ^ (n1 + 1)) ^ (p / 4)) *
          ((4:ℝ) ^ k * ((1:ℝ) / 2 ^ k) ^ (p / 4)) := by
    intro k
    have h4 : (2 ^ 2 : ℝ) ^ (n1 + 1 + k) = (4:ℝ) ^ (n1 + 1) * (4:ℝ) ^ k := by
      rw [show (2^2:ℝ) = 4 by norm_num, pow_add]
    have hhalf : ((1:ℝ) / 2 ^ (n1 + 1 + k)) ^ (p / 4) =
        ((1:ℝ) / 2 ^ (n1 + 1)) ^ (p / 4) * ((1:ℝ) / 2 ^ k) ^ (p / 4) := by
      rw [pow_add, ← Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      rw [div_mul_div_comm, one_mul]
    rw [h4, hhalf]
    ring
  have hpow_rpow : ∀ k : ℕ, ((1:ℝ) / 2 ^ k) ^ (p / 4) = (2:ℝ) ^ (-(p / 4) * (k : ℝ)) := by
    intro k
    rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_natCast (2:ℝ) k,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  have hrθ : ∀ k : ℕ, (2:ℝ) ^ k * ((4:ℝ) ^ k * ((1:ℝ) / 2 ^ k) ^ (p / 4)) = θ ^ k := by
    intro k
    rw [hpow_rpow k, hθdef, jensenRatio_rpow_one_sub (by linarith : (1:ℝ) < p), mul_pow, mul_pow]
    rw [show ((2:ℝ) ^ (-(p/4))) ^ k = (2:ℝ) ^ (-(p/4) * (k:ℝ)) from by
      rw [← Real.rpow_natCast ((2:ℝ) ^ (-(p/4))) k, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]]
    ring
  have hcombined : ∀ k : ℕ, r ^ ((k : ℝ) * (1 - p)) *
      (((2:ℝ) ^ 2) ^ (n1 + 1 + k) * ((1:ℝ) / 2 ^ (n1 + 1 + k)) ^ (p / 4)) =
        ((4:ℝ) ^ (n1 + 1) * ((1:ℝ) / 2 ^ (n1 + 1)) ^ (p / 4)) * θ ^ k := by
    intro k
    rw [hexpand k, hrpow_eq k]
    rw [show (2:ℝ) ^ k * (((4:ℝ) ^ (n1 + 1) * ((1:ℝ) / 2 ^ (n1 + 1)) ^ (p / 4)) *
        ((4:ℝ) ^ k * ((1:ℝ) / 2 ^ k) ^ (p / 4))) =
          ((4:ℝ) ^ (n1 + 1) * ((1:ℝ) / 2 ^ (n1 + 1)) ^ (p / 4)) *
            ((2:ℝ) ^ k * ((4:ℝ) ^ k * ((1:ℝ) / 2 ^ k) ^ (p / 4))) from by ring]
    rw [hrθ k]
  have hterm_bound : ∀ k ∈ Finset.range (N + 1),
      (∫ η, r ^ ((k : ℝ) * (1 - p)) * (x k η) ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        (M0 * (2 * (3 ^ 2 * ((4:ℝ)) ^ (n1 + 1) * ((1:ℝ)/2^(n1+1)) ^ (p/4)))) *
          ((n1 : ℝ) + 2) ^ 2 * ((k:ℝ)+1) ^ 2 * θ ^ k := by
    intro k _
    rw [integral_const_mul]
    have hpow2 : ((((n1 + 1 + k : ℕ) : ℝ)) + 1) ^ 2 ≤ (((n1 : ℝ) + 2) * ((k : ℝ) + 1)) ^ 2 := by
      have h1 : (((n1 + 1 + k : ℕ) : ℝ)) + 1 ≤ ((n1 : ℝ) + 2) * ((k : ℝ) + 1) := by
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) n1, Nat.cast_nonneg (α := ℝ) k]
      have hnn1 : (0:ℝ) ≤ (((n1 + 1 + k : ℕ) : ℝ)) + 1 := by positivity
      exact pow_le_pow_left₀ hnn1 h1 2
    calc r ^ ((k:ℝ)*(1-p)) * (∫ η, (x k η) ^ p ∂(iidLaw 2 (realLaw ν)))
        ≤ r ^ ((k:ℝ)*(1-p)) * (M0 * (2 * (3 ^ 2 *
            (((n1 + 1 + k : ℕ) : ℝ) + 1) ^ 2 * (2 ^ 2) ^ (n1 + 1 + k))) *
              ((1 : ℝ) / 2 ^ (n1 + 1 + k)) ^ (p / 4)) :=
          mul_le_mul_of_nonneg_left (hlevel k).2 (Real.rpow_nonneg hr0.le _)
      _ ≤ r ^ ((k:ℝ)*(1-p)) * (M0 * (2 * (3 ^ 2 *
            (((n1 : ℝ) + 2) * ((k:ℝ)+1)) ^ 2 * (2 ^ 2) ^ (n1 + 1 + k))) *
              ((1 : ℝ) / 2 ^ (n1 + 1 + k)) ^ (p / 4)) := by
          gcongr
      _ = (M0 * (2 * (3 ^ 2 * ((4:ℝ)) ^ (n1 + 1) * ((1:ℝ)/2^(n1+1)) ^ (p/4)))) *
            ((n1 : ℝ) + 2) ^ 2 * ((k:ℝ)+1) ^ 2 * θ ^ k := by
          linear_combination (M0 * (2 * (3 ^ 2 * (((n1 : ℝ) + 2) * ((k:ℝ)+1)) ^ 2))) * hcombined k
  calc (∫ η, (∑ k ∈ Finset.range (N + 1), x k η) ^ p ∂(iidLaw 2 (realLaw ν)))
      ≤ ∫ η, (1 - r) ^ (1 - p) * ∑ k ∈ Finset.range (N + 1),
          r ^ ((k : ℝ) * (1 - p)) * (x k η) ^ p ∂(iidLaw 2 (realLaw ν)) :=
        integral_mono_ae hlhs_int hrhs_int (Filter.Eventually.of_forall hpointwise)
    _ = (1 - r) ^ (1 - p) * ∑ k ∈ Finset.range (N + 1),
          ∫ η, r ^ ((k : ℝ) * (1 - p)) * (x k η) ^ p ∂(iidLaw 2 (realLaw ν)) := by
        rw [integral_const_mul, integral_finsetSum _ hterm_int]
    _ ≤ (1 - r) ^ (1 - p) * ∑ k ∈ Finset.range (N + 1),
          (M0 * (2 * (3 ^ 2 * ((4:ℝ)) ^ (n1 + 1) * ((1:ℝ)/2^(n1+1)) ^ (p/4)))) *
            ((n1 : ℝ) + 2) ^ 2 * ((k:ℝ)+1) ^ 2 * θ ^ k :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm_bound) (Real.rpow_nonneg h1r_pos.le _)
    _ = ∑ k ∈ Finset.range (N + 1), C0 * ((k : ℝ) + 1) ^ 2 * θ ^ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hC0def, hK0def]
        ring
    _ ≤ ∑' k : ℕ, C0 * ((k : ℝ) + 1) ^ 2 * θ ^ k :=
        hsummable.sum_le_tsum (Finset.range (N + 1)) (fun k _ => by positivity)
    _ = C := rfl

end Parking

end
