/-
The covariance of the rescaled oriented grid reward converges to the continuum
overlap kernel (`parking.tex:3192-3203`): the local-CLT Riemann sum.

The grid reward field of `Parking/Support/TightKolmogorov.lean` has, under the
i.i.d. scenery, an exact covariance of `n^{-1/2} · Var · greenCross`, which on
the layer diagonal collapses to `n^{-1/2} · Var · orientedCovSum`
(`Parking/Support/TightCovGreen.lean`).  Each summand of `orientedCovSum` is a
binomial mass, so the binomial local central limit theorem
(`Parking/External/BinomialLocalCLT.lean`) turns the sum into a Riemann sum of
the heat kernel over the common window, which converges to the overlap kernel
`contOverlap` of `Parking/Support/TightOverlap.lean`.

- `Parking.heatApprox`: the Gaussian profile `√(2/π)·(√a)⁻¹·exp(−v²/(2a))`
  produced by the local CLT, with its mean-value bounds.
- `Parking.abs_binomLaw_sub_heatApprox_le`: the local CLT applied to the
  diagonal covariance summand.
- `Parking.tendsto_riemann_sum_Ioo_of_continuousOn`: Riemann sums of a
  continuous integrand along a drifting endpoint.
- `Parking.tendsto_riemann_sum_singular_Ioo`: the same for the diagonal
  singularity `θ ↦ (πθ)^{-1/2}`, by monotonicity.
- `Parking.tendsto_riemann_sum_Ioo_param_pos`, `Parking.tendsto_riemann_sum_Ioo_same_time`:
  the same convergence along a jointly drifting delay/displacement, in the two remaining
  geometric regimes (different rescaled times; the same rescaled time with a drifting
  nonzero displacement).  Together with the two lemmas above, these are the four cases the
  covariance limit needs.
- `Parking.tendsto_orientedCovSum_of_pos`, `Parking.tendsto_orientedCovSum_of_eq`: the
  binomial covariance sum `orientedCovSum` itself (not just the heat-kernel Riemann sum it
  approximates) converges to the heat-kernel integral, transported through
  `Parking.External.BinomialLocalCLT` via the shared bridge lemma
  `Parking.abs_sum_binomLaw_sub_contHeat_le`.  Between them these cover all three
  geometrically distinct cases (different rescaled times; the diagonal; the same rescaled
  time with different space).
- `Parking.tendsto_integral_orientedGridReward_mul_of_pos`,
  `Parking.tendsto_integral_orientedGridReward_mul_of_eq`: the covariance limit itself, for
  the actual grid reward field `Parking.orientedGridReward` at two grid-point sequences
  `(m n, j n)`, `(m' n, j' n)` satisfying the matching asymptotic hypotheses, via
  `Parking.integral_orientedGridReward_mul` and `Parking.greenCross_layerPoint_sub_of_le`.
- `Parking.tendsto_int_floor_sub_div_atTop`, `Parking.tendsto_int_floor_mul_div`,
  `Parking.tendsto_int_floor_sub_div`: the floor-asymptotics engine.  Every `Int.floor`
  error is bounded by `1`, uniformly, so it vanishes after dividing by anything tending to
  infinity; this alone gives the signed floor limit `⌊n·x⌋/n → x` for every sign of `x`, and
  the difference-of-floors limit that both `m n = ⌊n·s⌋` and `j n = ⌊√n·y + n·s/2⌋` need.
- `Parking.contOverlap_eq_intervalIntegral_of_le`: `contOverlap` unfolded as a plain interval
  integral for the earlier point first, matching the shape the covariance-limit theorems
  produce.
- `Parking.tendsto_integral_orientedGridReward_mul_box_of_le`,
  `Parking.tendsto_integral_orientedGridReward_mul_box`: **the real-box-point covariance
  limit.**  The two grid-point theorems above, instantiated at the actual floor sequences
  `m n = ⌊n·s⌋`, `j n = ⌊√n·y + n·s/2⌋` of `Parking.orientedBoxReward` for two real box
  points `u = (s,y)`, `u' = (s',y')` of `Parking.orientedBox`, matched against
  `Parking.contOverlap` directly from its own definition.  This is Stage 1 of
  `parking.tex:3192-3203` in full: the covariance of the grid reward field at any two real
  box points converges to `Var(η) · contOverlap T u u'`.
-/
import Parking.Support.TightCovGreen
import Parking.Support.TightOverlap
import Parking.Support.TightWalk
import Parking.External.BinomialLocalCLT

open MeasureTheory LatticeProb Finset Filter
open scoped Topology

noncomputable section
namespace Parking

/-- The binomial mass is at most one. -/
theorem binomLaw_le_one (l : ℕ) (j : ℤ) : binomLaw l j ≤ 1 := by
  by_cases hj : j ∈ Icc (0 : ℤ) (l : ℤ)
  · exact (single_le_sum (fun i _ => binomLaw_nonneg l i) hj).trans_eq (sum_binomLaw l)
  · rw [binomLaw_zero_outside hj]
    exact zero_le_one

/-- The algebraic inequality behind the summability of `(t√t)⁻¹` along the
step-2 grid: for `t ≥ 2`, `(t√t)⁻¹ ≤ 2·((√t)⁻¹ − (√(t+2))⁻¹)`. -/
theorem inv_mul_sqrt_le_two_mul {t : ℝ} (ht : 2 ≤ t) :
    (t * √t)⁻¹ ≤ 2 * ((√t)⁻¹ - (√(t + 2))⁻¹) := by
  have ht0 : (0:ℝ) < t := lt_of_lt_of_le two_pos ht
  have hp : 0 < √t := Real.sqrt_pos.mpr ht0
  have hq : 0 < √(t + 2) := Real.sqrt_pos.mpr (by linarith)
  have hsqq : √(t + 2) * √(t + 2) = t + 2 := Real.mul_self_sqrt (by linarith)
  have hsqp : √t * √t = t := Real.mul_self_sqrt ht0.le
  have key : √t * √(t + 2) ≤ 3 * t - 2 := by
    have hsq : √t * √(t + 2) = √(t * (t + 2)) := (Real.sqrt_mul ht0.le (t + 2)).symm
    rw [hsq, Real.sqrt_le_iff]
    refine ⟨by linarith, ?_⟩
    have hprod : (0:ℝ) ≤ (t - 2) * (8 * t + 2) := by positivity
    nlinarith
  have e : 2 * ((√t)⁻¹ - (√(t + 2))⁻¹)
      = 4 / (√t * √(t + 2) * (√t + √(t + 2))) := by
    field_simp [hp.ne', hq.ne']
    nlinarith [hsqq, hsqp]
  rw [e, inv_eq_one_div, div_le_div_iff₀ (mul_pos ht0 hp)
    (mul_pos (mul_pos hp hq) (add_pos hp hq)), one_mul]
  have hA : √t * √(t + 2) * (√t + √(t + 2))
      = √t * (√t * √(t + 2)) + √t * (√(t + 2) * √(t + 2)) := by ring
  have hstep : √t * √(t + 2) * (√t + √(t + 2)) ≤ √t * (3 * t - 2) + √t * (t + 2) := by
    rw [hA, hsqq]
    exact add_le_add (mul_le_mul_of_nonneg_left key hp.le) (le_refl _)
  have hfin : √t * (3 * t - 2) + √t * (t + 2) = 4 * (t * √t) := by ring
  exact hstep.trans hfin.le

/-- **Summability of the local-CLT error profile**: the sum of
`((2i+D)√(2i+D))⁻¹` over `i < M` is at most `3`, uniformly in `D` and `M`. -/
theorem sum_range_two_mul_add_inv_le (D M : ℕ) :
    ∑ i ∈ range M, (((2 * i + D : ℕ) : ℝ) * √(((2 * i + D : ℕ) : ℝ)))⁻¹ ≤ 3 := by
  have h0 : (((2 * 0 + D : ℕ) : ℝ) * √(((2 * 0 + D : ℕ) : ℝ)))⁻¹ ≤ 1 := by
    rcases Nat.eq_zero_or_pos D with hD | hD
    · simp [hD]
    · have ht1 : (1:ℝ) ≤ ((2 * 0 + D : ℕ) : ℝ) := by
        simp only [Nat.mul_zero, Nat.zero_add]
        exact_mod_cast hD
      have hs : (1:ℝ) ≤ √(((2 * 0 + D : ℕ) : ℝ)) := by
        rw [Real.le_sqrt zero_le_one (by positivity)]
        rwa [one_pow]
      have h1 : (1:ℝ) ≤ ((2 * 0 + D : ℕ) : ℝ) * √(((2 * 0 + D : ℕ) : ℝ)) := by
        calc (1:ℝ) = 1 * 1 := (one_mul 1).symm
          _ ≤ ((2 * 0 + D : ℕ) : ℝ) * √(((2 * 0 + D : ℕ) : ℝ)) :=
            mul_le_mul ht1 hs zero_le_one (zero_le_one.trans ht1)
      exact inv_le_one_of_one_le₀ h1
  have hstep : ∀ i : ℕ, 1 ≤ i →
      ((((2 * i + D : ℕ) : ℝ) * √(((2 * i + D : ℕ) : ℝ)))⁻¹
        ≤ 2 * ((√(((2 * i + D : ℕ) : ℝ)))⁻¹ - (√(((2 * (i + 1) + D : ℕ) : ℝ)))⁻¹)) := by
    intro i hi
    have hti : (2:ℝ) ≤ ((2 * i + D : ℕ) : ℝ) := by
      have h1 : (2:ℝ) ≤ ((2 * i : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 2 ≤ 2 * i)
      exact h1.trans (by exact_mod_cast Nat.le_add_right _ _)
    have hsucc : ((2 * (i + 1) + D : ℕ) : ℝ) = ((2 * i + D : ℕ) : ℝ) + 2 := by
      push_cast
      ring
    rw [hsucc]
    exact inv_mul_sqrt_le_two_mul hti
  have hsub : range M ⊆ insert 0 (Ico 1 M) := by
    intro i hi
    rw [mem_range] at hi
    by_cases h : i = 0
    · rw [h]
      exact mem_insert_self 0 _
    · exact mem_insert_of_mem (mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr h, hi⟩)
  have hnn : ∀ i ∈ insert 0 (Ico 1 M), i ∉ range M
      → 0 ≤ (((2 * i + D : ℕ) : ℝ) * √(((2 * i + D : ℕ) : ℝ)))⁻¹ :=
    fun i _ _ => inv_nonneg.mpr
      (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
  calc ∑ i ∈ range M, (((2 * i + D : ℕ) : ℝ) * √(((2 * i + D : ℕ) : ℝ)))⁻¹
      ≤ ∑ i ∈ insert 0 (Ico 1 M), (((2 * i + D : ℕ) : ℝ) * √(((2 * i + D : ℕ) : ℝ)))⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsub hnn
    _ = (((2 * 0 + D : ℕ) : ℝ) * √(((2 * 0 + D : ℕ) : ℝ)))⁻¹
        + ∑ i ∈ Ico 1 M, (((2 * i + D : ℕ) : ℝ) * √(((2 * i + D : ℕ) : ℝ)))⁻¹ :=
        sum_insert (by simp)
    _ ≤ 1 + ∑ i ∈ Ico 1 M, 2 * ((√(((2 * i + D : ℕ) : ℝ)))⁻¹
        - (√(((2 * (i + 1) + D : ℕ) : ℝ)))⁻¹) :=
        add_le_add h0 (sum_le_sum fun i hi => hstep i (mem_Ico.mp hi).1)
    _ = 1 + 2 * ∑ i ∈ Ico 1 M, ((√(((2 * i + D : ℕ) : ℝ)))⁻¹
        - (√(((2 * (i + 1) + D : ℕ) : ℝ)))⁻¹) := by rw [mul_sum]
    _ = 1 + 2 * ∑ j ∈ range (M - 1), ((√(((2 * (1 + j) + D : ℕ) : ℝ)))⁻¹
        - (√(((2 * (1 + j + 1) + D : ℕ) : ℝ)))⁻¹) := by
        rw [sum_Ico_eq_sum_range]
    _ = 1 + 2 * ((√(((2 * (1 + 0) + D : ℕ) : ℝ)))⁻¹
        - (√(((2 * (1 + (M - 1)) + D : ℕ) : ℝ)))⁻¹) := by
        congr 1
        congr 1
        exact Finset.sum_range_sub' (fun j => (√(((2 * (1 + j) + D : ℕ) : ℝ)))⁻¹) (M - 1)
    _ ≤ 1 + 2 * ((√(((2 * (1 + 0) + D : ℕ) : ℝ)))⁻¹ - 0) := by
        have hB : (0:ℝ) ≤ (√(((2 * (1 + (M - 1)) + D : ℕ) : ℝ)))⁻¹ :=
          inv_nonneg.mpr (Real.sqrt_nonneg _)
        linarith [hB]
    _ ≤ 3 := by
        have h1 : (√(((2 * (1 + 0) + D : ℕ) : ℝ)))⁻¹ ≤ 1 := by
          apply inv_le_one_of_one_le₀
          rw [Real.le_sqrt zero_le_one (by positivity), one_pow]
          have hle : (1:ℕ) ≤ 2 * (1 + 0) + D := by omega
          exact_mod_cast hle
        linarith [h1]

/-- Shifting a sum off zero: `∑_{i=1}^{M-1} F i` equals the range sum with the
`i = 0` term set to zero. -/
theorem sum_Ico_one_eq_sum_range (M : ℕ) (F : ℕ → ℝ) :
    ∑ i ∈ Ico 1 M, F i = ∑ i ∈ range M, (if i = 0 then (0:ℝ) else F i) := by
  induction M with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · rw [sum_Ico_succ_top hk, sum_range_succ, ih,
        if_neg (Nat.pos_iff_ne_zero.mp hk)]

/-- The harmonic decrement: `1/i ≤ log i − log (i−1)` for `i ≥ 2`. -/
theorem inv_natCast_le_log_sub {i : ℕ} (hi : 2 ≤ i) :
    ((i : ℝ))⁻¹ ≤ Real.log (i : ℝ) - Real.log ((i - 1 : ℕ) : ℝ) := by
  have hic : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ i), Nat.cast_one]
  have h2 : (2:ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hpos : (0:ℝ) < ((i - 1 : ℕ) : ℝ) / i := by
    rw [hic]
    exact div_pos (by linarith) (Nat.cast_pos.mpr (by omega))
  have h := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_div (Nat.cast_ne_zero.mpr (by omega : i - 1 ≠ 0))
    (Nat.cast_ne_zero.mpr (by omega : i ≠ 0)), hic] at h
  have e : ((i : ℝ) - 1) / i - 1 = -(1 / i) := by field_simp; ring
  rw [e] at h
  rw [hic, inv_eq_one_div]
  linarith

/-- **The harmonic bound**: `∑_{1 ≤ i < M} 1/i ≤ 1 + log M`. -/
theorem sum_range_inv_le_one_add_log (M : ℕ) :
    ∑ i ∈ range M, (if i = 0 then (0:ℝ) else ((i : ℝ))⁻¹) ≤ 1 + Real.log M := by
  rw [← sum_Ico_one_eq_sum_range]
  rcases lt_or_ge M 2 with hM | hM
  · interval_cases M
    · simp
    · simp
  · rw [← sum_Ico_consecutive _ one_le_two hM]
    rw [show Ico 1 2 = {1} from by
      ext x
      simp only [mem_Ico, mem_singleton]
      omega]
    rw [sum_singleton]
    have hterm : ∀ i ∈ Ico 2 M, ((i : ℝ))⁻¹
        ≤ Real.log (i : ℝ) - Real.log ((i : ℝ) - 1) := fun i hi => by
      have h2 : 2 ≤ i := (mem_Ico.mp hi).1
      have h := inv_natCast_le_log_sub h2
      rwa [Nat.cast_sub (by omega : 1 ≤ i), Nat.cast_one] at h
    calc (((1 : ℕ) : ℝ))⁻¹ + ∑ i ∈ Ico 2 M, ((i : ℝ))⁻¹
        ≤ 1 + ∑ i ∈ Ico 2 M, (Real.log (i : ℝ) - Real.log ((i : ℝ) - 1)) := by
          rw [Nat.cast_one, inv_one]
          exact add_le_add (le_refl _) (sum_le_sum hterm)
      _ = 1 + (Real.log ((M - 1 : ℕ) : ℝ) - Real.log (2 - 1)) := by
          congr 1
          rw [sum_Ico_eq_sum_range]
          have hend : ((M - 2 + 1 : ℕ) : ℝ) = ((M - 1 : ℕ) : ℝ) := by
            rw [show M - 2 + 1 = M - 1 by omega]
          have hend0 : ((0 + 1 : ℕ) : ℝ) = (2:ℝ) - 1 := by push_cast; ring
          have htele := Finset.sum_range_sub (fun j => Real.log (((j + 1 : ℕ) : ℝ))) (M - 2)
          rw [← hend, ← hend0, ← htele]
          refine sum_congr rfl fun i _ => ?_
          rw [show (2 + i : ℕ) = i + 1 + 1 by omega]
          rw [show ((i + 1 + 1 : ℕ) : ℝ) - 1 = ((i + 1 : ℕ) : ℝ) by
            rw [Nat.cast_add, Nat.cast_one]
            ring]
      _ ≤ 1 + Real.log M := by
          have hmono : Real.log ((M - 1 : ℕ) : ℝ) ≤ Real.log (M : ℝ) := by
            apply Real.log_le_log
            · exact Nat.cast_pos.mpr (by omega : 0 < M - 1)
            · exact_mod_cast Nat.sub_le M 1
          rw [show (2:ℝ) - 1 = 1 by norm_num, Real.log_one, sub_zero]
          linarith [hmono]

/-- **The `log n / √n` decay**, from `log n ≤ 4 n^{1/4}`. -/
theorem tendsto_nat_log_div_sqrt_atTop :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) / √(n : ℝ)) atTop (𝓝 0) := by
  have hbound : ∀ n : ℕ, 1 ≤ n →
      Real.log (n : ℝ) / √(n : ℝ) ≤ 4 * (n : ℝ) ^ (-(1 : ℝ) / 4) := by
    intro n hn
    have hn0 : (0:ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have h3 : Real.log (n : ℝ) ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
      have h1 : Real.log ((n : ℝ) ^ ((1 : ℝ) / 4)) = (1 / 4) * Real.log (n : ℝ) :=
        Real.log_rpow hn0 _
      have h2 : Real.log ((n : ℝ) ^ ((1 : ℝ) / 4)) ≤ (n : ℝ) ^ ((1 : ℝ) / 4) - 1 :=
        Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hn0 _)
      linarith
    rw [Real.sqrt_eq_rpow, div_le_iff₀ (Real.rpow_pos_of_pos hn0 _)]
    rw [show 4 * (n : ℝ) ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 2)
        = 4 * ((n : ℝ) ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 2)) by ring]
    rw [← Real.rpow_add hn0]
    have he : (-(1 : ℝ) / 4) + (1 : ℝ) / 2 = 1 / 4 := by norm_num
    rw [he]
    exact h3
  have hgeo : Tendsto (fun n : ℕ => 4 * (n : ℝ) ^ (-(1 : ℝ) / 4)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop
    have h2 := h.const_mul 4
    have he : (-(1 : ℝ) / 4) = -(1 / 4 : ℝ) := by norm_num
    rw [he]
    simpa only [Function.comp_def, mul_zero] using h2
  refine squeeze_zero' ?_ ?_ hgeo
  · exact eventually_atTop.mpr ⟨1, fun n hn =>
      div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hn)) (Real.sqrt_nonneg _)⟩
  · exact eventually_atTop.mpr ⟨1, hbound⟩

/-- The Gaussian profile `√(2/π)·(√a)⁻¹·exp(−v²/(2a))` produced by the local CLT. -/
noncomputable def heatApprox (a v : ℝ) : ℝ :=
  Real.sqrt (2 / Real.pi) * (Real.sqrt a)⁻¹ * Real.exp (-(v ^ 2 / (2 * a)))

theorem heatApprox_nonneg (a v : ℝ) : 0 ≤ heatApprox a v := by
  unfold heatApprox
  positivity

theorem heatApprox_le (a v : ℝ) :
    heatApprox a v ≤ Real.sqrt (2 / Real.pi) * (Real.sqrt a)⁻¹ := by
  by_cases ha : a ≤ 0
  · simp [heatApprox, Real.sqrt_eq_zero_of_nonpos ha]
  · replace ha : 0 < a := not_le.mp ha
    have hE : Real.exp (-(v ^ 2 / (2 * a))) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr
        (neg_nonpos.mpr (div_nonneg (sq_nonneg v) (mul_nonneg zero_le_two ha.le)))
    unfold heatApprox
    calc Real.sqrt (2 / Real.pi) * (Real.sqrt a)⁻¹ * Real.exp (-(v ^ 2 / (2 * a)))
        ≤ Real.sqrt (2 / Real.pi) * (Real.sqrt a)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ = Real.sqrt (2 / Real.pi) * (Real.sqrt a)⁻¹ := mul_one _

theorem heatApprox_neg (a v : ℝ) : heatApprox a (-v) = heatApprox a v := by
  unfold heatApprox
  rw [neg_sq]

theorem sqrt_mul_exp_neg_le_one (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt t * Real.exp (-(t / 2)) ≤ 1 := by
  have h1 : Real.sqrt t ≤ 1 + t / 2 := by
    nlinarith [Real.mul_self_sqrt ht, sq_nonneg (Real.sqrt t - 1)]
  have h2 : 1 + t / 2 ≤ Real.exp (t / 2) := by
    have h := Real.add_one_le_exp (t / 2)
    linarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
  exact le_trans h1 h2

theorem one_add_mul_exp_neg_le_two (t : ℝ) :
    (t + 1) * Real.exp (-(t / 2)) ≤ 2 := by
  have h2 : t + 1 ≤ 2 * Real.exp (t / 2) := by
    have h := Real.add_one_le_exp (t / 2)
    linarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  exact h2

theorem hasDerivAt_heatApprox_snd (a v : ℝ) :
    HasDerivAt (fun w => heatApprox a w)
      (Real.sqrt (2 / Real.pi) * (Real.sqrt a)⁻¹ *
        (Real.exp (-(v ^ 2 / (2 * a))) * (-(v / a)))) v := by
  by_cases ha : a = 0
  · subst ha
    have hf : (fun w : ℝ => heatApprox 0 w) = fun _ => 0 := by
      funext w
      simp [heatApprox]
    rw [Real.sqrt_zero, inv_zero, mul_zero, zero_mul, hf]
    exact hasDerivAt_const v 0
  · have hinner : HasDerivAt (fun w => -(w ^ 2 / (2 * a))) (-(v / a)) v := by
      have h1 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * v) v := by
        simpa using hasDerivAt_pow 2 v
      have h2 := h1.div_const (2 * a)
      have h3 := h2.neg
      rwa [mul_div_mul_left v a two_ne_zero] at h3
    have h4 := hinner.exp
    have h5 := h4.const_mul (Real.sqrt (2 / Real.pi) * (Real.sqrt a)⁻¹)
    exact h5

theorem hasDerivAt_heatApprox_fst (a : ℝ) (ha : 0 < a) (v : ℝ) :
    HasDerivAt (fun b => heatApprox b v)
      (Real.sqrt (2 / Real.pi) * Real.exp (-(v ^ 2 / (2 * a))) * (v ^ 2 - a) /
        (2 * a ^ 2 * Real.sqrt a)) a := by
  have ha' : a ≠ 0 := ha.ne'
  have hsa : Real.sqrt a ≠ 0 := Real.sqrt_ne_zero'.mpr ha
  have hden : HasDerivAt (fun b : ℝ => 2 * b) (2 * 1) a := by
    simpa using (hasDerivAt_id' (x := a)).const_mul 2
  have hinner : HasDerivAt (fun b : ℝ => -(v ^ 2 / (2 * b)))
      (-((0 * (2 * a) - v ^ 2 * (2 * 1)) / (2 * a) ^ 2)) a :=
    ((hasDerivAt_const a (v ^ 2)).div hden (mul_ne_zero two_ne_zero ha')).neg
  have hinnerexp := hinner.exp
  have hsqrt : HasDerivAt (fun b : ℝ => (Real.sqrt b)⁻¹)
      (-(1 / (2 * Real.sqrt a)) / (Real.sqrt a) ^ 2) a :=
    (Real.hasDerivAt_sqrt ha').inv hsa
  have hcs := hsqrt.const_mul (Real.sqrt (2 / Real.pi))
  have hfull := hcs.mul hinnerexp
  have hder : Real.sqrt (2 / Real.pi) * Real.exp (-(v ^ 2 / (2 * a))) * (v ^ 2 - a) /
        (2 * a ^ 2 * Real.sqrt a) =
      Real.sqrt (2 / Real.pi) * (-(1 / (2 * Real.sqrt a)) / (Real.sqrt a) ^ 2) *
          Real.exp (-(v ^ 2 / (2 * a))) +
        Real.sqrt (2 / Real.pi) * (Real.sqrt a)⁻¹ *
          (Real.exp (-(v ^ 2 / (2 * a))) *
            -((0 * (2 * a) - v ^ 2 * (2 * 1)) / (2 * a) ^ 2)) := by
    rw [Real.sq_sqrt ha.le]
    field_simp [ha', hsa]
    ring
  rw [hder]
  exact hfull

theorem abs_deriv_heatApprox_snd_le (a : ℝ) (ha : 0 < a) (v : ℝ) :
    |Real.sqrt (2 / Real.pi) * (Real.sqrt a)⁻¹ *
        (Real.exp (-(v ^ 2 / (2 * a))) * (-(v / a)))| ≤ Real.sqrt (2 / Real.pi) / a := by
  have ha' : a ≠ 0 := ha.ne'
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsa' : Real.sqrt a ≠ 0 := hsa.ne'
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (2 / Real.pi)),
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg a)),
    abs_of_nonneg (Real.exp_pos _).le, abs_neg, abs_div, abs_of_pos ha]
  have hvt : Real.sqrt a * Real.sqrt (v ^ 2 / a) = |v| := by
    rw [← Real.sqrt_mul ha.le (v ^ 2 / a), ← mul_div_assoc, mul_div_cancel_left₀ _ ha',
      Real.sqrt_sq_eq_abs]
  have key : Real.sqrt (2 / Real.pi) * (Real.sqrt a)⁻¹ *
        (Real.exp (-(v ^ 2 / (2 * a))) * (|v| / a)) =
      (Real.sqrt (2 / Real.pi) / a) *
        (Real.exp (-(v ^ 2 / (2 * a))) * Real.sqrt (v ^ 2 / a)) := by
    rw [← hvt]
    field_simp [ha', hsa']
  rw [key]
  have hstep := sqrt_mul_exp_neg_le_one (v ^ 2 / a) (div_nonneg (sq_nonneg v) ha.le)
  have heq : -(v ^ 2 / (2 * a)) = -((v ^ 2 / a) / 2) := by
    rw [mul_comm 2 a, div_mul_eq_div_div]
  rw [heq, mul_comm (Real.exp (-((v ^ 2 / a) / 2))) (Real.sqrt (v ^ 2 / a))]
  calc Real.sqrt (2 / Real.pi) / a * (Real.sqrt (v ^ 2 / a) * Real.exp (-((v ^ 2 / a) / 2)))
      ≤ Real.sqrt (2 / Real.pi) / a * 1 :=
        mul_le_mul_of_nonneg_left hstep (div_nonneg (Real.sqrt_nonneg _) ha.le)
    _ = Real.sqrt (2 / Real.pi) / a := mul_one _

theorem abs_deriv_heatApprox_fst_le (a : ℝ) (ha : 0 < a) (v : ℝ) :
    |Real.sqrt (2 / Real.pi) * Real.exp (-(v ^ 2 / (2 * a))) * (v ^ 2 - a) /
        (2 * a ^ 2 * Real.sqrt a)| ≤ Real.sqrt (2 / Real.pi) / (a * Real.sqrt a) := by
  have ha' : a ≠ 0 := ha.ne'
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsa' : Real.sqrt a ≠ 0 := hsa.ne'
  have hden : 0 < 2 * a ^ 2 * Real.sqrt a := by positivity
  rw [abs_div, abs_of_pos hden, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (Real.exp_pos _).le]
  have hsub : |v ^ 2 - a| ≤ v ^ 2 + a := by
    calc |v ^ 2 - a| ≤ |v ^ 2| + |a| := abs_sub _ _
      _ = v ^ 2 + a := by rw [abs_of_nonneg (sq_nonneg v), abs_of_nonneg ha.le]
  have hstep : Real.exp (-(v ^ 2 / (2 * a))) * (v ^ 2 + a) ≤ 2 * a := by
    have ht : 0 ≤ v ^ 2 / a := div_nonneg (sq_nonneg v) ha.le
    have h1 := one_add_mul_exp_neg_le_two (v ^ 2 / a)
    have heq : -(v ^ 2 / (2 * a)) = -((v ^ 2 / a) / 2) := by
      rw [mul_comm 2 a, div_mul_eq_div_div]
    rw [heq]
    have hv2 : v ^ 2 + a = a * (v ^ 2 / a + 1) := by
      rw [mul_add, mul_div_assoc', mul_div_cancel_left₀ _ ha', mul_one]
    rw [hv2]
    calc Real.exp (-((v ^ 2 / a) / 2)) * (a * (v ^ 2 / a + 1))
        = a * ((v ^ 2 / a + 1) * Real.exp (-((v ^ 2 / a) / 2))) := by ring
      _ ≤ a * 2 := mul_le_mul_of_nonneg_left h1 ha.le
      _ = 2 * a := by ring
  rw [div_le_iff₀ hden]
  have hrhs : Real.sqrt (2 / Real.pi) / (a * Real.sqrt a) * (2 * a ^ 2 * Real.sqrt a) =
      Real.sqrt (2 / Real.pi) * (2 * a) := by
    rw [show 2 * a ^ 2 * Real.sqrt a = (a * Real.sqrt a) * (2 * a) by ring, ← mul_assoc,
      div_mul_cancel₀ _ (mul_ne_zero ha' hsa')]
  rw [hrhs]
  calc Real.sqrt (2 / Real.pi) * Real.exp (-(v ^ 2 / (2 * a))) * |v ^ 2 - a|
      ≤ Real.sqrt (2 / Real.pi) * Real.exp (-(v ^ 2 / (2 * a))) * (v ^ 2 + a) :=
        mul_le_mul_of_nonneg_left hsub (by positivity)
    _ = Real.sqrt (2 / Real.pi) * (Real.exp (-(v ^ 2 / (2 * a))) * (v ^ 2 + a)) := by ring
    _ ≤ Real.sqrt (2 / Real.pi) * (2 * a) :=
        mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg _)

theorem abs_heatApprox_sub_snd (a : ℝ) (ha : 0 < a) (u v : ℝ) :
    |heatApprox a u - heatApprox a v| ≤ (Real.sqrt (2 / Real.pi) / a) * |u - v| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun w => heatApprox a w)
    (f' := fun w => Real.sqrt (2 / Real.pi) * (Real.sqrt a)⁻¹ *
      (Real.exp (-(w ^ 2 / (2 * a))) * (-(w / a))))
    (s := Set.univ) (C := Real.sqrt (2 / Real.pi) / a)
    (fun x _ => (hasDerivAt_heatApprox_snd a x).hasDerivWithinAt)
    (fun x _ => by
      rw [Real.norm_eq_abs]
      exact abs_deriv_heatApprox_snd_le a ha x)
    convex_univ (Set.mem_univ u) (Set.mem_univ v)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  rw [abs_sub_comm (heatApprox a u) (heatApprox a v), abs_sub_comm u v]
  exact h

theorem abs_heatApprox_sub_fst {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (v : ℝ) :
    |heatApprox a v - heatApprox b v| ≤
      (Real.sqrt (2 / Real.pi) / (min a b * Real.sqrt (min a b))) * |a - b| := by
  have hmin : 0 < min a b := lt_min (by linarith) (by linarith)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun c => heatApprox c v)
    (f' := fun c => Real.sqrt (2 / Real.pi) * Real.exp (-(v ^ 2 / (2 * c))) * (v ^ 2 - c) /
      (2 * c ^ 2 * Real.sqrt c))
    (s := Set.Icc (min a b) (max a b))
    (C := Real.sqrt (2 / Real.pi) / (min a b * Real.sqrt (min a b)))
    (fun y hy =>
      (hasDerivAt_heatApprox_fst y
        (lt_of_lt_of_le hmin (Set.mem_Icc.mp hy).1) v).hasDerivWithinAt)
    (fun y hy => by
      have hy1 : min a b ≤ y := (Set.mem_Icc.mp hy).1
      have hy0 : 0 < y := lt_of_lt_of_le hmin hy1
      rw [Real.norm_eq_abs]
      exact (abs_deriv_heatApprox_fst_le y hy0 v).trans
        (div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
          (mul_pos hmin (Real.sqrt_pos.mpr hmin))
          (mul_le_mul hy1 (Real.sqrt_le_sqrt hy1) (Real.sqrt_nonneg _)
            (hmin.le.trans hy1))))
    (convex_Icc (min a b) (max a b))
    (Set.mem_Icc.mpr ⟨min_le_left a b, le_max_left a b⟩)
    (Set.mem_Icc.mpr ⟨min_le_right a b, le_max_right a b⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  rw [abs_sub_comm (heatApprox a v) (heatApprox b v), abs_sub_comm a b]
  exact h

theorem abs_heatApprox_sub {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (u v : ℝ) :
    |heatApprox a u - heatApprox b v| ≤
      (Real.sqrt (2 / Real.pi) / a) * |u - v| +
        (Real.sqrt (2 / Real.pi) / (min a b * Real.sqrt (min a b))) * |a - b| := by
  calc |heatApprox a u - heatApprox b v|
      = |(heatApprox a u - heatApprox a v) + (heatApprox a v - heatApprox b v)| := by
        rw [sub_add_sub_cancel]
    _ ≤ |heatApprox a u - heatApprox a v| + |heatApprox a v - heatApprox b v| :=
        abs_add_le _ _
    _ ≤ (Real.sqrt (2 / Real.pi) / a) * |u - v| +
          (Real.sqrt (2 / Real.pi) / (min a b * Real.sqrt (min a b))) * |a - b| :=
        add_le_add (abs_heatApprox_sub_snd a (by linarith) u v)
          (abs_heatApprox_sub_fst ha hb v)

theorem abs_binomLaw_sub_heatApprox_le {C : ℝ} (hCbound : ∀ m : ℕ, 1 ≤ m → ∀ j : ℤ,
    (j - (m : ℤ)) % 2 = 0 →
    |Real.sqrt (m : ℝ) * binomLaw m ((j + (m : ℤ)) / 2) -
      2 * (Real.exp (-((j : ℝ) / Real.sqrt (m : ℝ)) ^ 2 / 2) /
        Real.sqrt (2 * Real.pi))| ≤ C / (m : ℝ))
    (D : ℕ) (K : ℤ) (i : ℕ) (him : 1 ≤ 2 * i + D) :
    |binomLaw (2 * i + D) ((i : ℤ) + K) -
        heatApprox ((2 * i + D : ℕ) : ℝ) (2 * K - (D : ℤ))| ≤
      C / (((2 * i + D : ℕ) : ℝ) * Real.sqrt ((2 * i + D : ℕ) : ℝ)) := by
  have hpar : (2 * K - (D : ℤ) - ((2 * i + D : ℕ) : ℤ)) % 2 = 0 := by
    push_cast
    omega
  have hdiv : (2 * K - (D : ℤ) + ((2 * i + D : ℕ) : ℤ)) / 2 = (i : ℤ) + K := by
    push_cast
    omega
  have hstep := hCbound (2 * i + D) him (2 * K - (D : ℤ)) hpar
  rw [hdiv] at hstep
  have hcast : (((2 * K - (D : ℤ)) : ℤ) : ℝ) = 2 * (K : ℝ) - ((D : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hcast] at hstep
  have hmpos : (0 : ℝ) < ((2 * i + D : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le one_pos him)
  have hm0 : 0 < Real.sqrt ((2 * i + D : ℕ) : ℝ) := Real.sqrt_pos.mpr hmpos
  have hexp : -(((2 * K - (D : ℤ)) : ℝ) / Real.sqrt ((2 * i + D : ℕ) : ℝ)) ^ 2 / 2 =
      -(((2 * K - (D : ℤ)) : ℝ) ^ 2 / (2 * ((2 * i + D : ℕ) : ℝ))) := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _), neg_div, div_div, mul_comm _ (2 : ℝ)]
  have hconst : (2 : ℝ) / Real.sqrt (2 * Real.pi) = Real.sqrt (2 / Real.pi) := by
    rw [Real.sqrt_div zero_le_two _, Real.sqrt_mul zero_le_two _, div_mul_eq_div_div,
      show (2 : ℝ) / Real.sqrt 2 = Real.sqrt 2 by
        rw [div_eq_iff (Real.sqrt_ne_zero'.mpr two_pos), Real.mul_self_sqrt zero_le_two]]
  have halg : 2 * (Real.exp (-(((2 * K - (D : ℤ)) : ℝ) /
        Real.sqrt ((2 * i + D : ℕ) : ℝ)) ^ 2 / 2) / Real.sqrt (2 * Real.pi)) /
      Real.sqrt ((2 * i + D : ℕ) : ℝ) =
      heatApprox ((2 * i + D : ℕ) : ℝ) (2 * K - (D : ℤ)) := by
    unfold heatApprox
    rw [hexp,
      show (2 : ℝ) * (Real.exp (-(((2 * K - (D : ℤ)) : ℝ) ^ 2 /
            (2 * ((2 * i + D : ℕ) : ℝ)))) / Real.sqrt (2 * Real.pi)) =
        (2 / Real.sqrt (2 * Real.pi)) *
          Real.exp (-(((2 * K - (D : ℤ)) : ℝ) ^ 2 / (2 * ((2 * i + D : ℕ) : ℝ)))) by ring,
      hconst, div_eq_mul_inv]
    ring
  rw [← halg]
  rw [show binomLaw (2 * i + D) ((i : ℤ) + K) -
        2 * (Real.exp (-(((2 * K - (D : ℤ)) : ℝ) /
            Real.sqrt ((2 * i + D : ℕ) : ℝ)) ^ 2 / 2) / Real.sqrt (2 * Real.pi)) /
          Real.sqrt ((2 * i + D : ℕ) : ℝ) =
      (Real.sqrt ((2 * i + D : ℕ) : ℝ) * binomLaw (2 * i + D) ((i : ℤ) + K) -
        2 * (Real.exp (-(((2 * K - (D : ℤ)) : ℝ) /
            Real.sqrt ((2 * i + D : ℕ) : ℝ)) ^ 2 / 2) / Real.sqrt (2 * Real.pi))) /
        Real.sqrt ((2 * i + D : ℕ) : ℝ) from by
      conv_rhs => rw [sub_div, mul_div_cancel_left₀ _ hm0.ne']]
  rw [abs_div, abs_of_pos hm0,
    show C / (((2 * i + D : ℕ) : ℝ) * Real.sqrt ((2 * i + D : ℕ) : ℝ)) =
      (C / ((2 * i + D : ℕ) : ℝ)) / Real.sqrt ((2 * i + D : ℕ) : ℝ) from (div_div _ _ _).symm]
  rw [div_le_div_iff₀ hm0 hm0]
  exact mul_le_mul_of_nonneg_right hstep (Real.sqrt_nonneg _)

/-- The `n⁻¹`-weighted heat kernel at `i / n` equals the `n^{-1/2}`-weighted Gaussian
profile at `2i + nδ`: the Riemann-sum summand is the local-CLT approximation. -/
theorem riemann_term (n : ℕ) (hn : 1 ≤ n) (δ d : ℝ) (hδ : 0 ≤ δ) (i : ℕ) :
    ((n : ℝ))⁻¹ * contHeat (2 * (i : ℝ) / n + δ) 0 d =
      (Real.sqrt n)⁻¹ * heatApprox (2 * (i : ℝ) + (n : ℝ) * δ) (2 * Real.sqrt n * d) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hnnonneg : 0 ≤ 2 * (i : ℝ) + (n : ℝ) * δ :=
    add_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) (mul_nonneg hn0.le hδ)
  by_cases ht : 2 * (i : ℝ) + (n : ℝ) * δ = 0
  · have ht0 : 2 * (i : ℝ) / n + δ = 0 := by
      rw [show 2 * (i : ℝ) / n + δ = (2 * (i : ℝ) + (n : ℝ) * δ) / n from by
        field_simp [hnn], ht, zero_div]
    rw [contHeat_of_nonpos ht0.le 0 d, mul_zero, ht]
    simp [heatApprox]
  · replace ht : 0 < 2 * (i : ℝ) + (n : ℝ) * δ := lt_of_le_of_ne hnnonneg (Ne.symm ht)
    have ht' : 0 < 2 * (i : ℝ) / n + δ := by
      rw [show 2 * (i : ℝ) / n + δ = (2 * (i : ℝ) + (n : ℝ) * δ) / n from by
        field_simp [hnn]]
      exact div_pos ht hn0
    have hnnsq : ((n : ℝ))⁻¹ = (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ := by
      conv_lhs => rw [← Real.mul_self_sqrt hn0.le]
      rw [mul_inv]
    have hsqrtE : Real.sqrt (2 * (i : ℝ) / n + δ) =
        Real.sqrt (2 * (i : ℝ) + (n : ℝ) * δ) / Real.sqrt n := by
      rw [show 2 * (i : ℝ) / n + δ = (2 * (i : ℝ) + (n : ℝ) * δ) / n from by
        field_simp [hnn], Real.sqrt_div ht.le n]
    have hexpE : -2 * d ^ 2 / (2 * (i : ℝ) / n + δ) =
        -((2 * Real.sqrt n * d) ^ 2 / (2 * (2 * (i : ℝ) + (n : ℝ) * δ))) := by
      rw [show 2 * (i : ℝ) / n + δ = (2 * (i : ℝ) + (n : ℝ) * δ) / n from by
        field_simp [hnn], mul_pow, mul_pow, Real.sq_sqrt hn0.le]
      field_simp [hnn, ht.ne']
    rw [contHeat_zero_eq ht' d]
    unfold heatApprox
    rw [hsqrtE, hexpE, hnnsq]
    field_simp [hsn.ne', Real.sqrt_ne_zero'.mpr ht, ht.ne', hnn]

/-- The heat-kernel integrand `θ ↦ contHeat (2θ + δ) 0 d` is continuous on `Icc 0 a`
away from the joint degeneracy `δ = 0`, `d = 0`. -/
theorem continuousOn_contHeat_two_mul_add_zero {δ d : ℝ} (hδ : 0 ≤ δ) (h : 0 < δ ∨ d ≠ 0)
    (a : ℝ) : ContinuousOn (fun θ => contHeat (2 * θ + δ) 0 d) (Set.Icc 0 a) := by
  set F : ℝ → ℝ := fun θ => Real.sqrt (2 / Real.pi) * (Real.sqrt (2 * θ + δ))⁻¹ *
    Real.exp (-2 * d ^ 2 / (2 * θ + δ)) with hF
  have hEq : Set.EqOn (fun θ => contHeat (2 * θ + δ) 0 d) F (Set.Icc 0 a) := by
    intro θ hθ
    show contHeat (2 * θ + δ) 0 d = F θ
    have hθ0 : 0 ≤ θ := (Set.mem_Icc.mp hθ).1
    by_cases ht : 2 * θ + δ = 0
    · rw [contHeat_of_nonpos (le_of_eq ht) 0 d]
      simp [hF, ht]
    · replace ht : 0 < 2 * θ + δ :=
        lt_of_le_of_ne (add_nonneg (mul_nonneg zero_le_two hθ0) hδ) (Ne.symm ht)
      rw [contHeat_zero_eq ht d]
  rcases lt_or_eq_of_le hδ with hδpos | hδ0
  · have hpos : ∀ θ ∈ Set.Icc 0 a, 0 < 2 * θ + δ := fun θ hθ => by
      have h1 := (Set.mem_Icc.mp hθ).1
      linarith
    have h1 : ContinuousOn (fun θ : ℝ => 2 * θ + δ) (Set.Icc 0 a) := by fun_prop
    have h2 : ContinuousOn (fun θ : ℝ => Real.sqrt (2 * θ + δ)) (Set.Icc 0 a) :=
      Real.continuous_sqrt.comp_continuousOn h1
    have h3 : ContinuousOn (fun θ : ℝ => (Real.sqrt (2 * θ + δ))⁻¹) (Set.Icc 0 a) :=
      h2.inv₀ (fun θ hθ => (Real.sqrt_pos.mpr (hpos θ hθ)).ne')
    have h4 : ContinuousOn (fun θ : ℝ => -2 * d ^ 2 / (2 * θ + δ)) (Set.Icc 0 a) :=
      continuousOn_const.div h1 (fun θ hθ => (hpos θ hθ).ne')
    have h5 : ContinuousOn (fun θ : ℝ => Real.exp (-2 * d ^ 2 / (2 * θ + δ)))
        (Set.Icc 0 a) := Real.continuous_exp.comp_continuousOn h4
    exact ((continuousOn_const.mul h3).mul h5).congr hEq
  · subst hδ0
    have hd : d ≠ 0 := h.resolve_left (lt_irrefl (0 : ℝ))
    have hcont : ContinuousOn F (Set.Icc 0 a) := by
      intro θ hθ
      rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).1 with hθ0 | hθpos
      · subst hθ0
        have hF0 : F 0 = 0 := by simp [hF]
        show Tendsto F (𝓝[Set.Icc 0 a] 0) (𝓝 (F 0))
        rw [hF0]
        apply tendsto_zero_iff_norm_tendsto_zero.mpr
        have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd
        have hbound : ∀ θ : ℝ, ‖F θ‖ ≤
            (Real.sqrt (2 / Real.pi) / (Real.sqrt 2 * d ^ 2)) * Real.sqrt θ := by
          intro θ
          by_cases hθ0 : θ ≤ 0
          · have hθ : θ ≤ 0 := hθ0
            have hz : F θ = 0 := by
              have hle : 2 * θ + (0 : ℝ) ≤ 0 := by linarith
              have hz0 : Real.sqrt (2 * θ + (0 : ℝ)) = 0 := Real.sqrt_eq_zero_of_nonpos hle
              simp only [hF, hz0, inv_zero, mul_zero, zero_mul]
            rw [Real.norm_eq_abs, hz, abs_zero, Real.sqrt_eq_zero_of_nonpos hθ, mul_zero]
          · rw [Real.norm_eq_abs]
            have hθp : 0 < θ := not_le.mp hθ0
            have hFnn : 0 ≤ F θ := by simp only [hF]; positivity
            rw [abs_of_nonneg hFnn]
            have hy : 0 < d ^ 2 / θ :=
              div_pos (lt_of_le_of_ne (sq_nonneg d) (Ne.symm hd2)) hθp
            have h1 : d ^ 2 / θ ≤ Real.exp (d ^ 2 / θ) := by
              have h := Real.add_one_le_exp (d ^ 2 / θ)
              linarith
            have h2 : Real.exp (-(d ^ 2 / θ)) ≤ (d ^ 2 / θ)⁻¹ := by
              rw [Real.exp_neg]
              exact inv_anti₀ hy h1
            have hexp : -2 * d ^ 2 / (2 * θ + (0 : ℝ)) = -(d ^ 2 / θ) := by
              rw [add_zero, show (-2 : ℝ) * d ^ 2 = 2 * (-(d ^ 2)) by ring,
                mul_div_mul_left _ _ two_ne_zero, neg_div]
            have halg : Real.sqrt (2 / Real.pi) * (Real.sqrt (2 * θ + (0 : ℝ)))⁻¹ *
                (d ^ 2 / θ)⁻¹ =
                Real.sqrt (2 / Real.pi) / (Real.sqrt 2 * d ^ 2) * Real.sqrt θ := by
              rw [add_zero, Real.sqrt_mul zero_le_two θ, mul_inv, inv_div,
                div_eq_mul_inv θ (d ^ 2),
                show θ * (d ^ 2)⁻¹ = (Real.sqrt θ * Real.sqrt θ) * (d ^ 2)⁻¹ from by
                  rw [Real.mul_self_sqrt hθp.le]]
              field_simp [hd2, (Real.sqrt_pos.mpr hθp).ne', (Real.sqrt_pos.mpr two_pos).ne']
            simp only [hF]
            rw [hexp]
            calc Real.sqrt (2 / Real.pi) * (Real.sqrt (2 * θ + 0))⁻¹ * Real.exp (-(d ^ 2 / θ))
                ≤ Real.sqrt (2 / Real.pi) * (Real.sqrt (2 * θ + 0))⁻¹ * (d ^ 2 / θ)⁻¹ :=
                  mul_le_mul_of_nonneg_left h2
                    (mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _)))
              _ = Real.sqrt (2 / Real.pi) / (Real.sqrt 2 * d ^ 2) * Real.sqrt θ := halg
        have hsqrt0 : Tendsto (fun t => Real.sqrt t) (𝓝[Set.Icc 0 a] 0) (𝓝 0) := by
          have h : Tendsto (fun x => Real.sqrt x) (𝓝[Set.Icc 0 a] 0) (𝓝 (Real.sqrt 0)) :=
            Real.continuous_sqrt.continuousWithinAt (x := 0) (s := Set.Icc 0 a)
          rwa [Real.sqrt_zero] at h
        exact squeeze_zero' (Filter.Eventually.of_forall fun θ => norm_nonneg _)
          (Filter.Eventually.of_forall hbound)
          (by simpa only [mul_zero] using hsqrt0.const_mul _)
      · have hpos2 : (0 : ℝ) < 2 * θ + 0 := by linarith
        have hbase : ContinuousAt (fun x : ℝ => 2 * x + (0 : ℝ)) θ := by fun_prop
        have h1 : ContinuousAt (fun x : ℝ => Real.sqrt (2 * x + 0)) θ :=
          Real.continuous_sqrt.continuousAt.comp hbase
        have h2 : ContinuousAt (fun x : ℝ => (Real.sqrt (2 * x + 0))⁻¹) θ :=
          h1.inv₀ (Real.sqrt_ne_zero'.mpr hpos2)
        have h3 : ContinuousAt (fun x : ℝ => Real.exp (-2 * d ^ 2 / (2 * x + 0))) θ :=
          Real.continuous_exp.continuousAt.comp (continuousAt_const.div hbase hpos2.ne')
        have h4 : ContinuousAt (fun x : ℝ => Real.sqrt (2 / Real.pi) *
            (Real.sqrt (2 * x + 0))⁻¹ * Real.exp (-2 * d ^ 2 / (2 * x + 0))) θ :=
          (continuousAt_const.mul h2).mul h3
        exact h4.continuousWithinAt
    exact hcont.congr hEq

/-- **The interval-integral primitive from `0` is Lipschitz on `[0,b]`**, with the uniform
bound of the integrand as its constant. -/
theorem abs_integral_zero_sub_le_of_continuousOn {g : ℝ → ℝ} {b : ℝ}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) b)) {Cb : ℝ} (_hCb0 : 0 ≤ Cb)
    (hCbnd : ∀ x ∈ Set.Icc (0 : ℝ) b, |g x| ≤ Cb) (hb0 : (0 : ℝ) ≤ b)
    {c c' : ℝ} (hc : c ∈ Set.Icc (0 : ℝ) b) (hc' : c' ∈ Set.Icc (0 : ℝ) b) :
    |(∫ θ in (0 : ℝ)..c, g θ) - ∫ θ in (0 : ℝ)..c', g θ| ≤ Cb * |c - c'| := by
  have h0b : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b := ⟨le_refl 0, hb0⟩
  have hI1 : IntervalIntegrable g volume 0 c' :=
    (hg.mono (Set.uIcc_subset_Icc h0b hc')).intervalIntegrable
  have hI2 : IntervalIntegrable g volume c' c :=
    (hg.mono (Set.uIcc_subset_Icc hc' hc)).intervalIntegrable
  have hsplit : (∫ θ in (0 : ℝ)..c', g θ) + ∫ θ in c'..c, g θ = ∫ θ in (0 : ℝ)..c, g θ :=
    intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have hbound : ∀ x ∈ Set.uIoc c' c, |g x| ≤ Cb := fun x hx =>
    hCbnd x (Set.uIcc_subset_Icc hc' hc (Set.uIoc_subset_uIcc hx))
  have hnb : |∫ θ in c'..c, g θ| ≤ Cb * |c - c'| := by
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const (f := g) hbound
    rwa [Real.norm_eq_abs] at hn
  have heq : (∫ θ in (0 : ℝ)..c, g θ) - (∫ θ in (0 : ℝ)..c', g θ) = ∫ θ in c'..c, g θ := by
    linarith [hsplit]
  rw [heq]
  exact hnb

/-- **The discrete left-endpoint Riemann sum of mesh `1/n` on `[0, M/n]` is within
`(M/n)·ε'` of the integral**, once `1/n` is below the uniform-continuity scale `δ` of
the modulus at accuracy `ε'` and `M/n` stays in `[0,b]`. -/
theorem abs_riemann_partial_sub_integral_le {g : ℝ → ℝ} {b : ℝ} (_hb0 : (0 : ℝ) ≤ b)
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) b)) {ε' δ : ℝ} (_hε' : 0 ≤ ε')
    (hmod : ∀ x ∈ Set.Icc (0 : ℝ) b, ∀ y ∈ Set.Icc (0 : ℝ) b, |x - y| < δ → |g x - g y| ≤ ε')
    (n M : ℕ) (hn : 1 ≤ n) (hnδ : (n : ℝ)⁻¹ < δ) (hMb : (M : ℝ) / n ≤ b) :
    |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range M, g ((i : ℝ) / n) -
        ∫ θ in (0 : ℝ)..((M : ℝ) / n), g θ| ≤ (M : ℝ) / n * ε' := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hmem : ∀ i : ℕ, i ≤ M → (i : ℝ) / n ∈ Set.Icc (0 : ℝ) b := by
    intro i hi
    exact ⟨by positivity,
      ((div_le_div_iff_of_pos_right hn0).mpr (by exact_mod_cast hi)).trans hMb⟩
  have hlen : ∀ i : ℕ, (((i + 1 : ℕ) : ℝ) / n) - ((i : ℝ) / n) = (n : ℝ)⁻¹ := by
    intro i; push_cast; field_simp; ring
  have hle : ∀ i : ℕ, (i : ℝ) / n ≤ (((i + 1 : ℕ) : ℝ) / n) := by
    intro i
    have h := hlen i
    have h2 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    linarith
  have hint : ∀ k ∈ Set.Ico 0 M, IntervalIntegrable g volume
      ((k : ℝ) / n) (((k + 1 : ℕ) : ℝ) / n) := by
    intro k hk
    obtain ⟨-, hkM⟩ := Set.mem_Ico.mp hk
    exact (hg.mono (Set.uIcc_subset_Icc (hmem k (by omega))
      (hmem (k + 1) (by omega)))).intervalIntegrable
  have hsum : ∑ k ∈ Finset.Ico 0 M, ∫ θ in ((k : ℝ) / n)..(((k + 1 : ℕ) : ℝ) / n), g θ
      = ∫ θ in (0 : ℝ)..((M : ℝ) / n), g θ := by
    have h := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun j : ℕ => (j : ℝ) / n) (Nat.zero_le M) hint
    simpa using h
  have hstep1 : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range M, g ((i : ℝ) / n)
      = ∑ i ∈ Finset.Ico 0 M, ∫ θ in ((i : ℝ) / n)..(((i + 1 : ℕ) : ℝ) / n), g ((i : ℝ) / n) := by
    rw [Finset.range_eq_Ico, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const, hlen i, smul_eq_mul]
  have hdiff : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range M, g ((i : ℝ) / n)
      - ∫ θ in (0 : ℝ)..((M : ℝ) / n), g θ
      = ∑ i ∈ Finset.Ico 0 M, ∫ θ in ((i : ℝ) / n)..(((i + 1 : ℕ) : ℝ) / n),
          (g ((i : ℝ) / n) - g θ) := by
    rw [hstep1, ← hsum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (hint i (Set.mem_Ico.mpr (Finset.mem_Ico.mp hi)))]
  rw [hdiff]
  have hbnd : ∀ i ∈ Finset.Ico 0 M, |∫ θ in ((i : ℝ) / n)..(((i + 1 : ℕ) : ℝ) / n),
      (g ((i : ℝ) / n) - g θ)| ≤ (n : ℝ)⁻¹ * ε' := by
    intro i hi
    have hi1 : i + 1 ≤ M := (Finset.mem_Ico.mp hi).2
    have hmemi : (i : ℝ) / n ∈ Set.Icc (0 : ℝ) b := hmem i (by omega)
    have hmemi1 : (((i + 1 : ℕ) : ℝ) / n) ∈ Set.Icc (0 : ℝ) b := hmem (i + 1) hi1
    have hpt : ∀ θ ∈ Set.uIoc ((i : ℝ) / n) (((i + 1 : ℕ) : ℝ) / n),
        |g ((i : ℝ) / n) - g θ| ≤ ε' := by
      rw [Set.uIoc_of_le (hle i)]
      intro θ hθ
      obtain ⟨hθ1, hθ2⟩ := hθ
      have hθmem : θ ∈ Set.Icc (0 : ℝ) b := ⟨le_trans hmemi.1 hθ1.le, le_trans hθ2 hmemi1.2⟩
      have hb1 : θ - (i : ℝ) / n ≤ (n : ℝ)⁻¹ := by have h := hlen i; linarith
      have hθd : |((i : ℝ) / n) - θ| < δ := by
        rw [abs_of_nonpos (by linarith : (i : ℝ) / n - θ ≤ 0)]
        linarith [hnδ]
      exact hmod _ hmemi _ hθmem hθd
    have hnb := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun θ => g ((i : ℝ) / n) - g θ) hpt
    rw [Real.norm_eq_abs, hlen i, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹),
      mul_comm] at hnb
    exact hnb
  calc |∑ i ∈ Finset.Ico 0 M, ∫ θ in ((i : ℝ) / n)..(((i + 1 : ℕ) : ℝ) / n),
        (g ((i : ℝ) / n) - g θ)|
      ≤ ∑ i ∈ Finset.Ico 0 M, |∫ θ in ((i : ℝ) / n)..(((i + 1 : ℕ) : ℝ) / n),
          (g ((i : ℝ) / n) - g θ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.Ico 0 M, (n : ℝ)⁻¹ * ε' := Finset.sum_le_sum hbnd
    _ = (M : ℝ) / n * ε' := by
        rw [Finset.sum_const, Nat.card_Ico, Nat.sub_zero, nsmul_eq_mul]
        field_simp

/-- **Riemann sums of a continuous integrand converge to the integral along a drifting
endpoint.**  If `g` is continuous on `[0,b]` and `M n / n → a` for some `a < b`, the
discrete left-endpoint Riemann sum of mesh `1/n` on `[0, M n / n]` converges to `∫₀^a g`. -/
theorem tendsto_riemann_sum_Ioo_of_continuousOn {g : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) b)) {M : ℕ → ℕ}
    (hM : Tendsto (fun n : ℕ => (M n : ℝ) / (n : ℝ)) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (M n), g ((i : ℝ) / (n : ℝ)))
      atTop (𝓝 (∫ θ in (0 : ℝ)..a, g θ)) := by
  have hb0 : (0 : ℝ) ≤ b := le_trans ha hab.le
  have hab' : a ∈ Set.Icc (0 : ℝ) b := ⟨ha, hab.le⟩
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hg
  set Cb : ℝ := max C 0 with hCbdef
  have hCb0 : 0 ≤ Cb := le_max_right _ _
  have hCbnd : ∀ x ∈ Set.Icc (0 : ℝ) b, |g x| ≤ Cb := fun x hx =>
    le_trans (hC x hx) (le_max_left _ _)
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  have hη : (0 : ℝ) < ε / (2 * (b + 1)) := by positivity
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hg) (ε / (2 * (b + 1))) hη
  have hmod' : ∀ x ∈ Set.Icc (0 : ℝ) b, ∀ y ∈ Set.Icc (0 : ℝ) b, |x - y| < δ →
      |g x - g y| ≤ ε / (2 * (b + 1)) := by
    intro x hx y hy hxy
    have h := hmod x hx y hy (by rwa [Real.dist_eq])
    rw [Real.dist_eq] at h
    exact h.le
  have hev1 : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ < δ :=
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).eventually (eventually_lt_nhds hδ)
  have hev2 : ∀ᶠ n : ℕ in atTop, (M n : ℝ) / n < b := hM.eventually (eventually_lt_nhds hab)
  have hev3 : ∀ᶠ n : ℕ in atTop, Cb * |((M n : ℝ) / n) - a| < ε / 2 := by
    have h3 : Tendsto (fun n : ℕ => ((M n : ℝ) / n) - a) atTop (𝓝 0) := by
      simpa using hM.sub_const a
    have h4 : Tendsto (fun n : ℕ => Cb * |((M n : ℝ) / n) - a|) atTop (𝓝 0) := by
      simpa using h3.abs.const_mul Cb
    exact h4.eventually (eventually_lt_nhds (by positivity))
  refine Filter.eventually_atTop.mp ?_
  filter_upwards [hev1, hev2, hev3, eventually_ge_atTop 1] with n hn1 hn2 hn3 hn4
  have hMnb : (M n : ℝ) / n ≤ b := hn2.le
  have hstep := abs_riemann_partial_sub_integral_le hb0 hg hη.le hmod' n (M n) hn4 hn1 hMnb
  have hrhs_le : (M n : ℝ) / n * (ε / (2 * (b + 1))) ≤ ε / 2 := by
    have hlt : (M n : ℝ) / n * (ε / (2 * (b + 1))) < (b + 1) * (ε / (2 * (b + 1))) :=
      mul_lt_mul_of_pos_right (by linarith [hn2]) hη
    have heq : (b + 1) * (ε / (2 * (b + 1))) = ε / 2 := by
      have hb1 : (b + 1 : ℝ) ≠ 0 := by linarith
      field_simp
    linarith [hlt, heq]
  have hlip := abs_integral_zero_sub_le_of_continuousOn hg hCb0 hCbnd hb0
    (⟨by positivity, hMnb⟩ : (M n : ℝ) / n ∈ Set.Icc (0 : ℝ) b) hab'
  rw [Real.dist_eq]
  calc |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range (M n), g ((i : ℝ) / n) - ∫ θ in (0 : ℝ)..a, g θ|
      ≤ |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range (M n), g ((i : ℝ) / n) -
          ∫ θ in (0 : ℝ)..((M n : ℝ) / n), g θ| +
        |(∫ θ in (0 : ℝ)..((M n : ℝ) / n), g θ) - ∫ θ in (0 : ℝ)..a, g θ| :=
        abs_sub_le _ _ _
    _ ≤ (M n : ℝ) / n * (ε / (2 * (b + 1))) + Cb * |((M n : ℝ) / n) - a| :=
        add_le_add hstep hlip
    _ < ε / 2 + ε / 2 := by linarith [hrhs_le, hn3]
    _ = ε := by ring

/-- **The diagonal heat-kernel integrand is antitone away from the origin.** -/
theorem antitoneOn_contHeat_two_mul_zero_zero :
    AntitoneOn (fun θ : ℝ => contHeat (2 * θ) 0 0) (Set.Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  have hx2 : (0 : ℝ) < 2 * x := by linarith
  have hy2 : (0 : ℝ) < 2 * y := by linarith
  simp only
  rw [contHeat_zero_eq hx2 0, contHeat_zero_eq hy2 0]
  have he : ∀ t : ℝ, Real.exp (-2 * (0 : ℝ) ^ 2 / t) = 1 := by
    intro t; norm_num
  rw [he (2 * x), he (2 * y), mul_one, mul_one]
  have hsxy : Real.sqrt (2 * x) ≤ Real.sqrt (2 * y) := Real.sqrt_le_sqrt (by linarith)
  have hsx : 0 < Real.sqrt (2 * x) := Real.sqrt_pos.mpr hx2
  exact mul_le_mul_of_nonneg_left (inv_anti₀ hsx hsxy) (Real.sqrt_nonneg _)

/-- **The doubled diagonal heat kernel is interval-integrable everywhere.** -/
theorem intervalIntegrable_contHeat_two_mul (p q : ℝ) :
    IntervalIntegrable (fun θ => contHeat (2 * θ) 0 0) volume p q := by
  have h := (intervalIntegrable_contHeat_zero (2 * p) (2 * q) 0).comp_mul_left
    (c := 2) (f := fun ψ => contHeat ψ 0 0)
  have hp : (2 : ℝ) * p / 2 = p := by ring
  have hq : (2 : ℝ) * q / 2 = q := by ring
  rwa [hp, hq] at h

/-- **The doubled-time primitive from `0`**, related to `contHeatTimeIntegral` by the
change of variables `ψ = 2θ`. -/
theorem integral_contHeat_two_mul_eq {c : ℝ} (hc : 0 ≤ c) :
    (∫ θ in (0 : ℝ)..c, contHeat (2 * θ) 0 0) = 2⁻¹ * contHeatTimeIntegral (2 * c) 0 := by
  have h := intervalIntegral.integral_comp_mul_left (f := fun ψ => contHeat ψ 0 0)
    (a := (0 : ℝ)) (b := c) (two_ne_zero)
  simp only [mul_zero, smul_eq_mul] at h
  rw [h, contHeatTimeIntegral_eq (by linarith : (0 : ℝ) ≤ 2 * c) 0]

/-- **The doubled-time primitive is continuous.** -/
theorem continuous_integral_contHeat_two_mul :
    Continuous fun c : ℝ => 2⁻¹ * contHeatTimeIntegral (2 * c) 0 :=
  continuous_const.mul (continuous_contHeatTimeIntegral.comp
    (Continuous.prodMk (continuous_const.mul continuous_id) continuous_const))

/-- **Riemann sums of the diagonal heat kernel converge, past the singular endpoint,
to the integral through it.**  Sampling starts at `i = 1` (the sum omits the singular
node `θ = 0`); the drifting endpoint `M n / n → a` with `a > 0`. -/
theorem tendsto_riemann_sum_singular_Ioo {a : ℝ} (ha : 0 < a)
    {M : ℕ → ℕ} (hM : Tendsto (fun n : ℕ => (M n : ℝ) / (n : ℝ)) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        ∑ i ∈ Finset.Ico 1 (M n), contHeat (2 * ((i : ℝ) / n)) 0 0)
      atTop (𝓝 (∫ θ in (0 : ℝ)..a, contHeat (2 * θ) 0 0)) := by
  set g : ℝ → ℝ := fun θ => contHeat (2 * θ) 0 0 with hgdef
  set P : ℝ → ℝ := fun c => 2⁻¹ * contHeatTimeIntegral (2 * c) 0 with hPdef
  have hPeq : ∀ c : ℝ, 0 ≤ c → (∫ θ in (0 : ℝ)..c, g θ) = P c := fun c hc =>
    integral_contHeat_two_mul_eq hc
  have hPcont : Continuous P := continuous_integral_contHeat_two_mul
  have hP0 : P 0 = 0 := by
    show 2⁻¹ * contHeatTimeIntegral (2 * 0) 0 = 0
    rw [mul_zero, contHeatTimeIntegral_nonpos le_rfl, mul_zero]
  have hevM2 : ∀ᶠ n : ℕ in atTop, 2 ≤ M n := by
    have h2 : ∀ᶠ n : ℕ in atTop, a / 2 < (M n : ℝ) / n :=
      hM.eventually (eventually_gt_nhds (by linarith))
    have h5 : ∀ᶠ n : ℕ in atTop, (4 : ℝ) / a ≤ n :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (4 / a))
    filter_upwards [h2, h5, eventually_ge_atTop 1] with n hn2 hn5 hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hlt : a / 2 * n < (M n : ℝ) := (lt_div_iff₀ hn0).mp hn2
    have hn5' : (4 : ℝ) ≤ n * a := (div_le_iff₀ ha).mp hn5
    have hge : (2 : ℝ) ≤ a / 2 * n := by nlinarith [hn5']
    exact_mod_cast hge.trans hlt.le
  have hgi : ∀ p q : ℝ, IntervalIntegrable g volume p q := intervalIntegrable_contHeat_two_mul
  have hbnd : ∀ i : ℕ, 1 ≤ i → ∀ n : ℕ, 1 ≤ n →
      (∫ θ in ((i : ℝ) / n)..(((i + 1 : ℕ) : ℝ) / n), g θ) ≤ g ((i : ℝ) / n) / n ∧
      g ((i : ℝ) / n) / n ≤ ∫ θ in (((i - 1 : ℕ) : ℝ) / n)..((i : ℝ) / n), g θ := by
    intro i hi n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hi0 : (0 : ℝ) < (i : ℝ) / n := div_pos (by exact_mod_cast hi) hn0
    have hile : (i : ℝ) / n ≤ (((i + 1 : ℕ) : ℝ) / n) := by
      apply div_le_div_of_nonneg_right _ hn0.le
      exact_mod_cast Nat.le_succ i
    have hile' : (((i - 1 : ℕ) : ℝ) / n) ≤ (i : ℝ) / n := by
      apply div_le_div_of_nonneg_right _ hn0.le
      exact_mod_cast Nat.sub_le i 1
    have hlen1 : (((i + 1 : ℕ) : ℝ) / n) - (i : ℝ) / n = (n : ℝ)⁻¹ := by
      push_cast; field_simp; ring
    have hlen2 : (i : ℝ) / n - (((i - 1 : ℕ) : ℝ) / n) = (n : ℝ)⁻¹ := by
      have hcast : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
        rw [Nat.cast_sub hi, Nat.cast_one]
      rw [hcast]; field_simp; ring
    refine ⟨?_, ?_⟩
    · have hbound : ∀ θ ∈ Set.Icc ((i : ℝ) / n) (((i + 1 : ℕ) : ℝ) / n), g θ ≤ g ((i : ℝ) / n) :=
        fun θ hθ => antitoneOn_contHeat_two_mul_zero_zero (Set.mem_Ioi.mpr hi0)
          (Set.mem_Ioi.mpr (lt_of_lt_of_le hi0 hθ.1)) hθ.1
      have hI := intervalIntegral.integral_mono_on hile
        (hgi _ _) intervalIntegrable_const hbound
      rw [intervalIntegral.integral_const, smul_eq_mul, hlen1, mul_comm, ← div_eq_mul_inv] at hI
      exact hI
    · have hi1nn : (0 : ℝ) ≤ ((i - 1 : ℕ) : ℝ) / n := div_nonneg (Nat.cast_nonneg _) hn0.le
      have hbound : ∀ θ ∈ Set.Ioo (((i - 1 : ℕ) : ℝ) / n) ((i : ℝ) / n),
          g ((i : ℝ) / n) ≤ g θ := by
        intro θ hθ
        have hθ0 : (0 : ℝ) < θ := lt_of_le_of_lt hi1nn hθ.1
        exact antitoneOn_contHeat_two_mul_zero_zero (Set.mem_Ioi.mpr hθ0)
          (Set.mem_Ioi.mpr hi0) hθ.2.le
      have hI := intervalIntegral.integral_mono_on_of_le_Ioo hile'
        intervalIntegrable_const (hgi _ _) hbound
      rw [intervalIntegral.integral_const, smul_eq_mul, hlen2, mul_comm, ← div_eq_mul_inv] at hI
      exact hI
  have hupper_tel : ∀ n : ℕ, 2 ≤ M n →
      ∑ i ∈ Finset.Ico 1 (M n), (∫ θ in ((i : ℝ) / n)..(((i + 1 : ℕ) : ℝ) / n), g θ)
        = ∫ θ in (((1 : ℕ) : ℝ) / n)..(((M n : ℕ) : ℝ) / n), g θ := fun n hMn2 =>
    intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun k : ℕ => (k : ℝ) / n)
      (by omega) (fun k _ => hgi _ _)
  have hlower_tel : ∀ n : ℕ, 2 ≤ M n →
      ∑ i ∈ Finset.Ico 1 (M n), (∫ θ in (((i - 1 : ℕ) : ℝ) / n)..((i : ℝ) / n), g θ)
        = ∫ θ in (0 : ℝ)..(((M n - 1 : ℕ) : ℝ) / n), g θ := by
    intro n hMn2
    rw [Finset.sum_Ico_eq_sum_range]
    have hcongr : ∀ j ∈ Finset.range (M n - 1),
        (∫ θ in (((1 + j - 1 : ℕ) : ℝ) / n)..(((1 + j : ℕ) : ℝ) / n), g θ) =
          ∫ θ in ((j : ℝ) / n)..(((j + 1 : ℕ) : ℝ) / n), g θ := by
      intro j _
      have e1 : (1 + j - 1 : ℕ) = j := by omega
      have e2 : (1 + j : ℕ) = j + 1 := by omega
      rw [e1, e2]
    rw [Finset.sum_congr rfl hcongr, Finset.range_eq_Ico]
    have h := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun k : ℕ => (k : ℝ) / n) (Nat.zero_le (M n - 1)) (fun k _ => hgi _ _)
    simpa using h
  have hSge : ∀ n : ℕ, 1 ≤ n → 2 ≤ M n →
      (∫ θ in (((1 : ℕ) : ℝ) / n)..(((M n : ℕ) : ℝ) / n), g θ) ≤
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.Ico 1 (M n), g ((i : ℝ) / n) := by
    intro n hn hMn2
    rw [← hupper_tel n hMn2, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    obtain ⟨hi1, _⟩ := Finset.mem_Ico.mp hi
    have hb := (hbnd i hi1 n hn).1
    have heqiv : g ((i : ℝ) / n) / n = (n : ℝ)⁻¹ * g ((i : ℝ) / n) := by
      rw [div_eq_mul_inv, mul_comm]
    rwa [heqiv] at hb
  have hSle : ∀ n : ℕ, 1 ≤ n → 2 ≤ M n →
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.Ico 1 (M n), g ((i : ℝ) / n) ≤
        ∫ θ in (0 : ℝ)..(((M n - 1 : ℕ) : ℝ) / n), g θ := by
    intro n hn hMn2
    rw [← hlower_tel n hMn2, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    obtain ⟨hi1, _⟩ := Finset.mem_Ico.mp hi
    have hb := (hbnd i hi1 n hn).2
    have heqiv : g ((i : ℝ) / n) / n = (n : ℝ)⁻¹ * g ((i : ℝ) / n) := by
      rw [div_eq_mul_inv, mul_comm]
    rwa [heqiv] at hb
  have hlow_eq : ∀ n : ℕ, 1 ≤ n →
      (∫ θ in (((1 : ℕ) : ℝ) / n)..(((M n : ℕ) : ℝ) / n), g θ)
        = P ((M n : ℝ) / n) - P ((n : ℝ)⁻¹) := by
    intro n hn
    have h1n : ((1 : ℕ) : ℝ) / n = (n : ℝ)⁻¹ := by norm_num
    rw [h1n]
    have hI1 : IntervalIntegrable g volume 0 ((n : ℝ)⁻¹) := hgi _ _
    have hI2 : IntervalIntegrable g volume ((n : ℝ)⁻¹) ((M n : ℝ) / n) := hgi _ _
    have hadd := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
    rw [hPeq ((n : ℝ)⁻¹) (by positivity), hPeq ((M n : ℝ) / n) (by positivity)] at hadd
    linarith [hadd]
  have htendsto_inv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlow_lim : Tendsto (fun n : ℕ =>
      ∫ θ in (((1 : ℕ) : ℝ) / n)..(((M n : ℕ) : ℝ) / n), g θ) atTop (𝓝 (P a)) := by
    have heq : (fun n : ℕ => ∫ θ in (((1 : ℕ) : ℝ) / n)..(((M n : ℕ) : ℝ) / n), g θ) =ᶠ[atTop]
        (fun n : ℕ => P ((M n : ℝ) / n) - P ((n : ℝ)⁻¹)) := by
      filter_upwards [eventually_ge_atTop 1] with n hn using hlow_eq n hn
    have hlim : Tendsto (fun n : ℕ => P ((M n : ℝ) / n) - P ((n : ℝ)⁻¹)) atTop
        (𝓝 (P a - P 0)) :=
      ((hPcont.tendsto a).comp hM).sub ((hPcont.tendsto 0).comp htendsto_inv)
    rw [hP0, sub_zero] at hlim
    exact hlim.congr' heq.symm
  have hMsub_lim : Tendsto (fun n : ℕ => (((M n - 1 : ℕ) : ℝ) / n)) atTop (𝓝 a) := by
    have heq : (fun n : ℕ => (((M n - 1 : ℕ) : ℝ) / n)) =ᶠ[atTop]
        (fun n : ℕ => (M n : ℝ) / n - (n : ℝ)⁻¹) := by
      filter_upwards [hevM2] with n hn2
      rw [Nat.cast_sub (by omega), Nat.cast_one, sub_div, one_div]
    have hlim : Tendsto (fun n : ℕ => (M n : ℝ) / n - (n : ℝ)⁻¹) atTop (𝓝 (a - 0)) :=
      hM.sub htendsto_inv
    rw [sub_zero] at hlim
    exact hlim.congr' heq.symm
  have hhigh_lim : Tendsto (fun n : ℕ =>
      ∫ θ in (0 : ℝ)..(((M n - 1 : ℕ) : ℝ) / n), g θ) atTop (𝓝 (P a)) := by
    have heq : (fun n : ℕ => ∫ θ in (0 : ℝ)..(((M n - 1 : ℕ) : ℝ) / n), g θ) =ᶠ[atTop]
        (fun n : ℕ => P (((M n - 1 : ℕ) : ℝ) / n)) := by
      filter_upwards with n
      exact hPeq _ (by positivity)
    exact ((hPcont.tendsto a).comp hMsub_lim).congr' heq.symm
  have hfinal : Tendsto (fun n : ℕ =>
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.Ico 1 (M n), g ((i : ℝ) / n)) atTop (𝓝 (P a)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_lim hhigh_lim ?_ ?_
    · filter_upwards [hevM2, eventually_ge_atTop 1] with n hn2 hn1 using hSge n hn1 hn2
    · filter_upwards [hevM2, eventually_ge_atTop 1] with n hn2 hn1 using hSle n hn1 hn2
  have hgoal_eq : (fun n : ℕ => (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.Ico 1 (M n), contHeat (2 * ((i : ℝ) / n)) 0 0)
      = fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.Ico 1 (M n), g ((i : ℝ) / n) := rfl
  rw [hgoal_eq, hPeq a ha.le]
  exact hfinal

/-- **`heatApprox` is Lipschitz in its first argument on any range bounded below**,
with no need for the range to lie above `1`. -/
theorem abs_heatApprox_sub_fst' {a b a0 : ℝ} (ha0 : 0 < a0) (ha : a0 ≤ a) (hb : a0 ≤ b)
    (v : ℝ) :
    |heatApprox a v - heatApprox b v| ≤
      (Real.sqrt (2 / Real.pi) / (min a b * Real.sqrt (min a b))) * |a - b| := by
  have hmin : 0 < min a b := lt_min (lt_of_lt_of_le ha0 ha) (lt_of_lt_of_le ha0 hb)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun c => heatApprox c v)
    (f' := fun c => Real.sqrt (2 / Real.pi) * Real.exp (-(v ^ 2 / (2 * c))) * (v ^ 2 - c) /
      (2 * c ^ 2 * Real.sqrt c))
    (s := Set.Icc (min a b) (max a b))
    (C := Real.sqrt (2 / Real.pi) / (min a b * Real.sqrt (min a b)))
    (fun y hy =>
      (hasDerivAt_heatApprox_fst y
        (lt_of_lt_of_le hmin (Set.mem_Icc.mp hy).1) v).hasDerivWithinAt)
    (fun y hy => by
      have hy1 : min a b ≤ y := (Set.mem_Icc.mp hy).1
      have hy0 : 0 < y := lt_of_lt_of_le hmin hy1
      rw [Real.norm_eq_abs]
      exact (abs_deriv_heatApprox_fst_le y hy0 v).trans
        (div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
          (mul_pos hmin (Real.sqrt_pos.mpr hmin))
          (mul_le_mul hy1 (Real.sqrt_le_sqrt hy1) (Real.sqrt_nonneg _)
            (hmin.le.trans hy1))))
    (convex_Icc (min a b) (max a b))
    (Set.mem_Icc.mpr ⟨min_le_left a b, le_max_left a b⟩)
    (Set.mem_Icc.mpr ⟨min_le_right a b, le_max_right a b⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  rw [abs_sub_comm (heatApprox a v) (heatApprox b v), abs_sub_comm a b]
  exact h

/-- **`heatApprox` is jointly Lipschitz on any range bounded below**, with an explicit
constant depending only on the lower bound `a0`. -/
theorem abs_heatApprox_sub' {a b a0 : ℝ} (ha0 : 0 < a0) (ha : a0 ≤ a) (hb : a0 ≤ b)
    (u v : ℝ) :
    |heatApprox a u - heatApprox b v| ≤
      (Real.sqrt (2 / Real.pi) / a0) * |u - v| +
        (Real.sqrt (2 / Real.pi) / (a0 * Real.sqrt a0)) * |a - b| := by
  have hmin : a0 ≤ min a b := le_min ha hb
  have hminpos : 0 < min a b := lt_of_lt_of_le ha0 hmin
  calc |heatApprox a u - heatApprox b v|
      = |(heatApprox a u - heatApprox a v) + (heatApprox a v - heatApprox b v)| := by
        rw [sub_add_sub_cancel]
    _ ≤ |heatApprox a u - heatApprox a v| + |heatApprox a v - heatApprox b v| :=
        abs_add_le _ _
    _ ≤ (Real.sqrt (2 / Real.pi) / a) * |u - v| +
          (Real.sqrt (2 / Real.pi) / (min a b * Real.sqrt (min a b))) * |a - b| :=
        add_le_add (abs_heatApprox_sub_snd a (lt_of_lt_of_le ha0 ha) u v)
          (abs_heatApprox_sub_fst' ha0 ha hb v)
    _ ≤ (Real.sqrt (2 / Real.pi) / a0) * |u - v| +
          (Real.sqrt (2 / Real.pi) / (a0 * Real.sqrt a0)) * |a - b| := by
        gcongr

/-- **The diagonal heat-kernel is jointly Lipschitz in the delay and displacement**,
uniformly once the total elapsed time is bounded below. -/
theorem abs_contHeat_two_mul_sub {δ δ' d d' θ a0 : ℝ} (ha0 : 0 < a0)
    (hδ : a0 ≤ 2 * θ + δ) (hδ' : a0 ≤ 2 * θ + δ') :
    |contHeat (2 * θ + δ) 0 d - contHeat (2 * θ + δ') 0 d'| ≤
      (Real.sqrt (2 / Real.pi) / a0) * |2 * d - 2 * d'| +
        (Real.sqrt (2 / Real.pi) / (a0 * Real.sqrt a0)) * |δ - δ'| := by
  have ht : (0 : ℝ) < 2 * θ + δ := lt_of_lt_of_le ha0 hδ
  have ht' : (0 : ℝ) < 2 * θ + δ' := lt_of_lt_of_le ha0 hδ'
  have heq : contHeat (2 * θ + δ) 0 d = heatApprox (2 * θ + δ) (2 * d) := by
    rw [contHeat_zero_eq ht d]
    unfold heatApprox
    congr 2
    rw [mul_pow]
    field_simp
  have heq' : contHeat (2 * θ + δ') 0 d' = heatApprox (2 * θ + δ') (2 * d') := by
    rw [contHeat_zero_eq ht' d']
    unfold heatApprox
    congr 2
    rw [mul_pow]
    field_simp
  rw [heq, heq']
  have hab : |(2 * θ + δ) - (2 * θ + δ')| = |δ - δ'| := by
    rw [show (2 * θ + δ) - (2 * θ + δ') = δ - δ' from by ring]
  rw [← hab]
  exact abs_heatApprox_sub' ha0 hδ hδ' (2 * d) (2 * d')

/-- **Riemann sums of the heat kernel converge along a jointly drifting delay,
displacement and endpoint**, provided the limit delay is strictly positive (so the
kernel stays away from its singularity, uniformly, throughout the sum). -/
theorem tendsto_riemann_sum_Ioo_param_pos {δstar dstar a b : ℝ} (hδstar : 0 < δstar)
    (ha : 0 ≤ a) (hab : a < b) {δn dn : ℕ → ℝ} (hδn : Tendsto δn atTop (𝓝 δstar))
    (hdn : Tendsto dn atTop (𝓝 dstar)) {M : ℕ → ℕ}
    (hM : Tendsto (fun n : ℕ => (M n : ℝ) / (n : ℝ)) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (M n), contHeat (2 * ((i : ℝ) / n) + δn n) 0 (dn n))
      atTop (𝓝 (∫ θ in (0 : ℝ)..a, contHeat (2 * θ + δstar) 0 dstar)) := by
  have htarget := tendsto_riemann_sum_Ioo_of_continuousOn ha hab
    (continuousOn_contHeat_two_mul_add_zero (δ := δstar) (d := dstar) hδstar.le
      (Or.inl hδstar) b) hM
  suffices hdiff : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range (M n), contHeat (2 * ((i : ℝ) / n) + δn n) 0 (dn n) -
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (M n), contHeat (2 * ((i : ℝ) / n) + δstar) 0 dstar)
      atTop (𝓝 0) by
    have hsum := hdiff.add htarget
    simpa using hsum
  set a0 : ℝ := δstar / 2 with ha0def
  have ha0pos : 0 < a0 := by positivity
  have hev_close : ∀ᶠ n : ℕ in atTop, a0 ≤ δn n :=
    hδn.eventually (eventually_ge_nhds (by linarith : a0 < δstar))
  have hbound_diff : ∀ᶠ n : ℕ in atTop, ∀ θ : ℝ, 0 ≤ θ →
      |contHeat (2 * θ + δn n) 0 (dn n) - contHeat (2 * θ + δstar) 0 dstar| ≤
        (Real.sqrt (2 / Real.pi) / a0) * |2 * dn n - 2 * dstar| +
          (Real.sqrt (2 / Real.pi) / (a0 * Real.sqrt a0)) * |δn n - δstar| := by
    filter_upwards [hev_close] with n hn θ hθ
    exact abs_contHeat_two_mul_sub ha0pos (by linarith) (by linarith)
  set Cn : ℕ → ℝ := fun n => (Real.sqrt (2 / Real.pi) / a0) * |2 * dn n - 2 * dstar| +
      (Real.sqrt (2 / Real.pi) / (a0 * Real.sqrt a0)) * |δn n - δstar| with hCndef
  have hCn0 : Tendsto Cn atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 2 * dn n - 2 * dstar) atTop (𝓝 0) := by
      have h := (hdn.const_mul (2 : ℝ)).sub_const (2 * dstar)
      simpa using h
    have h2 : Tendsto (fun n : ℕ => δn n - δstar) atTop (𝓝 0) := by
      simpa using hδn.sub_const δstar
    have h3 : Tendsto (fun n : ℕ =>
        (Real.sqrt (2 / Real.pi) / a0) * |2 * dn n - 2 * dstar|) atTop (𝓝 0) := by
      simpa using (h1.abs).const_mul (Real.sqrt (2 / Real.pi) / a0)
    have h4 : Tendsto (fun n : ℕ =>
        (Real.sqrt (2 / Real.pi) / (a0 * Real.sqrt a0)) * |δn n - δstar|) atTop (𝓝 0) := by
      simpa using (h2.abs).const_mul (Real.sqrt (2 / Real.pi) / (a0 * Real.sqrt a0))
    simpa [hCndef] using h3.add h4
  have hMbnd : ∀ᶠ n : ℕ in atTop, (M n : ℝ) / n ≤ b :=
    hM.eventually (eventually_le_nhds hab)
  have hfinalbnd : ∀ᶠ n : ℕ in atTop, ‖(n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range (M n), contHeat (2 * ((i : ℝ) / n) + δn n) 0 (dn n) -
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (M n), contHeat (2 * ((i : ℝ) / n) + δstar) 0 dstar‖
        ≤ b * ‖Cn n‖ := by
    filter_upwards [hbound_diff, hMbnd, eventually_ge_atTop 1] with n hbdn hMle hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hMnn : (0 : ℝ) ≤ (M n : ℝ) / n := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ Cn n)]
    have hstep : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (M n), contHeat (2 * ((i : ℝ) / n) + δn n) 0 (dn n) -
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (M n), contHeat (2 * ((i : ℝ) / n) + δstar) 0 dstar
        = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (M n),
            (contHeat (2 * ((i : ℝ) / n) + δn n) 0 (dn n) -
              contHeat (2 * ((i : ℝ) / n) + δstar) 0 dstar) := by
      rw [← mul_sub, ← Finset.sum_sub_distrib]
    rw [hstep, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)⁻¹)]
    have hsum_le : |∑ i ∈ Finset.range (M n),
        (contHeat (2 * ((i : ℝ) / n) + δn n) 0 (dn n) -
          contHeat (2 * ((i : ℝ) / n) + δstar) 0 dstar)|
        ≤ ∑ i ∈ Finset.range (M n), Cn n :=
      le_trans (Finset.abs_sum_le_sum_abs _ _)
        (Finset.sum_le_sum fun i _ => hbdn ((i : ℝ) / n) (by positivity))
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum_le
    calc (n : ℝ)⁻¹ * |∑ i ∈ Finset.range (M n),
          (contHeat (2 * ((i : ℝ) / n) + δn n) 0 (dn n) -
            contHeat (2 * ((i : ℝ) / n) + δstar) 0 dstar)|
        ≤ (n : ℝ)⁻¹ * ((M n : ℝ) * Cn n) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = (M n : ℝ) / n * Cn n := by ring
      _ ≤ b * Cn n := by
          apply mul_le_mul_of_nonneg_right hMle (by positivity)
  have hCnnn : Tendsto (fun n => b * ‖Cn n‖) atTop (𝓝 0) := by
    have h := hCn0.norm
    rw [norm_zero] at h
    simpa using h.const_mul b
  exact squeeze_zero_norm' hfinalbnd hCnnn

/-- **The doubled diagonal heat kernel dominates every displacement**: `d = 0` maximizes
`contHeat (2θ) 0 d` at each fixed time. -/
theorem contHeat_le_contHeat_zero_zero {t : ℝ} (ht : 0 ≤ t) (d : ℝ) :
    contHeat t 0 d ≤ contHeat t 0 0 := by
  rcases ht.eq_or_lt with ht0 | ht0
  · rw [contHeat_of_nonpos ht0.symm.le 0 d, contHeat_of_nonpos ht0.symm.le 0 0]
  · rw [contHeat_zero_eq ht0 0]
    have h0 : Real.exp (-2 * (0 : ℝ) ^ 2 / t) = 1 := by norm_num
    rw [h0, mul_one]
    exact contHeat_zero_le ht0 d

/-- **One step of the antitone sandwich, in standalone form**: the discrete term
`contHeat(2i/n,0,0)/n` is at most the integral of the same kernel over the interval
immediately to its left. -/
theorem contHeat_two_mul_zero_zero_prev_bnd {n i : ℕ} (hi : 1 ≤ i) (hn : 1 ≤ n) :
    contHeat (2 * ((i : ℝ) / n)) 0 0 / n ≤
      ∫ θ in (((i - 1 : ℕ) : ℝ) / n)..((i : ℝ) / n), contHeat (2 * θ) 0 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hi0 : (0 : ℝ) < (i : ℝ) / n := div_pos (by exact_mod_cast hi) hn0
  have hile' : (((i - 1 : ℕ) : ℝ) / n) ≤ (i : ℝ) / n := by
    apply div_le_div_of_nonneg_right _ hn0.le
    exact_mod_cast Nat.sub_le i 1
  have hlen2 : (i : ℝ) / n - (((i - 1 : ℕ) : ℝ) / n) = (n : ℝ)⁻¹ := by
    have hcast : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
      rw [Nat.cast_sub hi, Nat.cast_one]
    rw [hcast]; field_simp; ring
  have hi1nn : (0 : ℝ) ≤ ((i - 1 : ℕ) : ℝ) / n := div_nonneg (Nat.cast_nonneg _) hn0.le
  have hbound : ∀ θ ∈ Set.Ioo (((i - 1 : ℕ) : ℝ) / n) ((i : ℝ) / n),
      contHeat (2 * ((i : ℝ) / n)) 0 0 ≤ contHeat (2 * θ) 0 0 := by
    intro θ hθ
    have hθ0 : (0 : ℝ) < θ := lt_of_le_of_lt hi1nn hθ.1
    exact antitoneOn_contHeat_two_mul_zero_zero (Set.mem_Ioi.mpr hθ0) (Set.mem_Ioi.mpr hi0) hθ.2.le
  have hI := intervalIntegral.integral_mono_on_of_le_Ioo hile'
    intervalIntegrable_const (intervalIntegrable_contHeat_two_mul _ _) hbound
  rw [intervalIntegral.integral_const, smul_eq_mul, hlen2, mul_comm, ← div_eq_mul_inv] at hI
  exact hI

/-- **Telescoped upper bound on `Ico 1 m`**: the discrete average over the indices `1`
through `m-1` is at most the integral up to `(m-1)/n`. -/
theorem sum_Ico_one_contHeat_two_mul_zero_zero_le (n m : ℕ) (hn : 1 ≤ n) (_hm : 1 ≤ m) :
    (n : ℝ)⁻¹ * ∑ i ∈ Finset.Ico 1 m, contHeat (2 * ((i : ℝ) / n)) 0 0 ≤
      ∫ θ in (0 : ℝ)..(((m - 1 : ℕ) : ℝ) / n), contHeat (2 * θ) 0 0 := by
  have htel : ∑ i ∈ Finset.Ico 1 m,
        (∫ θ in (((i - 1 : ℕ) : ℝ) / n)..((i : ℝ) / n), contHeat (2 * θ) 0 0)
      = ∫ θ in (0 : ℝ)..(((m - 1 : ℕ) : ℝ) / n), contHeat (2 * θ) 0 0 := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hcongr : ∀ j ∈ Finset.range (m - 1),
        (∫ θ in (((1 + j - 1 : ℕ) : ℝ) / n)..(((1 + j : ℕ) : ℝ) / n), contHeat (2 * θ) 0 0) =
          ∫ θ in ((j : ℝ) / n)..(((j + 1 : ℕ) : ℝ) / n), contHeat (2 * θ) 0 0 := by
      intro j _
      have e1 : (1 + j - 1 : ℕ) = j := by omega
      have e2 : (1 + j : ℕ) = j + 1 := by omega
      rw [e1, e2]
    rw [Finset.sum_congr rfl hcongr, Finset.range_eq_Ico]
    have h := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (a := fun k : ℕ => (k : ℝ) / n) (Nat.zero_le (m - 1))
      (fun k _ => intervalIntegrable_contHeat_two_mul _ _)
    simpa using h
  rw [Finset.mul_sum]
  calc ∑ i ∈ Finset.Ico 1 m, (n : ℝ)⁻¹ * contHeat (2 * ((i : ℝ) / n)) 0 0
      ≤ ∑ i ∈ Finset.Ico 1 m,
          (∫ θ in (((i - 1 : ℕ) : ℝ) / n)..((i : ℝ) / n), contHeat (2 * θ) 0 0) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi1 := (Finset.mem_Ico.mp hi).1
        calc (n : ℝ)⁻¹ * contHeat (2 * ((i : ℝ) / n)) 0 0
            = contHeat (2 * ((i : ℝ) / n)) 0 0 / n := by ring
          _ ≤ _ := contHeat_two_mul_zero_zero_prev_bnd hi1 hn
    _ = ∫ θ in (0 : ℝ)..(((m - 1 : ℕ) : ℝ) / n), contHeat (2 * θ) 0 0 := htel

/-- **Crude upper bound on a discrete average of the doubled diagonal heat kernel**: the
average over the first `m` indices is at most the integral of the same kernel from `0` to
any `c` with `m/n ≤ c`.  Controls the near-origin part of a Riemann sum uniformly in `n`. -/
theorem sum_range_contHeat_two_mul_zero_zero_le (n m : ℕ) (hn : 1 ≤ n) {c : ℝ} (hc : 0 ≤ c)
    (hm : (m : ℝ) / n ≤ c) :
    (n : ℝ)⁻¹ * ∑ i ∈ Finset.range m, contHeat (2 * ((i : ℝ) / n)) 0 0 ≤
      ∫ θ in (0 : ℝ)..c, contHeat (2 * θ) 0 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero]
    exact intervalIntegral.integral_nonneg hc (fun θ _ => contHeat_nonneg _ 0 0)
  · have heq0 : contHeat (2 * (((0 : ℕ) : ℝ) / (n : ℝ))) 0 0 = 0 := by
      simp only [Nat.cast_zero, zero_div, mul_zero]
      exact contHeat_of_nonpos (le_refl 0) 0 0
    have hrange_eq : ∑ i ∈ Finset.range m, contHeat (2 * ((i : ℝ) / n)) 0 0 =
        ∑ i ∈ Finset.Ico 1 m, contHeat (2 * ((i : ℝ) / n)) 0 0 :=
      (Finset.sum_subset
        (fun x hx => by
          rw [Finset.mem_Ico] at hx
          rw [Finset.mem_range]; omega)
        (fun x hx hxnot => by
          rw [Finset.mem_range] at hx
          rw [Finset.mem_Ico] at hxnot
          have hx0 : x = 0 := by
            by_contra hxne
            exact hxnot ⟨Nat.one_le_iff_ne_zero.mpr hxne, hx⟩
          subst hx0
          exact heq0)).symm
    rw [hrange_eq]
    refine (sum_Ico_one_contHeat_two_mul_zero_zero_le n m hn hm0).trans ?_
    have hnum_le : (((m - 1 : ℕ) : ℝ)) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m 1
    have hle : (((m - 1 : ℕ) : ℝ) / n) ≤ c := by
      calc (((m - 1 : ℕ) : ℝ) / n) ≤ (m : ℝ) / n :=
            div_le_div_of_nonneg_right hnum_le hn0.le
        _ ≤ c := hm
    have hadd : (∫ θ in (0 : ℝ)..(((m - 1 : ℕ) : ℝ) / n), contHeat (2 * θ) 0 0) +
        (∫ θ in (((m - 1 : ℕ) : ℝ) / n)..c, contHeat (2 * θ) 0 0) =
        ∫ θ in (0 : ℝ)..c, contHeat (2 * θ) 0 0 :=
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_contHeat_two_mul _ _) (intervalIntegrable_contHeat_two_mul _ _)
    have hnonneg : (0 : ℝ) ≤ ∫ θ in (((m - 1 : ℕ) : ℝ) / n)..c, contHeat (2 * θ) 0 0 :=
      intervalIntegral.integral_nonneg hle (fun θ _ => contHeat_nonneg _ 0 0)
    linarith [hadd, hnonneg]

/-- **The crude bound, at any fixed displacement**: dominating each summand by its value at
`d = 0` turns `sum_range_contHeat_two_mul_zero_zero_le` into a bound valid for every `d`. -/
theorem sum_range_contHeat_two_mul_zero_le (n m : ℕ) (hn : 1 ≤ n) {c : ℝ} (hc : 0 ≤ c)
    (hm : (m : ℝ) / n ≤ c) (d : ℝ) :
    (n : ℝ)⁻¹ * ∑ i ∈ Finset.range m, contHeat (2 * ((i : ℝ) / n)) 0 d ≤
      ∫ θ in (0 : ℝ)..c, contHeat (2 * θ) 0 0 := by
  refine le_trans ?_ (sum_range_contHeat_two_mul_zero_zero_le n m hn hc hm)
  apply mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)
  exact Finset.sum_le_sum fun i _ => contHeat_le_contHeat_zero_zero (by positivity) d

/-- **The doubled-time primitive is monotone** in its endpoint, since the integrand is
nonnegative. -/
theorem monotoneOn_integral_contHeat_two_mul :
    MonotoneOn (fun c => ∫ θ in (0 : ℝ)..c, contHeat (2 * θ) 0 0) (Set.Ici (0 : ℝ)) := by
  intro c1 hc1 c2 hc2 h12
  simp only [Set.mem_Ici] at hc1 hc2
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_contHeat_two_mul (0 : ℝ) c1) (intervalIntegrable_contHeat_two_mul c1 c2)
  have hnn : (0 : ℝ) ≤ ∫ θ in c1..c2, contHeat (2 * θ) 0 0 :=
    intervalIntegral.integral_nonneg h12 (fun θ _ => contHeat_nonneg _ 0 0)
  linarith [hadd]

/-- **Riemann sums of the heat kernel converge at a fixed elapsed time, along a drifting
nonzero displacement.**  The case `δn n = 0` identically (two points at the SAME rescaled
time, different rescaled space) omitted by `tendsto_riemann_sum_Ioo_param_pos`, whose
Lipschitz technique needs the delay bounded away from `0` uniformly in `θ`: here there is no
delay at all, so the bound is built instead by splitting the sum at a fixed `θ₀ > 0`, crudely
bounding the near-origin piece (on both sides of the comparison) by the antitone integral
`sum_range_contHeat_two_mul_zero_le`, and Lipschitz-comparing the rest via
`abs_contHeat_two_mul_sub` at `δ = δ' = 0`. -/
theorem tendsto_riemann_sum_Ioo_same_time {dstar a b : ℝ} (hdstar : dstar ≠ 0) (ha : 0 ≤ a)
    (hab : a < b) {dn : ℕ → ℝ} (hdn : Tendsto dn atTop (𝓝 dstar)) {M : ℕ → ℕ}
    (hM : Tendsto (fun n : ℕ => (M n : ℝ) / (n : ℝ)) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (M n), contHeat (2 * ((i : ℝ) / n)) 0 (dn n))
      atTop (𝓝 (∫ θ in (0 : ℝ)..a, contHeat (2 * θ) 0 dstar)) := by
  have htarget := tendsto_riemann_sum_Ioo_of_continuousOn ha hab
    (continuousOn_contHeat_two_mul_add_zero (δ := (0 : ℝ)) (d := dstar) le_rfl (Or.inr hdstar) b)
    hM
  simp only [add_zero] at htarget
  suffices hdiff : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range (M n), contHeat (2 * ((i : ℝ) / n)) 0 (dn n) -
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (M n), contHeat (2 * ((i : ℝ) / n)) 0 dstar)
      atTop (𝓝 0) by
    have hsum := hdiff.add htarget
    simpa using hsum
  rw [Metric.tendsto_atTop]
  intro ε hε
  set P : ℝ → ℝ := fun c => 2⁻¹ * contHeatTimeIntegral (2 * c) 0 with hPdef
  have hPcont : Continuous P := continuous_integral_contHeat_two_mul
  have hPeq : ∀ c : ℝ, 0 ≤ c → (∫ θ in (0 : ℝ)..c, contHeat (2 * θ) 0 0) = P c :=
    fun c hc => integral_contHeat_two_mul_eq hc
  have hP0 : P 0 = 0 := by
    show (2 : ℝ)⁻¹ * contHeatTimeIntegral (2 * 0) 0 = 0
    rw [mul_zero, contHeatTimeIntegral_nonpos le_rfl, mul_zero]
  have hPnn : ∀ c : ℝ, 0 ≤ c → 0 ≤ P c := by
    intro c hc
    rw [← hPeq c hc]
    exact intervalIntegral.integral_nonneg hc (fun θ _ => contHeat_nonneg _ 0 0)
  have hPcont2 : Continuous (fun c : ℝ => 2 * P (2 * c)) :=
    continuous_const.mul (hPcont.comp (continuous_const.mul continuous_id))
  have hP0' : (2 : ℝ) * P (2 * 0) = 0 := by
    have h20 : (2 : ℝ) * 0 = 0 := by ring
    rw [h20, hP0, mul_zero]
  have hcont0 : Tendsto (fun c : ℝ => 2 * P (2 * c)) (𝓝 0) (𝓝 0) := by
    have h := hPcont2.tendsto (0 : ℝ)
    rwa [hP0'] at h
  obtain ⟨δ, hδpos, hδ⟩ := Metric.tendsto_nhds_nhds.mp hcont0 (ε / 2) (by linarith)
  set θ0 : ℝ := δ / 2 with hθ0def
  have hθ0pos : 0 < θ0 := by positivity
  have hθ0lt : |θ0 - 0| < δ := by
    rw [sub_zero, abs_of_pos hθ0pos, hθ0def]
    linarith
  have hkey : |2 * P (2 * θ0) - 0| < ε / 2 := by
    have := hδ (show dist θ0 0 < δ by rwa [Real.dist_eq])
    rwa [Real.dist_eq] at this
  have hPθ0nn : (0 : ℝ) ≤ 2 * P (2 * θ0) := by
    have := hPnn (2 * θ0) (by positivity)
    linarith
  rw [sub_zero, abs_of_nonneg hPθ0nn] at hkey
  -- hkey : 2 * P (2 * θ0) < ε / 2
  set mfun : ℕ → ℕ := fun n => ⌈(n : ℝ) * θ0⌉₊ with hmfundef
  set kfun : ℕ → ℕ := fun n => min (mfun n) (M n) with hkfundef
  set Cθ0 : ℕ → ℝ := fun n => (Real.sqrt (2 / Real.pi) / (2 * θ0)) * |2 * dn n - 2 * dstar|
    with hCθ0def
  have hCθ0lim : Tendsto Cθ0 atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 2 * dn n - 2 * dstar) atTop (𝓝 0) := by
      have h := (hdn.const_mul (2 : ℝ)).sub_const (2 * dstar)
      simpa using h
    simpa [hCθ0def] using (h1.abs).const_mul (Real.sqrt (2 / Real.pi) / (2 * θ0))
  have hev1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / n ≤ θ0 := by
    have h : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have h2 : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ ≤ θ0 := h.eventually (eventually_le_nhds hθ0pos)
    simpa [one_div] using h2
  have hev3 : ∀ᶠ n : ℕ in atTop, (M n : ℝ) / n < b := hM.eventually (eventually_lt_nhds hab)
  have hev4 : ∀ᶠ n : ℕ in atTop, b * Cθ0 n < ε / 2 := by
    have h4 : Tendsto (fun n : ℕ => b * Cθ0 n) atTop (𝓝 0) := by
      simpa using hCθ0lim.const_mul b
    exact h4.eventually (eventually_lt_nhds (by linarith))
  refine Filter.eventually_atTop.mp ?_
  filter_upwards [hev1, hev3, hev4, eventually_ge_atTop 1] with n hn1 hn3 hn4 hnge1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnge1
  have hksplit : Finset.range (M n) = Finset.Ico 0 (kfun n) ∪ Finset.Ico (kfun n) (M n) := by
    rw [Finset.range_eq_Ico]
    exact (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (min_le_right (mfun n) (M n))).symm
  have hkle : (kfun n : ℝ) / n ≤ 2 * θ0 := by
    have h1 : kfun n ≤ mfun n := min_le_left _ _
    have h2 : (kfun n : ℝ) / n ≤ (mfun n : ℝ) / n :=
      div_le_div_of_nonneg_right (by exact_mod_cast h1) hn0.le
    have h3 : (mfun n : ℝ) < (n : ℝ) * θ0 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h4 : (mfun n : ℝ) / n < θ0 + 1 / n := by
      rw [div_lt_iff₀ hn0, add_mul, div_mul_cancel₀ _ hn0.ne', mul_comm θ0 (n : ℝ)]
      linarith [h3]
    have h5 : (1 : ℝ) / n ≤ θ0 := hn1
    linarith [h2, h4, h5]
  have hsmall : (n : ℝ)⁻¹ *
      |∑ i ∈ Finset.range (kfun n), (contHeat (2 * ((i : ℝ) / n)) 0 (dn n) -
          contHeat (2 * ((i : ℝ) / n)) 0 dstar)| < ε / 2 := by
    have hstep : (n : ℝ)⁻¹ *
        |∑ i ∈ Finset.range (kfun n), (contHeat (2 * ((i : ℝ) / n)) 0 (dn n) -
            contHeat (2 * ((i : ℝ) / n)) 0 dstar)|
        ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (kfun n),
            (contHeat (2 * ((i : ℝ) / n)) 0 (dn n) + contHeat (2 * ((i : ℝ) / n)) 0 dstar) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      exact (abs_sub _ _).trans (by
        rw [abs_of_nonneg (contHeat_nonneg _ 0 (dn n)), abs_of_nonneg (contHeat_nonneg _ 0 dstar)])
    have hsplit2 : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (kfun n),
        (contHeat (2 * ((i : ℝ) / n)) 0 (dn n) + contHeat (2 * ((i : ℝ) / n)) 0 dstar)
        = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (kfun n), contHeat (2 * ((i : ℝ) / n)) 0 (dn n) +
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (kfun n), contHeat (2 * ((i : ℝ) / n)) 0 dstar := by
      rw [Finset.sum_add_distrib, mul_add]
    have hb1 : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (kfun n), contHeat (2 * ((i : ℝ) / n)) 0 (dn n) ≤
        P (2 * θ0) := by
      rw [← hPeq (2 * θ0) (by positivity)]
      exact sum_range_contHeat_two_mul_zero_le n (kfun n) hnge1 (by positivity) hkle (dn n)
    have hb2 : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (kfun n), contHeat (2 * ((i : ℝ) / n)) 0 dstar ≤
        P (2 * θ0) := by
      rw [← hPeq (2 * θ0) (by positivity)]
      exact sum_range_contHeat_two_mul_zero_le n (kfun n) hnge1 (by positivity) hkle dstar
    calc (n : ℝ)⁻¹ *
        |∑ i ∈ Finset.range (kfun n), (contHeat (2 * ((i : ℝ) / n)) 0 (dn n) -
            contHeat (2 * ((i : ℝ) / n)) 0 dstar)|
        ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (kfun n),
            (contHeat (2 * ((i : ℝ) / n)) 0 (dn n) + contHeat (2 * ((i : ℝ) / n)) 0 dstar) :=
          hstep
      _ = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (kfun n), contHeat (2 * ((i : ℝ) / n)) 0 (dn n) +
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (kfun n), contHeat (2 * ((i : ℝ) / n)) 0 dstar := hsplit2
      _ ≤ P (2 * θ0) + P (2 * θ0) := add_le_add hb1 hb2
      _ = 2 * P (2 * θ0) := by ring
      _ < ε / 2 := hkey
  have hlarge_idx : ∀ i, kfun n ≤ i → i < M n → mfun n ≤ i := by
    intro i hki hiM
    rcases le_total (mfun n) (M n) with h | h
    · have hkeq : kfun n = mfun n := min_eq_left h
      omega
    · have hkeq : kfun n = M n := min_eq_right h
      omega
  have hlarge : (n : ℝ)⁻¹ *
      |∑ i ∈ Finset.Ico (kfun n) (M n), (contHeat (2 * ((i : ℝ) / n)) 0 (dn n) -
          contHeat (2 * ((i : ℝ) / n)) 0 dstar)| < ε / 2 := by
    have hterm : ∀ i ∈ Finset.Ico (kfun n) (M n),
        |contHeat (2 * ((i : ℝ) / n)) 0 (dn n) - contHeat (2 * ((i : ℝ) / n)) 0 dstar| ≤
          Cθ0 n := by
      intro i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.mp hi
      have hige : mfun n ≤ i := hlarge_idx i hi1 hi2
      have hige' : (n : ℝ) * θ0 ≤ (i : ℝ) := (Nat.le_ceil ((n : ℝ) * θ0)).trans (by exact_mod_cast hige)
      have hthetage : θ0 ≤ (i : ℝ) / n := by
        rw [le_div_iff₀ hn0]; linarith [hige']
      have hbnd := abs_contHeat_two_mul_sub (δ := (0 : ℝ)) (δ' := (0 : ℝ)) (d := dn n)
        (d' := dstar) (θ := (i : ℝ) / n) (a0 := 2 * θ0) (by positivity)
        (by linarith [hthetage]) (by linarith [hthetage])
      simpa [Cθ0, hCθ0def] using hbnd
    have hsum_le : |∑ i ∈ Finset.Ico (kfun n) (M n),
        (contHeat (2 * ((i : ℝ) / n)) 0 (dn n) - contHeat (2 * ((i : ℝ) / n)) 0 dstar)|
        ≤ ∑ i ∈ Finset.Ico (kfun n) (M n), Cθ0 n :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hsum_le
    have hcard_le : ((M n - kfun n : ℕ) : ℝ) ≤ (M n : ℝ) := by
      exact_mod_cast Nat.sub_le (M n) (kfun n)
    have hCθ0nn : (0 : ℝ) ≤ Cθ0 n := by positivity
    calc (n : ℝ)⁻¹ * |∑ i ∈ Finset.Ico (kfun n) (M n),
          (contHeat (2 * ((i : ℝ) / n)) 0 (dn n) - contHeat (2 * ((i : ℝ) / n)) 0 dstar)|
        ≤ (n : ℝ)⁻¹ * (((M n - kfun n : ℕ) : ℝ) * Cθ0 n) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ ≤ (n : ℝ)⁻¹ * ((M n : ℝ) * Cθ0 n) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard_le hCθ0nn) (by positivity)
      _ = (M n : ℝ) / n * Cθ0 n := by ring
      _ ≤ b * Cθ0 n := mul_le_mul_of_nonneg_right hn3.le hCθ0nn
      _ < ε / 2 := hn4
  have hksplit' : Finset.range (M n) = Finset.range (kfun n) ∪ Finset.Ico (kfun n) (M n) := by
    rw [Finset.range_eq_Ico (kfun n)]
    exact hksplit
  have hdisj : Disjoint (Finset.range (kfun n)) (Finset.Ico (kfun n) (M n)) := by
    rw [Finset.range_eq_Ico]
    exact Finset.Ico_disjoint_Ico_consecutive 0 (kfun n) (M n)
  have hfull : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (M n),
      (contHeat (2 * ((i : ℝ) / n)) 0 (dn n) - contHeat (2 * ((i : ℝ) / n)) 0 dstar)
      = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (kfun n),
          (contHeat (2 * ((i : ℝ) / n)) 0 (dn n) - contHeat (2 * ((i : ℝ) / n)) 0 dstar) +
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.Ico (kfun n) (M n),
          (contHeat (2 * ((i : ℝ) / n)) 0 (dn n) - contHeat (2 * ((i : ℝ) / n)) 0 dstar) := by
    rw [← mul_add, ← Finset.sum_union hdisj, ← hksplit']
  rw [Real.dist_eq, sub_zero]
  have hgoaleq : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (M n), contHeat (2 * ((i : ℝ) / n)) 0 (dn n) -
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (M n), contHeat (2 * ((i : ℝ) / n)) 0 dstar
      = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (M n),
          (contHeat (2 * ((i : ℝ) / n)) 0 (dn n) - contHeat (2 * ((i : ℝ) / n)) 0 dstar) := by
    rw [Finset.sum_sub_distrib, mul_sub]
  rw [hgoaleq, hfull]
  calc |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range (kfun n),
        (contHeat (2 * ((i : ℝ) / n)) 0 (dn n) - contHeat (2 * ((i : ℝ) / n)) 0 dstar) +
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.Ico (kfun n) (M n),
        (contHeat (2 * ((i : ℝ) / n)) 0 (dn n) - contHeat (2 * ((i : ℝ) / n)) 0 dstar)|
      ≤ |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range (kfun n),
            (contHeat (2 * ((i : ℝ) / n)) 0 (dn n) - contHeat (2 * ((i : ℝ) / n)) 0 dstar)| +
        |(n : ℝ)⁻¹ * ∑ i ∈ Finset.Ico (kfun n) (M n),
            (contHeat (2 * ((i : ℝ) / n)) 0 (dn n) - contHeat (2 * ((i : ℝ) / n)) 0 dstar)| :=
        abs_add_le _ _
    _ < ε / 2 + ε / 2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)⁻¹)]
        exact add_lt_add hsmall hlarge
    _ = ε := by ring

/-- `n^{-1/2}` is `(√n)⁻¹`. -/
theorem rpow_neg_half_eq_inv_sqrt (n : ℕ) : (n : ℝ) ^ (-(1 : ℝ) / 2) = (Real.sqrt n)⁻¹ := by
  rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) from by ring, Real.rpow_neg (Nat.cast_nonneg n),
    ← Real.sqrt_eq_rpow]

/-- **The local-CLT term, matched to the covariance-sum summand.**  For `n ≥ 1`, the
`n⁻¹`-weighted heat kernel at the drifting delay/displacement pair coming from `D n, K n`
equals the `(√n)⁻¹`-weighted Gaussian profile at the exact integers `2i + D n`,
`2K n - D n` that `abs_binomLaw_sub_heatApprox_le` compares against. -/
theorem riemann_term_orientedCovSum {n : ℕ} (hn : 1 ≤ n) (D : ℕ) (K : ℤ) (i : ℕ) :
    (n : ℝ)⁻¹ * contHeat (2 * ((i : ℝ) / n) + (D : ℝ) / n) 0
        ((2 * (K : ℝ) - D) / (2 * Real.sqrt n))
      = (Real.sqrt n)⁻¹ * heatApprox (((2 * i + D : ℕ) : ℝ)) (2 * (K : ℝ) - ((D : ℤ) : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hrw1 : (2 : ℝ) * ((i : ℝ) / n) = 2 * (i : ℝ) / n := by ring
  have hstep := riemann_term n hn ((D : ℝ) / n) ((2 * (K : ℝ) - D) / (2 * Real.sqrt n)) (by positivity) i
  rw [hrw1, hstep]
  have hnδ : (n : ℝ) * ((D : ℝ) / n) = (D : ℝ) := by field_simp
  have hdd : (2 : ℝ) * Real.sqrt n * ((2 * (K : ℝ) - D) / (2 * Real.sqrt n)) = 2 * (K : ℝ) - D := by
    field_simp
  rw [hnδ, hdd]
  congr 2
  push_cast; ring

/-- **The covariance sum converges to the heat-kernel integral, in the case of two points
at different rescaled times** (`D n / n → δstar > 0`): the same limit as
`tendsto_riemann_sum_Ioo_param_pos`, but for the actual discrete binomial covariance sum
`orientedCovSum`, transported through the binomial local central limit theorem
(`Parking.External.BinomialLocalCLT`). -/
theorem tendsto_orientedCovSum_of_pos (hBinomial : External.BinomialLocalCLT)
    {δstar dstar a b : ℝ} (hδstar : 0 < δstar) (ha : 0 ≤ a) (hab : a < b)
    {D M : ℕ → ℕ} {K : ℕ → ℤ}
    (hδn : Tendsto (fun n => (D n : ℝ) / n) atTop (𝓝 δstar))
    (hMn : Tendsto (fun n => (M n : ℝ) / n) atTop (𝓝 a))
    (hdn : Tendsto (fun n => (2 * (K n : ℝ) - D n) / (2 * Real.sqrt n)) atTop (𝓝 dstar)) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 2) * orientedCovSum (D n) (M n) (K n))
      atTop (𝓝 (∫ θ in (0 : ℝ)..a, contHeat (2 * θ + δstar) 0 dstar)) := by
  obtain ⟨C, hCpos, hCbound⟩ := hBinomial
  have htarget := tendsto_riemann_sum_Ioo_param_pos hδstar ha hab hδn hdn hMn
  suffices hdiff : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 2) *
      orientedCovSum (D n) (M n) (K n) -
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (M n),
        contHeat (2 * ((i : ℝ) / n) + (D n : ℝ) / n) 0
          ((2 * (K n : ℝ) - D n) / (2 * Real.sqrt n)))
      atTop (𝓝 0) by
    have hsum := hdiff.add htarget
    simpa using hsum
  have hevD : ∀ᶠ n : ℕ in atTop, 1 ≤ D n := by
    have h2 : ∀ᶠ n : ℕ in atTop, δstar / 2 < (D n : ℝ) / n :=
      hδn.eventually (eventually_gt_nhds (by linarith))
    have h3 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) / δstar ≤ n :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2 / δstar))
    filter_upwards [h2, h3, eventually_ge_atTop 1] with n hn2 hn3 hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hlt : δstar / 2 * n < (D n : ℝ) := (lt_div_iff₀ hn0).mp hn2
    have hn3' : (2 : ℝ) ≤ n * δstar := (div_le_iff₀ hδstar).mp hn3
    have : (1 : ℝ) ≤ (D n : ℝ) := by nlinarith
    exact_mod_cast this
  have hbnd : ∀ᶠ n : ℕ in atTop, ‖(n : ℝ) ^ (-(1 : ℝ) / 2) * orientedCovSum (D n) (M n) (K n) -
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (M n),
        contHeat (2 * ((i : ℝ) / n) + (D n : ℝ) / n) 0
          ((2 * (K n : ℝ) - D n) / (2 * Real.sqrt n))‖ ≤ (Real.sqrt n)⁻¹ * (C * 3) := by
    filter_upwards [hevD, eventually_ge_atTop 1] with n hnD hn1
    have heq1 : (n : ℝ) ^ (-(1 : ℝ) / 2) * orientedCovSum (D n) (M n) (K n)
        = (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range (M n),
            binomLaw (2 * i + D n) ((i : ℤ) + K n) := by
      rw [rpow_neg_half_eq_inv_sqrt]
      rfl
    have heq2 : (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (M n),
        contHeat (2 * ((i : ℝ) / n) + (D n : ℝ) / n) 0
          ((2 * (K n : ℝ) - D n) / (2 * Real.sqrt n))
        = (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range (M n),
            heatApprox (((2 * i + D n : ℕ) : ℝ)) (2 * (K n : ℝ) - ((D n : ℤ) : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => riemann_term_orientedCovSum hn1 (D n) (K n) i
    rw [heq1, heq2, ← mul_sub, ← Finset.sum_sub_distrib]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.sqrt n)⁻¹)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hle : ∑ i ∈ Finset.range (M n),
        (C / ((((2 * i + D n : ℕ) : ℝ)) * Real.sqrt (((2 * i + D n : ℕ) : ℝ))))
        ≤ C * 3 := by
      have h3C : ∀ i ∈ Finset.range (M n), C / ((((2 * i + D n : ℕ) : ℝ)) *
          Real.sqrt (((2 * i + D n : ℕ) : ℝ))) =
          C * (((2 * i + D n : ℕ) : ℝ) * Real.sqrt (((2 * i + D n : ℕ) : ℝ)))⁻¹ := by
        intro i _; rw [div_eq_mul_inv]
      rw [Finset.sum_congr rfl h3C, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_range_two_mul_add_inv_le (D n) (M n)) hCpos.le
    calc |∑ i ∈ Finset.range (M n), (binomLaw (2 * i + D n) ((i : ℤ) + K n) -
          heatApprox (((2 * i + D n : ℕ) : ℝ)) (2 * (K n : ℝ) - ((D n : ℤ) : ℝ)))|
        ≤ ∑ i ∈ Finset.range (M n), |binomLaw (2 * i + D n) ((i : ℤ) + K n) -
            heatApprox (((2 * i + D n : ℕ) : ℝ)) (2 * (K n : ℝ) - ((D n : ℤ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (M n),
            C / ((((2 * i + D n : ℕ) : ℝ)) * Real.sqrt (((2 * i + D n : ℕ) : ℝ))) :=
          Finset.sum_le_sum fun i _ =>
            abs_binomLaw_sub_heatApprox_le hCbound (D n) (K n) i (by omega)
      _ ≤ C * 3 := hle
  have hsqrt_inv0 : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ * (C * 3)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1
    simpa using h2.mul_const (C * 3)
  exact squeeze_zero_norm' hbnd hsqrt_inv0

/-- **The local-CLT bridge, on an arbitrary finite index set.**  Bounds the difference
between a finite piece of the discrete covariance sum and its heat-kernel Riemann sum,
using the binomial local central limit theorem, uniformly over any finite set of indices
`S` clear of the singular combination `i = 0, D = 0` (`hS`).  Used both for `S = range (M
n)` (when `D` is bounded away from `0`, as in `tendsto_orientedCovSum_of_pos`) and for `S =
Ico 1 (M n)` (which avoids `i = 0` even when `D = 0` identically). -/
theorem abs_sum_binomLaw_sub_contHeat_le {C : ℝ} (hCpos : 0 < C)
    (hCbound : ∀ m : ℕ, 1 ≤ m → ∀ j : ℤ, (j - (m : ℤ)) % 2 = 0 →
      |Real.sqrt (m : ℝ) * binomLaw m ((j + (m : ℤ)) / 2) -
        2 * (Real.exp (-((j : ℝ) / Real.sqrt (m : ℝ)) ^ 2 / 2) /
          Real.sqrt (2 * Real.pi))| ≤ C / (m : ℝ))
    {n : ℕ} (hn : 1 ≤ n) (D : ℕ) (K : ℤ) (S : Finset ℕ) (hS : ∀ i ∈ S, 1 ≤ 2 * i + D) :
    ‖(n : ℝ) ^ (-(1 : ℝ) / 2) * ∑ i ∈ S, binomLaw (2 * i + D) ((i : ℤ) + K) -
        (n : ℝ)⁻¹ * ∑ i ∈ S, contHeat (2 * ((i : ℝ) / n) + (D : ℝ) / n) 0
          ((2 * (K : ℝ) - D) / (2 * Real.sqrt n))‖ ≤ (Real.sqrt n)⁻¹ * (C * 3) := by
  have heq1 : (n : ℝ) ^ (-(1 : ℝ) / 2) * ∑ i ∈ S, binomLaw (2 * i + D) ((i : ℤ) + K)
      = (Real.sqrt n)⁻¹ * ∑ i ∈ S, binomLaw (2 * i + D) ((i : ℤ) + K) := by
    rw [rpow_neg_half_eq_inv_sqrt]
  have heq2 : (n : ℝ)⁻¹ * ∑ i ∈ S,
      contHeat (2 * ((i : ℝ) / n) + (D : ℝ) / n) 0 ((2 * (K : ℝ) - D) / (2 * Real.sqrt n))
      = (Real.sqrt n)⁻¹ * ∑ i ∈ S,
          heatApprox (((2 * i + D : ℕ) : ℝ)) (2 * (K : ℝ) - ((D : ℤ) : ℝ)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => riemann_term_orientedCovSum hn D K i
  rw [heq1, heq2, ← mul_sub, ← Finset.sum_sub_distrib]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.sqrt n)⁻¹)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hle : ∑ i ∈ S,
      (C / ((((2 * i + D : ℕ) : ℝ)) * Real.sqrt (((2 * i + D : ℕ) : ℝ)))) ≤ C * 3 := by
    have h3C : ∀ i ∈ S, C / ((((2 * i + D : ℕ) : ℝ)) * Real.sqrt (((2 * i + D : ℕ) : ℝ))) =
        C * (((2 * i + D : ℕ) : ℝ) * Real.sqrt (((2 * i + D : ℕ) : ℝ)))⁻¹ := by
      intro i _; rw [div_eq_mul_inv]
    rw [Finset.sum_congr rfl h3C, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hCpos.le
    calc ∑ i ∈ S, (((2 * i + D : ℕ) : ℝ) * Real.sqrt (((2 * i + D : ℕ) : ℝ)))⁻¹
        ≤ ∑ i ∈ Finset.range (S.sup id + 1),
            (((2 * i + D : ℕ) : ℝ) * Real.sqrt (((2 * i + D : ℕ) : ℝ)))⁻¹ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
          · intro i _ _; positivity
      _ ≤ 3 := sum_range_two_mul_add_inv_le D (S.sup id + 1)
  calc |∑ i ∈ S, (binomLaw (2 * i + D) ((i : ℤ) + K) -
        heatApprox (((2 * i + D : ℕ) : ℝ)) (2 * (K : ℝ) - ((D : ℤ) : ℝ)))|
      ≤ ∑ i ∈ S, |binomLaw (2 * i + D) ((i : ℤ) + K) -
          heatApprox (((2 * i + D : ℕ) : ℝ)) (2 * (K : ℝ) - ((D : ℤ) : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, C / ((((2 * i + D : ℕ) : ℝ)) * Real.sqrt (((2 * i + D : ℕ) : ℝ))) :=
        Finset.sum_le_sum fun i hi => abs_binomLaw_sub_heatApprox_le hCbound D K i (hS i hi)
    _ ≤ C * 3 := hle

/-- **Splitting off the zero index.**  A sum over `range m` (`m ≥ 1`) is its value at `0`
plus the sum over `Ico 1 m`. -/
theorem sum_range_eq_zero_add_sum_Ico_one (f : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ∑ i ∈ Finset.range m, f i = f 0 + ∑ i ∈ Finset.Ico 1 m, f i := by
  have h := Finset.sum_Ico_consecutive f (Nat.zero_le 1) hm
  rw [Finset.range_eq_Ico, ← h]
  congr 1
  simp

/-- **The covariance sum converges to the heat-kernel integral, in the case of two points
at the SAME rescaled time** (`D = 0` identically): covers both the diagonal case (`K n = 0`
identically, `dstar = 0`, via `tendsto_riemann_sum_singular_Ioo`) and the same-time,
different-space case (`dstar ≠ 0`, via `tendsto_riemann_sum_Ioo_same_time`). -/
theorem tendsto_orientedCovSum_of_eq (hBinomial : External.BinomialLocalCLT)
    {dstar a b : ℝ} (ha : 0 < a) (hab : a < b) {M : ℕ → ℕ} {K : ℕ → ℤ}
    (hcase : (∀ n, K n = 0) ∨ dstar ≠ 0)
    (hMn : Tendsto (fun n => (M n : ℝ) / n) atTop (𝓝 a))
    (hdn : Tendsto (fun n => (K n : ℝ) / Real.sqrt n) atTop (𝓝 dstar)) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 2) * orientedCovSum 0 (M n) (K n))
      atTop (𝓝 (∫ θ in (0 : ℝ)..a, contHeat (2 * θ) 0 dstar)) := by
  obtain ⟨C, hCpos, hCbound⟩ := hBinomial
  have hMev : ∀ᶠ n : ℕ in atTop, 1 ≤ M n := by
    have h2 : ∀ᶠ n : ℕ in atTop, a / 2 < (M n : ℝ) / n :=
      hMn.eventually (eventually_gt_nhds (by linarith))
    have h3 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) / a ≤ n :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2 / a))
    filter_upwards [h2, h3, eventually_ge_atTop 1] with n hn2 hn3 hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hlt : a / 2 * n < (M n : ℝ) := (lt_div_iff₀ hn0).mp hn2
    have hn3' : (2 : ℝ) ≤ n * a := (div_le_iff₀ ha).mp hn3
    have : (1 : ℝ) ≤ (M n : ℝ) := by nlinarith
    exact_mod_cast this
  have hOrientedEq : ∀ n : ℕ, 1 ≤ M n → orientedCovSum 0 (M n) (K n)
      = binomLaw 0 (K n) + ∑ i ∈ Finset.Ico 1 (M n), binomLaw (2 * i) ((i : ℤ) + K n) := by
    intro n hn
    show ∑ i ∈ Finset.range (M n), binomLaw (2 * i + 0) ((i : ℤ) + K n) = _
    simp only [add_zero]
    have h := sum_range_eq_zero_add_sum_Ico_one (fun i => binomLaw (2 * i) ((i : ℤ) + K n)) hn
    simpa using h
  rcases hcase with hK0 | hdstarNe
  · -- diagonal: K n = 0 identically, forces dstar = 0
    have hdstar0 : dstar = 0 := by
      have heq : (fun n : ℕ => (K n : ℝ) / Real.sqrt n) = fun _ : ℕ => (0 : ℝ) := by
        funext n; rw [hK0 n]; simp
      rw [heq] at hdn
      exact tendsto_nhds_unique hdn tendsto_const_nhds
    subst hdstar0
    have htarget := tendsto_riemann_sum_singular_Ioo ha hMn
    suffices hdiff : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 2) *
        orientedCovSum 0 (M n) (K n) -
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.Ico 1 (M n), contHeat (2 * ((i : ℝ) / n)) 0 0)
        atTop (𝓝 0) by
      have hsum := hdiff.add htarget
      simpa using hsum
    have hn_half0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 2)) atTop (𝓝 0) := by
      have heq : (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 2)) = fun n : ℕ => (Real.sqrt n)⁻¹ :=
        funext rpow_neg_half_eq_inv_sqrt
      rw [heq]
      exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hb1 : binomLaw 0 (0 : ℤ) = 1 := by unfold binomLaw; norm_num
    have hbnd2 : ∀ᶠ n : ℕ in atTop, ‖(n : ℝ) ^ (-(1 : ℝ) / 2) *
        ∑ i ∈ Finset.Ico 1 (M n), binomLaw (2 * i) ((i : ℤ) + K n) -
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.Ico 1 (M n), contHeat (2 * ((i : ℝ) / n)) 0 0‖
        ≤ (Real.sqrt n)⁻¹ * (C * 3) := by
      filter_upwards [eventually_ge_atTop 1] with n hn1
      rw [hK0 n]
      have hS : ∀ i ∈ Finset.Ico 1 (M n), 1 ≤ 2 * i + 0 := by
        intro i hi; obtain ⟨hi1, -⟩ := Finset.mem_Ico.mp hi; omega
      have hstep := abs_sum_binomLaw_sub_contHeat_le hCpos hCbound (n := n) hn1 0 (0 : ℤ)
        (Finset.Ico 1 (M n)) hS
      simpa using hstep
    have hpart2 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 2) *
        ∑ i ∈ Finset.Ico 1 (M n), binomLaw (2 * i) ((i : ℤ) + K n) -
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.Ico 1 (M n), contHeat (2 * ((i : ℝ) / n)) 0 0)
        atTop (𝓝 0) := by
      have hsqrt_inv0 : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ * (C * 3)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
          Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
        have h2 : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp h1
        simpa using h2.mul_const (C * 3)
      exact squeeze_zero_norm' hbnd2 hsqrt_inv0
    have hp1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 2) * (1 : ℝ)) atTop (𝓝 0) := by
      simpa using hn_half0
    have hcombine := hp1.add hpart2
    simp only [zero_add] at hcombine
    refine hcombine.congr' ?_
    filter_upwards [hMev] with n hn
    rw [hOrientedEq n hn, hK0 n, hb1]
    ring
  · -- same time, different space: dstar ≠ 0
    have htarget := tendsto_riemann_sum_Ioo_same_time hdstarNe ha.le hab hdn hMn
    have hn_half0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 2)) atTop (𝓝 0) := by
      have heq : (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 2)) = fun n : ℕ => (Real.sqrt n)⁻¹ :=
        funext rpow_neg_half_eq_inv_sqrt
      rw [heq]
      exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hcontEq : ∀ n : ℕ, 1 ≤ M n → (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (M n),
        contHeat (2 * ((i : ℝ) / n)) 0 (K n / Real.sqrt n)
        = (n : ℝ)⁻¹ * contHeat 0 0 (K n / Real.sqrt n) +
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.Ico 1 (M n), contHeat (2 * ((i : ℝ) / n)) 0 (K n / Real.sqrt n) := by
      intro n hn
      rw [← mul_add]
      congr 1
      have h0 : (2 : ℝ) * (((0 : ℕ) : ℝ) / n) = 0 := by simp
      have hsplit := sum_range_eq_zero_add_sum_Ico_one
        (fun i : ℕ => contHeat (2 * ((i : ℝ) / n)) 0 (K n / Real.sqrt n)) hn
      rw [hsplit, h0]
    have hpart1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 2) * binomLaw 0 (K n) -
        (n : ℝ)⁻¹ * contHeat 0 0 (K n / Real.sqrt n)) atTop (𝓝 0) := by
      have hzero : ∀ n : ℕ, (n : ℝ)⁻¹ * contHeat 0 0 (K n / Real.sqrt n) = 0 := by
        intro n; rw [contHeat_of_nonpos le_rfl 0 _, mul_zero]
      have heqf : (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 2) * binomLaw 0 (K n) -
          (n : ℝ)⁻¹ * contHeat 0 0 (K n / Real.sqrt n))
          = fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 2) * binomLaw 0 (K n) := by
        funext n; rw [hzero n, sub_zero]
      rw [heqf]
      have hbnd1 : ∀ n : ℕ, ‖(n : ℝ) ^ (-(1 : ℝ) / 2) * binomLaw 0 (K n)‖ ≤
          ‖(n : ℝ) ^ (-(1 : ℝ) / 2)‖ := by
        intro n
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        have h1 : |binomLaw 0 (K n)| ≤ 1 := by
          rw [abs_of_nonneg (binomLaw_nonneg 0 (K n))]
          exact binomLaw_le_one 0 (K n)
        calc |(n : ℝ) ^ (-(1 : ℝ) / 2)| * |binomLaw 0 (K n)|
            ≤ |(n : ℝ) ^ (-(1 : ℝ) / 2)| * 1 :=
              mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ = |(n : ℝ) ^ (-(1 : ℝ) / 2)| := mul_one _
      have hn_half0' : Tendsto (fun n : ℕ => ‖(n : ℝ) ^ (-(1 : ℝ) / 2)‖) atTop (𝓝 0) := by
        simpa using hn_half0.norm
      exact squeeze_zero_norm hbnd1 hn_half0'
    have hpart2 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 2) *
        ∑ i ∈ Finset.Ico 1 (M n), binomLaw (2 * i) ((i : ℤ) + K n) -
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.Ico 1 (M n),
          contHeat (2 * ((i : ℝ) / n)) 0 (K n / Real.sqrt n)) atTop (𝓝 0) := by
      have heqd : ∀ n : ℕ, (2 * (K n : ℝ) - 0) / (2 * Real.sqrt n) = K n / Real.sqrt n := by
        intro n; rw [sub_zero]; ring
      have hbnd2 : ∀ᶠ n : ℕ in atTop, ‖(n : ℝ) ^ (-(1 : ℝ) / 2) *
          ∑ i ∈ Finset.Ico 1 (M n), binomLaw (2 * i) ((i : ℤ) + K n) -
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.Ico 1 (M n),
            contHeat (2 * ((i : ℝ) / n)) 0 (K n / Real.sqrt n)‖ ≤ (Real.sqrt n)⁻¹ * (C * 3) := by
        filter_upwards [eventually_ge_atTop 1] with n hn1
        have hS : ∀ i ∈ Finset.Ico 1 (M n), 1 ≤ 2 * i + 0 := by
          intro i hi; obtain ⟨hi1, -⟩ := Finset.mem_Ico.mp hi; omega
        have hstep := abs_sum_binomLaw_sub_contHeat_le hCpos hCbound (n := n) hn1 0 (K n)
          (Finset.Ico 1 (M n)) hS
        simp only [Nat.cast_zero, zero_div, add_zero] at hstep
        rw [heqd n] at hstep
        exact hstep
      have hsqrt_inv0 : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ * (C * 3)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
          Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
        have h2 : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp h1
        simpa using h2.mul_const (C * 3)
      exact squeeze_zero_norm' hbnd2 hsqrt_inv0
    suffices hdiff : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 2) *
        orientedCovSum 0 (M n) (K n) -
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range (M n), contHeat (2 * ((i : ℝ) / n)) 0 (K n / Real.sqrt n))
        atTop (𝓝 0) by
      have hsum := hdiff.add htarget
      simpa using hsum
    have hcombine := hpart1.add hpart2
    simp only [add_zero] at hcombine
    refine hcombine.congr' ?_
    filter_upwards [hMev] with n hn
    rw [hOrientedEq n hn, hcontEq n hn]
    ring

/-- **The covariance of the grid reward field, at two grid points at different rescaled
times** (`(m' n).toNat - (m n).toNat` grows linearly, `/n → δstar > 0`): the discrete
covariance converges to `Var(η) ·` the heat-kernel integral, via `integral_
orientedGridReward_mul`, `greenCross_layerPoint_sub_of_le` and `tendsto_orientedCovSum_of_
pos`. -/
theorem tendsto_integral_orientedGridReward_mul_of_pos (ν : Measure ℤ) (hν : CriticalLaw ν)
    (hBinomial : External.BinomialLocalCLT)
    {δstar dstar a b : ℝ} (hδstar : 0 < δstar) (ha : 0 ≤ a) (hab : a < b)
    {m m' j j' : ℕ → ℤ} {N : ℕ → ℕ}
    (hmm' : ∀ n, (m n).toNat ≤ (m' n).toNat) (hm'N : ∀ n, (m' n).toNat ≤ N n)
    (hδn : Tendsto (fun n => (((m' n).toNat - (m n).toNat : ℕ) : ℝ) / n) atTop (𝓝 δstar))
    (hMn : Tendsto (fun n => ((N n - (m' n).toNat : ℕ) : ℝ) / n) atTop (𝓝 a))
    (hdn : Tendsto (fun n => (2 * ((j' n - j n : ℤ) : ℝ) - ((m' n).toNat - (m n).toNat : ℕ)) /
        (2 * Real.sqrt n)) atTop (𝓝 dstar)) :
    Tendsto (fun n : ℕ => ∫ η : Site 2 → ℝ, orientedGridReward n (N n) η (m n) (j n) *
        orientedGridReward n (N n) η (m' n) (j' n) ∂(iidLaw 2 (realLaw ν))) atTop
      (𝓝 ((∫ x : ℝ, x ^ 2 ∂(realLaw ν)) * ∫ θ in (0 : ℝ)..a, contHeat (2 * θ + δstar) 0 dstar)) := by
  have hpt : ∀ n : ℕ, (∫ η : Site 2 → ℝ, orientedGridReward n (N n) η (m n) (j n) *
        orientedGridReward n (N n) η (m' n) (j' n) ∂(iidLaw 2 (realLaw ν)))
      = (n : ℝ) ^ (-(1 : ℝ) / 2) * ((∫ x : ℝ, x ^ 2 ∂(realLaw ν)) *
          orientedCovSum ((m' n).toNat - (m n).toNat) (N n - (m' n).toNat) (j' n - j n)) := by
    intro n
    rw [integral_orientedGridReward_mul ν hν n (N n) (m n) (m' n) (j n) (j' n),
      greenCross_layerPoint_sub_of_le (hmm' n) (hm'N n) (j n) (j' n)]
  have hcov := tendsto_orientedCovSum_of_pos hBinomial hδstar ha hab hδn hMn hdn
  have hscaled := hcov.const_mul (∫ x : ℝ, x ^ 2 ∂(realLaw ν))
  have heqf : (fun n : ℕ => ∫ η : Site 2 → ℝ, orientedGridReward n (N n) η (m n) (j n) *
        orientedGridReward n (N n) η (m' n) (j' n) ∂(iidLaw 2 (realLaw ν)))
      = fun n : ℕ => (∫ x : ℝ, x ^ 2 ∂(realLaw ν)) *
          ((n : ℝ) ^ (-(1 : ℝ) / 2) * orientedCovSum ((m' n).toNat - (m n).toNat)
              (N n - (m' n).toNat) (j' n - j n)) := by
    funext n; rw [hpt n]; ring
  rw [heqf]
  exact hscaled

/-- **The covariance of the grid reward field, at two grid points at the SAME rescaled
time** (`(m' n).toNat = (m n).toNat`, i.e. `m n = m' n`): covers both the diagonal
(`j n = j' n` identically) and the same-time-different-space (`dstar ≠ 0`) cases, via
`tendsto_orientedCovSum_of_eq`. -/
theorem tendsto_integral_orientedGridReward_mul_of_eq (ν : Measure ℤ) (hν : CriticalLaw ν)
    (hBinomial : External.BinomialLocalCLT)
    {dstar a b : ℝ} (ha : 0 < a) (hab : a < b)
    {m j j' : ℕ → ℤ} {N : ℕ → ℕ} (hmN : ∀ n, (m n).toNat ≤ N n)
    (hcase : (∀ n, j n = j' n) ∨ dstar ≠ 0)
    (hMn : Tendsto (fun n => ((N n - (m n).toNat : ℕ) : ℝ) / n) atTop (𝓝 a))
    (hdn : Tendsto (fun n => ((j' n - j n : ℤ) : ℝ) / Real.sqrt n) atTop (𝓝 dstar)) :
    Tendsto (fun n : ℕ => ∫ η : Site 2 → ℝ, orientedGridReward n (N n) η (m n) (j n) *
        orientedGridReward n (N n) η (m n) (j' n) ∂(iidLaw 2 (realLaw ν))) atTop
      (𝓝 ((∫ x : ℝ, x ^ 2 ∂(realLaw ν)) * ∫ θ in (0 : ℝ)..a, contHeat (2 * θ) 0 dstar)) := by
  have hpt : ∀ n : ℕ, (∫ η : Site 2 → ℝ, orientedGridReward n (N n) η (m n) (j n) *
        orientedGridReward n (N n) η (m n) (j' n) ∂(iidLaw 2 (realLaw ν)))
      = (n : ℝ) ^ (-(1 : ℝ) / 2) * ((∫ x : ℝ, x ^ 2 ∂(realLaw ν)) *
          orientedCovSum 0 (N n - (m n).toNat) (j' n - j n)) := by
    intro n
    rw [integral_orientedGridReward_mul ν hν n (N n) (m n) (m n) (j n) (j' n),
      greenCross_layerPoint_sub_of_le (le_refl (m n).toNat) (hmN n) (j n) (j' n)]
    norm_num
  have hcaseK : (∀ n, j' n - j n = 0) ∨ dstar ≠ 0 := by
    rcases hcase with h | h
    · left; intro n; rw [h n]; ring
    · right; exact h
  have hcov := tendsto_orientedCovSum_of_eq hBinomial ha hab hcaseK hMn hdn
  have hscaled := hcov.const_mul (∫ x : ℝ, x ^ 2 ∂(realLaw ν))
  have heqf : (fun n : ℕ => ∫ η : Site 2 → ℝ, orientedGridReward n (N n) η (m n) (j n) *
        orientedGridReward n (N n) η (m n) (j' n) ∂(iidLaw 2 (realLaw ν)))
      = fun n : ℕ => (∫ x : ℝ, x ^ 2 ∂(realLaw ν)) *
          ((n : ℝ) ^ (-(1 : ℝ) / 2) * orientedCovSum 0 (N n - (m n).toNat) (j' n - j n)) := by
    funext n; rw [hpt n]; ring
  rw [heqf]
  exact hscaled

/-- **The floor error of any real sequence is bounded, uniformly, and vanishes after
dividing by any sequence tending to infinity.** -/
theorem tendsto_int_floor_sub_div_atTop {g h : ℕ → ℝ} (hh : Tendsto h atTop atTop) :
    Tendsto (fun n : ℕ => (((⌊g n⌋ : ℤ) : ℝ) - g n) / h n) atTop (𝓝 0) := by
  have hub : ∀ n : ℕ, (((⌊g n⌋ : ℤ) : ℝ) - g n) ≤ 0 := fun n => sub_nonpos.mpr (Int.floor_le (g n))
  have hlb : ∀ n : ℕ, (-1 : ℝ) ≤ (((⌊g n⌋ : ℤ) : ℝ) - g n) := fun n => by
    have := Int.sub_one_lt_floor (g n); linarith
  have hinv : Tendsto (fun n : ℕ => (h n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hh
  have h1 : Tendsto (fun n : ℕ => (-1 : ℝ) / h n) atTop (𝓝 0) := by
    have hneg : Tendsto (fun n : ℕ => -(h n)⁻¹) atTop (𝓝 (-(0 : ℝ))) := hinv.neg
    rw [neg_zero] at hneg
    refine hneg.congr' (Filter.Eventually.of_forall fun n => ?_)
    show -(h n)⁻¹ = -1 / h n
    rw [div_eq_mul_inv, neg_one_mul]
  have h2 : Tendsto (fun n : ℕ => (0 : ℝ) / h n) atTop (𝓝 0) := by
    have heq : (fun n : ℕ => (0 : ℝ) / h n) = fun _ => (0 : ℝ) := by funext n; rw [zero_div]
    rw [heq]
    exact tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2 ?_ ?_
  · filter_upwards [hh.eventually_gt_atTop 0] with n hn
    exact (div_le_div_iff_of_pos_right hn).mpr (hlb n)
  · filter_upwards [hh.eventually_gt_atTop 0] with n hn
    exact (div_le_div_iff_of_pos_right hn).mpr (hub n)

/-- **The floor of `n·x`, rescaled by `n`, converges to `x`**, for any sign of `x`. -/
theorem tendsto_int_floor_mul_div (x : ℝ) :
    Tendsto (fun n : ℕ => ((⌊(n : ℝ) * x⌋ : ℤ) : ℝ) / n) atTop (𝓝 x) := by
  have herr := tendsto_int_floor_sub_div_atTop (g := fun n : ℕ => (n : ℝ) * x)
    tendsto_natCast_atTop_atTop
  have hsum := herr.add (tendsto_const_nhds (x := x))
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  show (((⌊(n : ℝ) * x⌋ : ℤ) : ℝ) - (n : ℝ) * x) / n + x = ((⌊(n : ℝ) * x⌋ : ℤ) : ℝ) / n
  field_simp
  ring



/-- **Difference of two floors, rescaled**: if the arguments' difference, rescaled, tends to
`L`, so does the difference of their floors, rescaled by the same (eventually infinite)
sequence. -/
theorem tendsto_int_floor_sub_div {g k h : ℕ → ℝ} {L : ℝ} (hh : Tendsto h atTop atTop)
    (hgk : Tendsto (fun n => (g n - k n) / h n) atTop (𝓝 L)) :
    Tendsto (fun n => (((⌊g n⌋ : ℤ) : ℝ) - ((⌊k n⌋ : ℤ) : ℝ)) / h n) atTop (𝓝 L) := by
  have e1 := tendsto_int_floor_sub_div_atTop (g := g) hh
  have e2 := tendsto_int_floor_sub_div_atTop (g := k) hh
  have hsum := (e1.sub e2).add hgk
  rw [sub_zero, zero_add] at hsum
  refine hsum.congr' (Filter.Eventually.of_forall fun n => ?_)
  show (((⌊g n⌋ : ℤ) : ℝ) - g n) / h n - (((⌊k n⌋ : ℤ) : ℝ) - k n) / h n + (g n - k n) / h n
      = (((⌊g n⌋ : ℤ) : ℝ) - ((⌊k n⌋ : ℤ) : ℝ)) / h n
  ring

/-- **The `toNat` gap of two nonnegative, ordered integers, cast to `ℝ`, is their
difference.** -/
theorem cast_toNat_sub_toNat {m m' : ℤ} (h0 : 0 ≤ m) (hmm' : m ≤ m') :
    ((m'.toNat - m.toNat : ℕ) : ℝ) = (m' : ℝ) - (m : ℝ) := by
  have h0' : 0 ≤ m' := h0.trans hmm'
  have hsub : m'.toNat - m.toNat = (m' - m).toNat := by omega
  rw [hsub]
  have hnn : (0:ℤ) ≤ m' - m := by omega
  have hcast : ((m' - m).toNat : ℤ) = m' - m := Int.toNat_of_nonneg hnn
  have hcastR : (((m' - m).toNat : ℤ) : ℝ) = ((m' - m : ℤ) : ℝ) := by rw [hcast]
  push_cast at hcastR ⊢
  linarith



/-- **The overlap kernel as an interval integral, for two box points with the earlier
point first.** -/
theorem contOverlap_eq_intervalIntegral_of_le {T : ℝ} {u u' : Fin 2 → ℝ}
    (hle : u 0 ≤ u' 0) (hu'T : u' 0 ≤ T) :
    contOverlap T u u' =
      ∫ θ in (0 : ℝ)..(T - u' 0), contHeat (2 * θ + (u' 0 - u 0)) 0 (u' 1 - u 1) := by
  have hmax : max (u 0) (u' 0) = u' 0 := max_eq_right hle
  have habs : |u 0 - u' 0| = u' 0 - u 0 := by
    rw [abs_of_nonpos (by linarith : u 0 - u' 0 ≤ 0)]; ring
  unfold contOverlap
  rw [hmax, habs]
  have hmx : (0 : ℝ) ≤ T - u' 0 := by linarith
  rw [MeasureTheory.integral_indicator measurableSet_Ioo,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hmx]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [show u 1 - u' 1 = -(u' 1 - u 1) by ring, contHeat_zero_neg]



/-- **The remaining-horizon asymptotic**: the horizon `⌊nT⌋₊` minus the `toNat` of a floor
grid time `⌊nc⌋`, rescaled by `n`, converges to `T - c`, given `0 ≤ c ≤ T`. -/
theorem tendsto_horizon_sub_floor_div (T c : ℝ) (hc0 : 0 ≤ c) (hcT : c ≤ T) :
    Tendsto (fun n : ℕ =>
        ((⌊(n : ℝ) * T⌋₊ - (⌊(n : ℝ) * c⌋ : ℤ).toNat : ℕ) : ℝ) / n) atTop (𝓝 (T - c)) := by
  have hmn : ∀ n : ℕ, (⌊(n : ℝ) * c⌋ : ℤ).toNat ≤ ⌊(n : ℝ) * T⌋₊ := by
    intro n
    rw [Int.floor_toNat]
    exact Nat.floor_mono (mul_le_mul_of_nonneg_left hcT (Nat.cast_nonneg n))
  have hcast : ∀ n : ℕ,
      ((⌊(n : ℝ) * T⌋₊ - (⌊(n : ℝ) * c⌋ : ℤ).toNat : ℕ) : ℝ)
        = (⌊(n : ℝ) * T⌋₊ : ℝ) - ((⌊(n : ℝ) * c⌋ : ℤ) : ℝ) := by
    intro n
    rw [Nat.cast_sub (hmn n)]
    have hnn : (0 : ℤ) ≤ ⌊(n : ℝ) * c⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg n) hc0)
    have e1 : ((⌊(n : ℝ) * c⌋ : ℤ).toNat : ℤ) = ⌊(n : ℝ) * c⌋ := Int.toNat_of_nonneg hnn
    have e2 : (((⌊(n : ℝ) * c⌋ : ℤ).toNat : ℕ) : ℝ)
        = (((⌊(n : ℝ) * c⌋ : ℤ).toNat : ℤ) : ℝ) := by norm_cast
    rw [e2, e1]
  have hT : Tendsto (fun n : ℕ => (⌊(n : ℝ) * T⌋₊ : ℝ) / n) atTop (𝓝 T) :=
    tendsto_nat_floor_div T (hc0.trans hcT)
  have hcfl : Tendsto (fun n : ℕ => ((⌊(n : ℝ) * c⌋ : ℤ) : ℝ) / n) atTop (𝓝 c) :=
    tendsto_int_floor_mul_div c
  have hdiff := hT.sub hcfl
  refine hdiff.congr' (Filter.Eventually.of_forall fun n => ?_)
  show (⌊(n : ℝ) * T⌋₊ : ℝ) / n - ((⌊(n : ℝ) * c⌋ : ℤ) : ℝ) / n
      = ((⌊(n : ℝ) * T⌋₊ - (⌊(n : ℝ) * c⌋ : ℤ).toNat : ℕ) : ℝ) / n
  rw [hcast n, sub_div]



/-- **The same-time displacement asymptotic**: the difference of two floors of
`√n·y + nc/2`-type expressions at the same slope `c`, rescaled by `√n`, converges to the
difference of the `y`'s exactly. -/
theorem tendsto_int_floor_sqrt_add_sub_div (c y y' : ℝ) :
    Tendsto (fun n : ℕ =>
        (((⌊Real.sqrt n * y' + (n : ℝ) * c / 2⌋ : ℤ) : ℝ) -
            ((⌊Real.sqrt n * y + (n : ℝ) * c / 2⌋ : ℤ) : ℝ)) / Real.sqrt n)
      atTop (𝓝 (y' - y)) := by
  have hh : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  refine tendsto_int_floor_sub_div hh ?_
  have heq : (fun n : ℕ => (Real.sqrt n * y' + (n : ℝ) * c / 2 -
        (Real.sqrt n * y + (n : ℝ) * c / 2)) / Real.sqrt n)
      =ᶠ[atTop] (fun _ : ℕ => y' - y) := by
    filter_upwards [hh.eventually_gt_atTop 0] with n hn
    have hn0 : Real.sqrt n ≠ 0 := hn.ne'
    field_simp
    ring
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => y' - y) atTop (𝓝 (y' - y))).congr' heq.symm



/-- **The different-times displacement asymptotic**: the numerator of the `dn` hypothesis of
`tendsto_integral_orientedGridReward_mul_of_pos`, built from floors at two different slopes
`s, s'`, rescaled by `2√n`, converges to `y' - y` exactly. -/
theorem tendsto_dn_pos_aux (s s' y y' : ℝ) :
    Tendsto (fun n : ℕ =>
        (2 * (((⌊Real.sqrt n * y' + (n : ℝ) * s' / 2⌋ : ℤ) : ℝ) -
              ((⌊Real.sqrt n * y + (n : ℝ) * s / 2⌋ : ℤ) : ℝ))
            - (((⌊(n : ℝ) * s'⌋ : ℤ) : ℝ) - ((⌊(n : ℝ) * s⌋ : ℤ) : ℝ)))
          / (2 * Real.sqrt n))
      atTop (𝓝 (y' - y)) := by
  have hh : Tendsto (fun n : ℕ => 2 * Real.sqrt n) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
  have e1 := tendsto_int_floor_sub_div_atTop
    (g := fun n : ℕ => Real.sqrt n * y' + (n : ℝ) * s' / 2) hh
  have e2 := tendsto_int_floor_sub_div_atTop
    (g := fun n : ℕ => Real.sqrt n * y + (n : ℝ) * s / 2) hh
  have e3 := tendsto_int_floor_sub_div_atTop (g := fun n : ℕ => (n : ℝ) * s') hh
  have e4 := tendsto_int_floor_sub_div_atTop (g := fun n : ℕ => (n : ℝ) * s) hh
  have hcomb := (((e1.const_mul 2).sub (e2.const_mul 2)).sub e3).add e4
  rw [show (2 : ℝ) * 0 - 2 * 0 - 0 + 0 = 0 by ring] at hcomb
  have hsum := hcomb.add (tendsto_const_nhds (x := y' - y))
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually_gt_atTop 0] with n hn
  have hn0 : Real.sqrt n ≠ 0 := hn.ne'
  show 2 * (((((⌊Real.sqrt n * y' + (n : ℝ) * s' / 2⌋ : ℤ) : ℝ)
          - (Real.sqrt n * y' + (n : ℝ) * s' / 2)) / (2 * Real.sqrt n)))
      - 2 * (((((⌊Real.sqrt n * y + (n : ℝ) * s / 2⌋ : ℤ) : ℝ)
          - (Real.sqrt n * y + (n : ℝ) * s / 2)) / (2 * Real.sqrt n)))
      - (((⌊(n : ℝ) * s'⌋ : ℤ) : ℝ) - (n : ℝ) * s') / (2 * Real.sqrt n)
      + (((⌊(n : ℝ) * s⌋ : ℤ) : ℝ) - (n : ℝ) * s) / (2 * Real.sqrt n) + (y' - y)
      = (2 * (((⌊Real.sqrt n * y' + (n : ℝ) * s' / 2⌋ : ℤ) : ℝ) -
              ((⌊Real.sqrt n * y + (n : ℝ) * s / 2⌋ : ℤ) : ℝ))
            - (((⌊(n : ℝ) * s'⌋ : ℤ) : ℝ) - ((⌊(n : ℝ) * s⌋ : ℤ) : ℝ)))
          / (2 * Real.sqrt n)
  field_simp
  ring



/-- **The elapsed-time asymptotic**: the `toNat` gap of two ordered nonnegative floors
`⌊ns⌋ ≤ ⌊ns'⌋`, rescaled by `n`, converges to `s' - s`. -/
theorem tendsto_floor_toNat_sub_div (s s' : ℝ) (hs0 : 0 ≤ s) (hss' : s ≤ s') :
    Tendsto (fun n : ℕ =>
        (((⌊(n : ℝ) * s'⌋ : ℤ).toNat - (⌊(n : ℝ) * s⌋ : ℤ).toNat : ℕ) : ℝ) / n)
      atTop (𝓝 (s' - s)) := by
  have hcast : ∀ n : ℕ,
      (((⌊(n : ℝ) * s'⌋ : ℤ).toNat - (⌊(n : ℝ) * s⌋ : ℤ).toNat : ℕ) : ℝ)
        = ((⌊(n : ℝ) * s'⌋ : ℤ) : ℝ) - ((⌊(n : ℝ) * s⌋ : ℤ) : ℝ) := by
    intro n
    have h0 : (0 : ℤ) ≤ ⌊(n : ℝ) * s⌋ := Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg n) hs0)
    have hmm' : ⌊(n : ℝ) * s⌋ ≤ ⌊(n : ℝ) * s'⌋ :=
      Int.floor_mono (mul_le_mul_of_nonneg_left hss' (Nat.cast_nonneg n))
    exact cast_toNat_sub_toNat h0 hmm'
  have hdiff := (tendsto_int_floor_mul_div s').sub (tendsto_int_floor_mul_div s)
  refine hdiff.congr' (Filter.Eventually.of_forall fun n => ?_)
  show ((⌊(n : ℝ) * s'⌋ : ℤ) : ℝ) / n - ((⌊(n : ℝ) * s⌋ : ℤ) : ℝ) / n
      = (((⌊(n : ℝ) * s'⌋ : ℤ).toNat - (⌊(n : ℝ) * s⌋ : ℤ).toNat : ℕ) : ℝ) / n
  rw [hcast n, sub_div]



/-- **The `dn` hypothesis of `tendsto_integral_orientedGridReward_mul_of_pos`, at the
floor sequences of two box points with `s ≤ s'`.** -/
theorem tendsto_dn_pos_final (s s' y y' : ℝ) (hs0 : 0 ≤ s) (hss' : s ≤ s') :
    Tendsto (fun n : ℕ =>
        (2 * (((⌊Real.sqrt n * y' + (n : ℝ) * s' / 2⌋ - ⌊Real.sqrt n * y + (n : ℝ) * s / 2⌋ :
              ℤ) : ℝ))
          - (((⌊(n : ℝ) * s'⌋ : ℤ).toNat - (⌊(n : ℝ) * s⌋ : ℤ).toNat : ℕ) : ℝ))
          / (2 * Real.sqrt n))
      atTop (𝓝 (y' - y)) := by
  have h := tendsto_dn_pos_aux s s' y y'
  refine h.congr' (Filter.Eventually.of_forall fun n => ?_)
  have h0 : (0 : ℤ) ≤ ⌊(n : ℝ) * s⌋ := Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg n) hs0)
  have hmm' : ⌊(n : ℝ) * s⌋ ≤ ⌊(n : ℝ) * s'⌋ :=
    Int.floor_mono (mul_le_mul_of_nonneg_left hss' (Nat.cast_nonneg n))
  dsimp only
  rw [cast_toNat_sub_toNat h0 hmm']
  push_cast
  ring

/-- **The `dn` hypothesis of `tendsto_integral_orientedGridReward_mul_of_eq`, at the floor
sequences of two box points at the same time.** -/
theorem tendsto_dn_eq_final (c y y' : ℝ) :
    Tendsto (fun n : ℕ =>
        ((⌊Real.sqrt n * y' + (n : ℝ) * c / 2⌋ - ⌊Real.sqrt n * y + (n : ℝ) * c / 2⌋ : ℤ) : ℝ)
          / Real.sqrt n)
      atTop (𝓝 (y' - y)) := by
  have h := tendsto_int_floor_sqrt_add_sub_div c y y'
  refine h.congr' (Filter.Eventually.of_forall fun n => ?_)
  push_cast
  ring



/-- **The covariance of the grid reward field at the floor sequences of two real box
points, with the earlier point first**, converges to `Var(η) · contOverlap`. -/
theorem tendsto_integral_orientedGridReward_mul_box_of_le (ν : Measure ℤ) (hν : CriticalLaw ν)
    (hBinomial : External.BinomialLocalCLT) (T : ℝ)
    (u u' : Fin 2 → ℝ) (hu0 : 0 ≤ u 0) (hle : u 0 ≤ u' 0) (hu'T : u' 0 ≤ T) :
    Tendsto (fun n : ℕ => ∫ η : Site 2 → ℝ,
        orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
          ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ *
        orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u' 0⌋
          ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋
      ∂(iidLaw 2 (realLaw ν))) atTop
      (𝓝 ((∫ x : ℝ, x ^ 2 ∂(realLaw ν)) * contOverlap T u u')) := by
  rw [contOverlap_eq_intervalIntegral_of_le hle hu'T]
  by_cases hdeg : u' 0 = T
  · have hval0 : (∫ θ in (0 : ℝ)..(T - u' 0), contHeat (2 * θ + (u' 0 - u 0)) 0 (u' 1 - u 1)) = 0 := by
      rw [hdeg, sub_self, intervalIntegral.integral_same]
    rw [hval0, mul_zero]
    have hzero : ∀ n : ℕ, (∫ η : Site 2 → ℝ,
        orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
          ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ *
        orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u' 0⌋
          ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋
        ∂(iidLaw 2 (realLaw ν))) = 0 := by
      intro n
      have hNe : ⌊(n : ℝ) * T⌋₊ ≤ (⌊(n : ℝ) * u' 0⌋ : ℤ).toNat := by
        rw [Int.floor_toNat, hdeg]
      have hf0 : (fun η : Site 2 → ℝ =>
          orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
            ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ *
          orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u' 0⌋
            ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋) = fun _ => (0 : ℝ) := by
        funext η
        rw [orientedGridReward_eq_zero_of_le hNe, mul_zero]
      rw [hf0, integral_zero]
    exact tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => (hzero n).symm)
  · have hu'ltT : u' 0 < T := lt_of_le_of_ne hu'T hdeg
    have ha : (0 : ℝ) < T - u' 0 := by linarith
    have hab : T - u' 0 < T - u' 0 + 1 := by linarith
    rcases hle.eq_or_lt with heq | hlt
    · rw [← heq]
      simp only [sub_self, add_zero]
      have ha' : (0 : ℝ) < T - u 0 := by rw [heq]; exact ha
      have hab' : T - u 0 < T - u 0 + 1 := by linarith
      have hu0T : u 0 ≤ T := by rw [heq]; exact hu'ltT.le
      refine tendsto_integral_orientedGridReward_mul_of_eq ν hν hBinomial
        (a := T - u 0) (b := T - u 0 + 1) (dstar := u' 1 - u 1) ha' hab'
        (m := fun n : ℕ => ⌊(n : ℝ) * u 0⌋)
        (j := fun n : ℕ => ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋)
        (j' := fun n : ℕ => ⌊Real.sqrt n * u' 1 + (n : ℝ) * u 0 / 2⌋)
        (N := fun n : ℕ => ⌊(n : ℝ) * T⌋₊)
        ?_ ?_ ?_ ?_
      · intro n
        rw [Int.floor_toNat]
        exact Nat.floor_mono (mul_le_mul_of_nonneg_left hu0T (Nat.cast_nonneg n))
      · exact (eq_or_ne (u 1) (u' 1)).imp
          (fun h n => by rw [h]) (fun h => sub_ne_zero.mpr (Ne.symm h))
      · exact tendsto_horizon_sub_floor_div T (u 0) hu0 hu0T
      · exact tendsto_dn_eq_final (u 0) (u 1) (u' 1)
    · have hu0T : u 0 ≤ T := by linarith
      refine tendsto_integral_orientedGridReward_mul_of_pos ν hν hBinomial
        (δstar := u' 0 - u 0) (dstar := u' 1 - u 1) (a := T - u' 0) (b := T - u' 0 + 1)
        (by linarith) ha.le hab
        (m := fun n : ℕ => ⌊(n : ℝ) * u 0⌋) (m' := fun n : ℕ => ⌊(n : ℝ) * u' 0⌋)
        (j := fun n : ℕ => ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋)
        (j' := fun n : ℕ => ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋)
        (N := fun n : ℕ => ⌊(n : ℝ) * T⌋₊)
        ?_ ?_ ?_ ?_ ?_
      · intro n
        rw [Int.floor_toNat, Int.floor_toNat]
        exact Nat.floor_mono (mul_le_mul_of_nonneg_left hlt.le (Nat.cast_nonneg n))
      · intro n
        rw [Int.floor_toNat]
        exact Nat.floor_mono (mul_le_mul_of_nonneg_left hu'ltT.le (Nat.cast_nonneg n))
      · exact tendsto_floor_toNat_sub_div (u 0) (u' 0) hu0 hlt.le
      · exact tendsto_horizon_sub_floor_div T (u' 0) (hu0.trans hlt.le) hu'ltT.le
      · exact tendsto_dn_pos_final (u 0) (u' 0) (u 1) (u' 1) hu0 hlt.le



/-- **The covariance of the grid reward field at the floor sequences of two real box
points converges to `Var(η) · contOverlap`**, for two points in any order. -/
theorem tendsto_integral_orientedGridReward_mul_box (ν : Measure ℤ) (hν : CriticalLaw ν)
    (hBinomial : External.BinomialLocalCLT) (T : ℝ)
    (u u' : Fin 2 → ℝ) (hu0 : 0 ≤ u 0) (huT : u 0 ≤ T) (hu'0 : 0 ≤ u' 0) (hu'T : u' 0 ≤ T) :
    Tendsto (fun n : ℕ => ∫ η : Site 2 → ℝ,
        orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
          ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ *
        orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u' 0⌋
          ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋
      ∂(iidLaw 2 (realLaw ν))) atTop
      (𝓝 ((∫ x : ℝ, x ^ 2 ∂(realLaw ν)) * contOverlap T u u')) := by
  rcases le_total (u 0) (u' 0) with hle | hle
  · exact tendsto_integral_orientedGridReward_mul_box_of_le ν hν hBinomial T u u' hu0 hle hu'T
  · have h := tendsto_integral_orientedGridReward_mul_box_of_le ν hν hBinomial T u' u hu'0 hle huT
    rw [contOverlap_symm] at h
    refine h.congr' (Filter.Eventually.of_forall fun n => ?_)
    exact integral_congr_ae (Filter.Eventually.of_forall fun η => mul_comm _ _)

end Parking
end
