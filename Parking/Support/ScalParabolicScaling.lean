/-
The parabolic rescaling identities of `prop:oriented-scaling`'s Step 2
(`parking.tex:3205-3218`).

Step 2 derives `U(T) =_d T^{1/4} U(1)` from parabolic scaling and transfers the
convergence in law at time `1` to time `T`.  The transfer is the Slutsky step
that replaces the integer horizon `⌊nT⌋` by the real horizon `nT`: the ratio of
the two prefactors `⌊nT⌋^{-1/4}` and `(nT)^{-1/4}` tends to one, because
`⌊nT⌋/(nT) → 1` and `x ↦ x^{-1/4}` is continuous at one.

The three identities here are the arithmetic of that step, and nothing else.
-/
import Parking.Support.ScalScalingDischarge
import Parking.Support.UpperStep

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- **The rescaling identity of the parabolic scaling.**  For `T > 0` and `n > 0`
the prefactor `n^{-1/4}` is `T^{1/4}` times the prefactor at scale `nT`. -/
theorem rpow_neg_quarter_eq_mul (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ (-(1 : ℝ) / 4) = T ^ ((1 : ℝ) / 4) * ((n : ℝ) * T) ^ (-(1 : ℝ) / 4) := by
  rw [mul_comm (n:ℝ) T]
  rw [Real.mul_rpow (le_of_lt hT) (by positivity : (0:ℝ) ≤ (n:ℝ))]
  rw [← mul_assoc, ← Real.rpow_add hT]
  norm_num

/-- **The floor of the rescaled horizon is asymptotic to the horizon.**  For
`T > 0` the ratio `⌊nT⌋/(nT)` tends to one. -/
theorem tendsto_floor_mul_div (T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ => ((⌊(n : ℝ) * T⌋₊ : ℝ) / ((n : ℝ) * T))) atTop (𝓝 1) := by
  refine Filter.Tendsto.congr (fun n => ?_) (tendsto_nat_floor_div_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hT))
  simp [Function.comp, mul_comm]

/-- **The prefactor at the integer horizon is asymptotic to the prefactor at the
real horizon.**  Since `⌊nT⌋/(nT) → 1`, the ratio of the two prefactors
`(⌊nT⌋)^{-1/4} / (nT)^{-1/4}` tends to one; this is the Slutsky step that
transfers the convergence in law at time `1` to time `T`. -/
theorem tendsto_rpow_neg_quarter_floor_div (T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ => ((⌊(n : ℝ) * T⌋₊ : ℝ) ^ (-(1 : ℝ) / 4)) /
      (((n : ℝ) * T) ^ (-(1 : ℝ) / 4))) atTop (𝓝 1) := by
  have h := tendsto_floor_mul_div T hT
  have hcont : ContinuousAt (fun x : ℝ => x ^ (-(1 : ℝ) / 4)) 1 :=
    Real.continuousAt_rpow_const 1 (-(1 : ℝ) / 4) (Or.inl (by norm_num))
  have h1 : Tendsto (fun n : ℕ => (((⌊(n : ℝ) * T⌋₊ : ℝ) / ((n : ℝ) * T))) ^ (-(1 : ℝ) / 4))
      atTop (𝓝 (1 ^ (-(1 : ℝ) / 4))) := hcont.tendsto.comp h
  rw [Real.one_rpow] at h1
  refine Filter.Tendsto.congr (fun n => ?_) h1
  rw [Real.div_rpow (by positivity) (by positivity)]

/-- **The self-similarity clause of `prop:oriented-scaling` from the almost-sure
parabolic scaling.**  If `U(T)` agrees almost surely with `T^{1/4}U(1)`, then
the law of `U(T)` is the law of `T^{1/4}U(1)`, which is the frozen statement's
`Q.map (Uc T) = Q.map (fun ω => T^{1/4} * Uc 1 ω)`. -/
theorem map_selfsimilar_of_ae {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (Uc : ℝ → Ω → ℝ) (T : ℝ)
    (h : Uc T =ᵐ[Q] fun ω => T ^ ((1 : ℝ) / 4) * Uc 1 ω) :
    Q.map (Uc T) = Q.map fun ω => T ^ ((1 : ℝ) / 4) * Uc 1 ω :=
  Measure.map_congr h

/-- **The integrability clause of `prop:oriented-scaling` from an `L^r` bound.**
The paper's Step 2 bounds `n^{-1/4} u_n(0)` in `L^r` for a fixed `r > 4` and
concludes that the limit `U(1)` is integrable. -/
theorem integrable_of_memLp_one {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsFiniteMeasure Q] (U : Ω → ℝ) {r : ℝ≥0∞} (hr : 1 ≤ r) (h : MemLp U r Q) :
    Integrable U Q :=
  h.integrable hr

end Parking

/-- **A limit of eventually positive reals is nonnegative.**  The paper's Step 2
concludes `μ > 0` from the lower bound in `thm:oriented`; the limit of a
sequence that is eventually positive is nonnegative. -/
theorem mean_pos_of_tendsto_of_eventually_pos {f : ℕ → ℝ} {μ : ℝ}
    (h : Tendsto f atTop (𝓝 μ)) (hf : ∀ᶠ n in atTop, 0 < f n) : 0 ≤ μ := by
  exact ge_of_tendsto h (hf.mono fun n hn => hn.le)


theorem rNorm_rescaled_le_of_rNorm_le {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω)
    (X : ℕ → Ω → ℝ) (r : ℝ) (hr : 0 < r) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ n, Parking.rNorm Q r (X n) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4)) :
    ∀ n : ℕ, 1 ≤ n →
      Parking.rNorm Q r (fun ω => (n : ℝ) ^ (-(1 : ℝ) / 4) * X n ω) ≤ C := by
  intro n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hA : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg hn0.le _
  have hI : (0 : ℝ) ≤ ∫ ω, |X n ω| ^ r ∂Q :=
    integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hint : (∫ ω, |(n : ℝ) ^ (-(1 : ℝ) / 4) * X n ω| ^ r ∂Q)
      = ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ r * ∫ ω, |X n ω| ^ r ∂Q := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only []
    rw [abs_mul, abs_of_nonneg hA]
    exact Real.mul_rpow hA (abs_nonneg _)
  have hsplit : (((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ r * ∫ ω, |X n ω| ^ r ∂Q) ^ (1 / r)
      = (n : ℝ) ^ (-(1 : ℝ) / 4) * (∫ ω, |X n ω| ^ r ∂Q) ^ (1 / r) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hA r) hI]
    rw [← Real.rpow_mul hA r (1 / r), show r * (1 / r) = 1 by field_simp, Real.rpow_one]
  have hfin : (n : ℝ) ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4) = 1 := by
    rw [← Real.rpow_add hn0]; norm_num
  rw [Parking.rNorm, hint, hsplit]
  calc (n : ℝ) ^ (-(1 : ℝ) / 4) * (∫ ω, |X n ω| ^ r ∂Q) ^ (1 / r)
      ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) * (C * (n : ℝ) ^ ((1 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left (hb n) hA
    _ = C * ((n : ℝ) ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4)) := by ring
    _ = C := by rw [hfin, mul_one]


