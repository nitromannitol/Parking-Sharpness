import Parking.External.DonskerVaradhan
import Parking.Frozen.SubcriticalTail
import Parking.Support.DVLimitLower
import Parking.Support.RangeUpperScaling

/-!
# The Donsker-Varadhan range estimate without hypotheses

`Parking.External.DonskerVaradhanRange`, the Donsker-Varadhan asymptotic
`log E_0 e^{-a|R_t|} ~ -k t^{d/(d+2)}` quoted at `parking.tex:117-121`, holds with no
hypothesis, with `k = dvConst d a c`, where `c` is the limit of `n^{2/d}` times the least
Dirichlet ratio of a region of `n` sites (`Parking.exists_tendsto_dirichletRate`).

The proof is not the one of Donsker and Varadhan (large deviations of the occupation measure
and the Faber-Krahn inequality); see `CORRESPONDENCE.md`.  It identifies the constant through
the discrete Faber-Krahn function itself:

- the lower bound `eventually_log_rangeExp_ge` confines the walk to the support of a near
  optimal function of `n ≈ w t^{d/(d+2)}` sites (`Parking.rangeExp_ge_of_ratio`);
- the upper bound `eventually_log_rangeExp_le` coarse-grains the range into boxes: the walk
  spends little time in boxes it leaves porous (`Parking.measureReal_endPorous_le`), and the
  time outside the union of the boxes it fills is charged as a soft killing, which costs the
  least Dirichlet ratio of a region barely larger than that union
  (`Parking.dirichletRate_mul_le_of_soft`, `Parking.measureReal_rangeCard_le`).

That `k > 0` follows from the stretched-exponential upper bound
`Parking.range_moment_upper_bound_of_range_count`.

With the input proved, Theorem 1.1 also holds by the route of the paper
(`Parking.subcritical_tail_of_donskerVaradhan`): the Donsker-Varadhan hypothesis of
`Parking.Frozen.subcritical_tail` is discharged.
-/

open Filter Topology

namespace Parking

/-- The limit, for a fixed Faber-Krahn constant `c`. -/
theorem tendsto_log_rangeExp {d : ℕ} (hd : 1 ≤ d) {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    (hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ ((2 : ℝ) / d) * dirichletRate d n) atTop (𝓝 c)) :
    Tendsto (fun t : ℕ => Real.log (rangeExp d a t) / (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))
      atTop (𝓝 (-dvConst d a c)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set k := dvConst d a c
  have hspos : ∀ᶠ t : ℕ in atTop, 0 < (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)) := by
    filter_upwards [eventually_ge_atTop 1] with t ht
    have : (0 : ℝ) < t := by exact_mod_cast ht
    positivity
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · have hε : 0 < -k - b := by linarith
    filter_upwards [eventually_log_rangeExp_ge hd ha hc hlim (by linarith : 0 < (-k - b) / 2),
      hspos] with t ht hs
    rw [lt_div_iff₀ hs]
    have : -(k + (-k - b) / 2) * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2))
        > b * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)) := by
      have : -(k + (-k - b) / 2) > b := by linarith
      exact mul_lt_mul_of_pos_right this hs
    linarith
  · have hε : 0 < b + k := by linarith
    filter_upwards [eventually_log_rangeExp_le hd ha hc hlim (by linarith : 0 < (b + k) / 2),
      hspos] with t ht hs
    rw [div_lt_iff₀ hs]
    have : -((k - (b + k) / 2) * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))
        < b * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)) := by
      have : -(k - (b + k) / 2) < b := by linarith
      nlinarith
    linarith

/-- The constant is positive: otherwise the lower bound would contradict the
stretched-exponential decay of the range moment. -/
theorem dvConst_pos_of_tendsto {d : ℕ} (hd : 1 ≤ d) {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    (hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ ((2 : ℝ) / d) * dirichletRate d n) atTop (𝓝 c)) :
    0 < dvConst d a c := by
  obtain ⟨c', C, hc', hC, hupper⟩ := range_moment_upper_bound_of_range_count d hd a ha
  by_contra hk
  push Not at hk
  have hs : Tendsto (fun t : ℕ => (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2))) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  have hev := (eventually_log_rangeExp_ge hd ha hc hlim (by linarith : 0 < c' / 2)).and
    ((hs.eventually_gt_atTop (2 * Real.log C / c')).and (eventually_ge_atTop 1))
  obtain ⟨t, ht, hts, ht1⟩ := hev.exists
  have hZ := rangeExp_pos hd ha.le t
  have hU := hupper t ht1
  have hL : Real.log (rangeExp d a t)
      ≤ Real.log C - c' * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)) := by
    have := Real.log_le_log hZ hU
    rwa [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, ← sub_eq_add_neg]
      at this
  set s := (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2))
  have hs0 : 0 ≤ s := by positivity
  have h1 : -(dvConst d a c + c' / 2) * s ≥ -(c' / 2) * s := by
    have : -(dvConst d a c + c' / 2) ≥ -(c' / 2) := by linarith
    exact mul_le_mul_of_nonneg_right this hs0
  have h2 : 2 * Real.log C / c' < s := hts
  rw [div_lt_iff₀ hc'] at h2
  nlinarith

end Parking

/-- The Donsker-Varadhan estimate for the range of the walk, with no hypothesis. -/
-- FROZEN-STATEMENT-BEGIN
theorem Parking.External.donskerVaradhanRange_holds : Parking.External.DonskerVaradhanRange
-- FROZEN-STATEMENT-END
:= by
  intro d hd a ha
  obtain ⟨c, hc, hlim⟩ := Parking.exists_tendsto_dirichletRate hd
  exact ⟨Parking.dvConst d a c, Parking.dvConst_pos_of_tendsto hd ha hc hlim,
    Parking.tendsto_log_rangeExp hd ha hc hlim⟩

open MeasureTheory in
/-- **Theorem 1.1** (`thm:subcritical-tail`) by the route of the paper, its Donsker-Varadhan
hypothesis discharged by `Parking.External.donskerVaradhanRange_holds`. -/
theorem Parking.subcritical_tail_of_donskerVaradhan
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν < 0)
    (hpos : 0 < ν (Set.Ioi 0))
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
      C⁻¹ * Real.exp (-(C * (t : ℝ) ^ ((d : ℝ) / (d + 2)))) ≤ Parking.S (Parking.law d ν) t ∧
        Parking.S (Parking.law d ν) t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((d : ℝ) / (d + 2)))) :=
  Parking.Frozen.subcritical_tail Parking.External.donskerVaradhanRange_holds d hd ν hprob hint
    hmean hpos θ hθ hexp
