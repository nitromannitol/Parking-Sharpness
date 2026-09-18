/-
`thm:subcritical-tail` from `thm:subcritical` and `lem:range-lower`
(`parking.tex:2497-2502`).

The two bounds of the paper are bounds on averages over the walk alone.  The
upper one is `S_t\leq C\E_0e^{-a|R_t|}` with the `a>0` that `thm:subcritical`
produces; the lower one is `S_t\geq\E\eta(0)^+\E_0[q^{|R_t|-1}]` with
`q=\P(\eta(0)\geq0)`, and `q^{|R_t|-1}\geq e^{-a_1|R_t|}` for `a_1=-\log q`,
which is positive because the mean is negative.  The Donsker-Varadhan estimate
turns each average into a stretched exponential in `t`, and the two one-sided
bounds are then merged into one pair of constants.
-/
import Parking.Support.TailRange
import Parking.Support.TailExp
import Parking.Support.SubcriticalInterval
import Parking.Frozen.RangeLower
import Parking.External.DonskerVaradhan

open MeasureTheory Filter Topology

noncomputable section

namespace Parking

variable {d : ℕ}

/-- **The upper half of `eq:sharpness`.**  `thm:subcritical` gives
`S_t\leq C\E_0e^{-a|R_t|}` and the Donsker-Varadhan estimate turns the average
into a stretched exponential. -/
theorem exists_upper_tail (hDV : External.DonskerVaradhanRange) (hd : 1 ≤ d) {ν : Measure ℤ}
    [IsProbabilityMeasure ν] (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν < 0) {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℕ, 1 ≤ t →
      S (law d ν) t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))) := by
  obtain ⟨a, C₂, ha, hC₂, hUp⟩ := exists_subcritical_rangeExp hd hint hmean hθ hexp
  obtain ⟨k₂, hk₂, hT₂⟩ := hDV d hd a ha
  have hαpos : 0 < (d : ℝ) / ((d : ℝ) + 2) := by
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    apply div_pos <;> linarith
  obtain ⟨C₃, hC₃, hB₃⟩ := exp_bounds_of_log_tendsto
      (F := fun t => rangeExp d a t) (fun t => rangeExp_pos hd ha.le t) hk₂ hαpos hT₂
  have hC₃pos : (0 : ℝ) < C₃ := lt_of_lt_of_le zero_lt_one hC₃
  refine ⟨k₂ / 2, C₂ * C₃, by linarith, mul_pos hC₂ hC₃pos, fun t ht => ?_⟩
  have h1 := (hUp t).2
  have h2 := (hB₃ t ht).1
  calc S (law d ν) t ≤ C₂ * rangeExp d a t := h1
    _ ≤ C₂ * (C₃ * Real.exp (-(k₂ / 2) * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))) :=
        mul_le_mul_of_nonneg_left h2 hC₂.le
    _ = C₂ * C₃ * Real.exp (-(k₂ / 2 * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))) := by
        rw [neg_mul]
        ring

/-- **The lower half of `eq:sharpness`.**  `lem:range-lower` gives
`S_t\geq\E\eta(0)^+\E_0[q^{|R_t|-1}]`, the power is above `e^{-a_1|R_t|}` for
`a_1=-\log q>0`, and the Donsker-Varadhan estimate applies to that average too. -/
theorem exists_lower_tail (hDV : External.DonskerVaradhanRange) (hd : 1 ≤ d) {ν : Measure ℤ}
    [IsProbabilityMeasure ν] (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν < 0) (hpos : 0 < ν (Set.Ioi (0 : ℤ))) {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧ ∀ t : ℕ, 1 ≤ t →
      C⁻¹ * Real.exp (-(K * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))) ≤ S (law d ν) t := by
  obtain ⟨hIR, -, hLow⟩ := Frozen.range_lower d hd ν inferInstance hint hmean hpos θ hθ hexp
  have hq0 : 0 < (ν {j : ℤ | 0 ≤ j}).toReal := nonnegProb_pos hpos
  have hq1 : (ν {j : ℤ | 0 ≤ j}).toReal < 1 := nonnegProb_lt_one hmean
  have ha₁ : 0 < -Real.log ((ν {j : ℤ | 0 ≤ j}).toReal) := by
    have h := Real.log_neg hq0 hq1
    linarith
  obtain ⟨k₁, hk₁, hT₁⟩ := hDV d hd (-Real.log ((ν {j : ℤ | 0 ≤ j}).toReal)) ha₁
  have hαpos : 0 < (d : ℝ) / ((d : ℝ) + 2) := by
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    apply div_pos <;> linarith
  obtain ⟨C₄, hC₄, hB₄⟩ := exp_bounds_of_log_tendsto
      (F := fun t => rangeExp d (-Real.log ((ν {j : ℤ | 0 ≤ j}).toReal)) t)
      (fun t => rangeExp_pos hd ha₁.le t) hk₁ hαpos hT₁
  have hC₄pos : (0 : ℝ) < C₄ := lt_of_lt_of_le zero_lt_one hC₄
  have hm : 0 < ∫ k, max (k : ℝ) 0 ∂ν := integral_posPart_pos hint hpos
  refine ⟨2 * k₁, C₄ / (∫ k, max (k : ℝ) 0 ∂ν), by linarith, div_pos hC₄pos hm, fun t ht => ?_⟩
  have h1 : rangeExp d (-Real.log ((ν {j : ℤ | 0 ≤ j}).toReal)) t
      ≤ ∫ p, (ν {j : ℤ | 0 ≤ j}).toReal ^ (rangeCard (0 : Site d) p t - 1) ∂(walkLaw d) :=
    rangeExp_le_powIntegral hd hq0 hq1.le t (hIR t)
  have h2 := (hB₄ t ht).2
  have h3 := hLow t
  have hinv : (C₄ / (∫ k, max (k : ℝ) 0 ∂ν))⁻¹ = (∫ k, max (k : ℝ) 0 ∂ν) / C₄ := by
    rw [inv_div]
  rw [hinv]
  have hstep : Real.exp (-(2 * k₁) * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2))) / C₄
      ≤ rangeExp d (-Real.log ((ν {j : ℤ | 0 ≤ j}).toReal)) t :=
    (div_le_iff₀ hC₄pos).2 (by linarith [h2])
  have hmul : (∫ k, max (k : ℝ) 0 ∂ν)
        * (Real.exp (-(2 * k₁) * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2))) / C₄)
      ≤ (∫ k, max (k : ℝ) 0 ∂ν)
        * ∫ p, (ν {j : ℤ | 0 ≤ j}).toReal ^ (rangeCard (0 : Site d) p t - 1) ∂(walkLaw d) :=
    mul_le_mul_of_nonneg_left (le_trans hstep h1) hm.le
  calc (∫ k, max (k : ℝ) 0 ∂ν) / C₄
        * Real.exp (-(2 * k₁ * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2))))
      = (∫ k, max (k : ℝ) 0 ∂ν)
        * (Real.exp (-(2 * k₁) * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2))) / C₄) := by
        rw [neg_mul]
        ring
    _ ≤ (∫ k, max (k : ℝ) 0 ∂ν)
        * ∫ p, (ν {j : ℤ | 0 ≤ j}).toReal ^ (rangeCard (0 : Site d) p t - 1) ∂(walkLaw d) := hmul
    _ ≤ S (law d ν) t := h3

/-- **Two one-sided stretched-exponential bounds merge into one pair of
constants**, as `eq:sharpness` states them. -/
theorem two_sided_combine {f : ℕ → ℝ} {α K C₁ c C₂ : ℝ} (hC₁ : 0 < C₁) (hc : 0 < c)
    (hlow : ∀ t : ℕ, 1 ≤ t → C₁⁻¹ * Real.exp (-(K * (t : ℝ) ^ α)) ≤ f t)
    (hup : ∀ t : ℕ, 1 ≤ t → f t ≤ C₂ * Real.exp (-(c * (t : ℝ) ^ α))) :
    ∃ c' C' : ℝ, 0 < c' ∧ c' ≤ C' ∧ ∀ t : ℕ, 1 ≤ t →
      C'⁻¹ * Real.exp (-(C' * (t : ℝ) ^ α)) ≤ f t ∧
        f t ≤ C' * Real.exp (-(c' * (t : ℝ) ^ α)) := by
  refine ⟨min c (max (max C₁ K) C₂), max (max C₁ K) C₂, ?_, min_le_right _ _, ?_⟩
  · exact lt_min hc (lt_of_lt_of_le hC₁ (le_trans (le_max_left _ _) (le_max_left _ _)))
  · intro t ht
    have hC'pos : 0 < max (max C₁ K) C₂ :=
      lt_of_lt_of_le hC₁ (le_trans (le_max_left _ _) (le_max_left _ _))
    have htα : (0 : ℝ) ≤ (t : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg t) α
    have hC1le : C₁ ≤ max (max C₁ K) C₂ := le_trans (le_max_left _ _) (le_max_left _ _)
    have hKle : K ≤ max (max C₁ K) C₂ := le_trans (le_max_right _ _) (le_max_left _ _)
    have hC2le : C₂ ≤ max (max C₁ K) C₂ := le_max_right _ _
    constructor
    · have h1 : (max (max C₁ K) C₂)⁻¹ ≤ C₁⁻¹ := inv_anti₀ hC₁ hC1le
      have h2 : Real.exp (-(max (max C₁ K) C₂ * (t : ℝ) ^ α))
          ≤ Real.exp (-(K * (t : ℝ) ^ α)) := by
        refine Real.exp_le_exp.2 ?_
        nlinarith [htα, hKle]
      calc (max (max C₁ K) C₂)⁻¹ * Real.exp (-(max (max C₁ K) C₂ * (t : ℝ) ^ α))
          ≤ C₁⁻¹ * Real.exp (-(K * (t : ℝ) ^ α)) :=
            mul_le_mul h1 h2 (Real.exp_nonneg _) (le_of_lt (inv_pos.2 hC₁))
        _ ≤ f t := hlow t ht
    · have h3 : Real.exp (-(c * (t : ℝ) ^ α))
          ≤ Real.exp (-(min c (max (max C₁ K) C₂) * (t : ℝ) ^ α)) := by
        refine Real.exp_le_exp.2 ?_
        nlinarith [htα, min_le_left c (max (max C₁ K) C₂)]
      calc f t ≤ C₂ * Real.exp (-(c * (t : ℝ) ^ α)) := hup t ht
        _ ≤ max (max C₁ K) C₂ * Real.exp (-(min c (max (max C₁ K) C₂) * (t : ℝ) ^ α)) :=
            mul_le_mul hC2le h3 (Real.exp_nonneg _) (le_of_lt hC'pos)

/-- **`eq:sharpness`**, from the two halves. -/
theorem exists_tail_bounds (hDV : External.DonskerVaradhanRange) (hd : 1 ≤ d) {ν : Measure ℤ}
    [IsProbabilityMeasure ν] (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν < 0) (hpos : 0 < ν (Set.Ioi (0 : ℤ))) {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
      C⁻¹ * Real.exp (-(C * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))) ≤ S (law d ν) t ∧
        S (law d ν) t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))) := by
  obtain ⟨K, C₁, hK, hC₁, hlow⟩ := exists_lower_tail hDV hd hint hmean hpos hθ hexp
  obtain ⟨c, C₂, hc, hC₂, hup⟩ := exists_upper_tail hDV hd hint hmean hθ hexp
  exact two_sided_combine hC₁ hc hlow hup

end Parking

end
