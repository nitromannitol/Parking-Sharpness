import Parking.Support.TailTwoSided
import Parking.Support.RangeResolvent

/-!
# Range moment bounds and subcritical tails

The upper and lower estimates on the exponential moment of the walk range are
sufficient separately for the two halves of the subcritical tail estimate.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace Parking

/-- The upper stretched-exponential estimate for the walk range moment. -/
def RangeMomentUpperBound : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ a : ℝ, 0 < a →
    ∃ c C : ℝ, 0 < c ∧ 1 ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
      rangeExp d a t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2))))

/-- The lower stretched-exponential estimate for the walk range moment. -/
def RangeMomentLowerBound : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ a : ℝ, 0 < a →
    ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
      Real.exp (-(K * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))) ≤ C * rangeExp d a t

/-- The upper range moment estimate in dimension one follows from the range resolvent bound. -/
theorem range_moment_upper_bound_one (a : ℝ) (ha : 0 < a) :
    ∃ c C : ℝ, 0 < c ∧ 1 ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
      rangeExp 1 a t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((1 : ℝ) / 3))) := by
  obtain ⟨c, C, hc, _, hbound⟩ := exists_rangeExp_bound_one (d := 1) rfl
  let b : ℝ := min a 1
  have hb : 0 < b := lt_min ha zero_lt_one
  have hb1 : b ≤ 1 := min_le_right _ _
  have hba : b ≤ a := min_le_left _ _
  refine ⟨c * b ^ ((2 : ℝ) / 3), max 1 C,
    mul_pos hc (Real.rpow_pos_of_pos hb _), le_max_left _ _, fun t ht => ?_⟩
  have h := hbound b hb hb1 t ht
  calc
    rangeExp 1 a t ≤ rangeExp 1 b t := rangeExp_anti (by norm_num) hb.le hba t
    _ ≤ C * Real.exp (-(c * b ^ ((2 : ℝ) / 3) * (t : ℝ) ^ ((1 : ℝ) / 3))) := h
    _ ≤ max 1 C * Real.exp (-(c * b ^ ((2 : ℝ) / 3) * (t : ℝ) ^ ((1 : ℝ) / 3))) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)

/-- The logarithmic range asymptotic implies the two moment bounds. -/
theorem range_moment_bounds_of_donsker_varadhan (hDV : External.DonskerVaradhanRange) :
    RangeMomentUpperBound ∧ RangeMomentLowerBound := by
  have hbounds (d : ℕ) (hd : 1 ≤ d) (a : ℝ) (ha : 0 < a) :
      ∃ k C : ℝ, 0 < k ∧ 1 ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
        rangeExp d a t ≤ C * Real.exp (-(k / 2) * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2))) ∧
        Real.exp (-(2 * k) * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2))) ≤ C * rangeExp d a t := by
    obtain ⟨k, hk, hT⟩ := hDV d hd a ha
    have hα : 0 < (d : ℝ) / ((d : ℝ) + 2) := by
      have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
      apply div_pos <;> linarith
    obtain ⟨C, hC, hB⟩ := exp_bounds_of_log_tendsto
      (fun t => rangeExp_pos hd ha.le t) hk hα hT
    exact ⟨k, C, hk, hC, hB⟩
  constructor
  · intro d hd a ha
    obtain ⟨k, C, hk, hC, hB⟩ := hbounds d hd a ha
    refine ⟨k / 2, C, by linarith, hC, fun t ht => ?_⟩
    simpa only [neg_mul] using (hB t ht).1
  · intro d hd a ha
    obtain ⟨k, C, hk, hC, hB⟩ := hbounds d hd a ha
    refine ⟨2 * k, C, by linarith, hC, fun t ht => ?_⟩
    simpa only [neg_mul] using (hB t ht).2

variable {d : ℕ}

/-- The upper range moment estimate implies the upper subcritical tail bound. -/
theorem exists_upper_tail_of_range_moment (hd : 1 ≤ d)
    (hUpper : ∀ a : ℝ, 0 < a → ∃ c C : ℝ, 0 < c ∧ 1 ≤ C ∧
      ∀ t : ℕ, 1 ≤ t →
        rangeExp d a t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))))
    {ν : Measure ℤ}
    [IsProbabilityMeasure ν] (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν < 0) {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℕ, 1 ≤ t →
      S (law d ν) t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))) := by
  obtain ⟨a, C₂, ha, hC₂, hUp⟩ := exists_subcritical_rangeExp hd hint hmean hθ hexp
  obtain ⟨c₂, C₃, hc₂, hC₃, hB₃⟩ := hUpper a ha
  have hC₃pos : (0 : ℝ) < C₃ := lt_of_lt_of_le zero_lt_one hC₃
  refine ⟨c₂, C₂ * C₃, hc₂, mul_pos hC₂ hC₃pos, fun t ht => ?_⟩
  have h1 := (hUp t).2
  have h2 := hB₃ t ht
  calc S (law d ν) t ≤ C₂ * rangeExp d a t := h1
    _ ≤ C₂ * (C₃ * Real.exp (-(c₂ * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2))))) :=
        mul_le_mul_of_nonneg_left h2 hC₂.le
    _ = C₂ * C₃ * Real.exp (-(c₂ * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))) := by
        ring

/-- The upper subcritical tail estimate in dimension one. -/
theorem exists_upper_tail_one {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν < 0) {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℕ, 1 ≤ t →
      S (law 1 ν) t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((1 : ℝ) / 3))) := by
  have hr : ((1 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) + 2) = (1 : ℝ) / 3 := by norm_num
  have hUpper : ∀ a : ℝ, 0 < a → ∃ c C : ℝ, 0 < c ∧ 1 ≤ C ∧
      ∀ t : ℕ, 1 ≤ t → rangeExp 1 a t ≤
        C * Real.exp (-(c * (t : ℝ) ^ (((1 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) + 2)))) := by
    intro a ha
    rw [hr]
    exact range_moment_upper_bound_one a ha
  have h := exists_upper_tail_of_range_moment (d := 1) (by norm_num)
    hUpper hint hmean hθ hexp
  rw [hr] at h
  exact h

/-- The lower range moment estimate implies the lower subcritical tail bound. -/
theorem exists_lower_tail_of_range_moment (hd : 1 ≤ d)
    (hLower : ∀ a : ℝ, 0 < a → ∃ K C : ℝ, 0 < K ∧ 1 ≤ C ∧
      ∀ t : ℕ, 1 ≤ t →
        Real.exp (-(K * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))) ≤ C * rangeExp d a t)
    {ν : Measure ℤ}
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
  obtain ⟨K₁, C₄, hK₁, hC₄, hB₄⟩ :=
    hLower (-Real.log ((ν {j : ℤ | 0 ≤ j}).toReal)) ha₁
  have hC₄pos : (0 : ℝ) < C₄ := lt_of_lt_of_le zero_lt_one hC₄
  have hm : 0 < ∫ k, max (k : ℝ) 0 ∂ν := integral_posPart_pos hint hpos
  refine ⟨K₁, C₄ / (∫ k, max (k : ℝ) 0 ∂ν), hK₁, div_pos hC₄pos hm, fun t ht => ?_⟩
  have h1 : rangeExp d (-Real.log ((ν {j : ℤ | 0 ≤ j}).toReal)) t
      ≤ ∫ p, (ν {j : ℤ | 0 ≤ j}).toReal ^ (rangeCard (0 : Site d) p t - 1) ∂(walkLaw d) :=
    rangeExp_le_powIntegral hd hq0 hq1.le t (hIR t)
  have h2 := hB₄ t ht
  have h3 := hLow t
  have hinv : (C₄ / (∫ k, max (k : ℝ) 0 ∂ν))⁻¹ = (∫ k, max (k : ℝ) 0 ∂ν) / C₄ := by
    rw [inv_div]
  rw [hinv]
  have hstep : Real.exp (-(K₁ * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))) / C₄
      ≤ rangeExp d (-Real.log ((ν {j : ℤ | 0 ≤ j}).toReal)) t :=
    (div_le_iff₀ hC₄pos).2 (by linarith [h2])
  have hmul : (∫ k, max (k : ℝ) 0 ∂ν)
        * (Real.exp (-(K₁ * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))) / C₄)
      ≤ (∫ k, max (k : ℝ) 0 ∂ν)
        * ∫ p, (ν {j : ℤ | 0 ≤ j}).toReal ^ (rangeCard (0 : Site d) p t - 1) ∂(walkLaw d) :=
    mul_le_mul_of_nonneg_left (le_trans hstep h1) hm.le
  calc (∫ k, max (k : ℝ) 0 ∂ν) / C₄
        * Real.exp (-(K₁ * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2))))
      = (∫ k, max (k : ℝ) 0 ∂ν)
        * (Real.exp (-(K₁ * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))) / C₄) := by
        ring
    _ ≤ (∫ k, max (k : ℝ) 0 ∂ν)
        * ∫ p, (ν {j : ℤ | 0 ≤ j}).toReal ^ (rangeCard (0 : Site d) p t - 1) ∂(walkLaw d) := hmul
    _ ≤ S (law d ν) t := h3

/-- Both range moment estimates imply the subcritical tail estimate. -/
theorem exists_tail_bounds_of_range_moment
    (hUpper : RangeMomentUpperBound) (hLower : RangeMomentLowerBound)
    (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν < 0) (hpos : 0 < ν (Set.Ioi (0 : ℤ)))
    {θ : ℝ} (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
      C⁻¹ * Real.exp (-(C * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))) ≤ S (law d ν) t ∧
        S (law d ν) t ≤ C * Real.exp (-(c * (t : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 2)))) := by
  obtain ⟨K, C₁, _, hC₁, hlow⟩ :=
    exists_lower_tail_of_range_moment hd (hLower d hd) hint hmean hpos hθ hexp
  obtain ⟨c, C₂, hc, _, hup⟩ :=
    exists_upper_tail_of_range_moment hd (hUpper d hd) hint hmean hθ hexp
  exact two_sided_combine hC₁ hc hlow hup

end Parking

end
