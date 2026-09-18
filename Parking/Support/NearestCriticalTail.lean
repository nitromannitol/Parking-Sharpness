/-
The critical lower tail of `parking.tex:1807-1833` in the rescaled parking
odometer. The source estimate has fixed positive constants after the law's
variance and third moment are chosen. Its logarithmic error vanishes with the
horizon; the remaining negative power of the threshold then tends to zero.
-/
import Parking.External.CriticalScaleLowerTail
import Parking.Support.NearestCriticalNormalization
import Parking.Support.URealMoment
import Parking.Support.Continuum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open MeasureTheory ProbabilityTheory LatticeProb Filter Topology Parking.CriticalScale

theorem Parking.CriticalScale.realLaw_thirdMoment (ν : Measure ℤ)
    (hν : Parking.CriticalLaw ν) : Integrable (fun z : ℝ => |z| ^ 3) (Parking.realLaw ν) := by
  haveI := hν.prob
  obtain ⟨θ, hθ, he⟩ := Parking.realLaw_expMoment ν hν
  exact Parking.integrable_abs_pow_of_exp_moment _ hθ he 3

theorem Parking.CriticalScale.realLaw_variance_pos (ν : Measure ℤ)
    (hν : Parking.CriticalLaw ν) : 0 < variance (id : ℝ → ℝ) (Parking.realLaw ν) := by
  exact ENNReal.toReal_pos (ne_of_gt (Parking.realLaw_evariance_pos ν hν))
    (ne_of_lt (Parking.realLaw_evariance_lt_top ν hν))

theorem Parking.CriticalScale.exponent_one_admissible {d : ℕ}
    (hd : 1 ≤ d) (hd3 : d ≤ 3) : (1 : ℝ) < 4 / (4 - (d : ℝ)) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd3R : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  apply (lt_div_iff₀ (by linarith : (0 : ℝ) < 4 - (d : ℝ))).mpr
  linarith

theorem Parking.CriticalScale.eventually_threshold (L a : ℝ) :
    ∀ᶠ t : ℕ in atTop, 3 ≤ t ∧ L ^ a ≤ (t : ℝ) / 2 := by
  filter_upwards [eventually_ge_atTop 3, (tendsto_natCast_atTop_atTop :
    Tendsto (fun t : ℕ => (t : ℝ)) atTop atTop).eventually_ge_atTop (2 * L ^ a)] with t ht hL
  exact ⟨ht, by linarith⟩

theorem Parking.CriticalScale.log_rpow_mul_neg_rpow_tendsto (a b : ℝ) (hb : 0 < b) :
    Tendsto (fun t : ℕ => Real.log (t : ℝ) ^ a * (t : ℝ) ^ (-b)) atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_rpow_atTop a hb).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun t : ℕ => (t : ℝ)) atTop atTop)
  simpa only [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv, Function.comp_def] using h

theorem Parking.CriticalScale.scaled_event {s L x : ℝ} (hs : 0 < s) :
    (s⁻¹ * x ≤ 1 / L) ↔ x ≤ s / L := by
  rw [inv_mul_eq_div, div_le_iff₀ hs]
  simp [div_eq_mul_inv, mul_comm]

theorem Parking.CriticalScale.lowerTailRemainder_tendsto (d : ℕ) (L a : ℝ) :
    Tendsto (fun t : ℕ => lowerTailRemainder d t L a) atTop (𝓝 0) := by
  by_cases hd : d = 2
  · simpa only [lowerTailRemainder, if_pos hd, zero_mul, neg_div] using
      (log_rpow_mul_neg_rpow_tendsto ((7 : ℝ) / 4) ((1 : ℝ) / 2) (by norm_num)).mul_const (L ^ (a / 2))
  · simpa only [lowerTailRemainder, if_neg hd, zero_mul, neg_div] using
      (log_rpow_mul_neg_rpow_tendsto ((3 : ℝ) / 4) ((1 : ℝ) / 4) (by norm_num)).mul_const (L ^ (a / 4))

theorem Parking.CriticalScale.barDivisible_sqrt {d : ℕ} (ω : Parking.Data d)
    (t : ℕ) (ht : 0 < t) : Parking.barDivisible ω (Real.sqrt (t : ℝ)) 1 0 =
      (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) * Parking.uOf ω t 0 := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hpow : (Real.sqrt (t : ℝ)) ^ ((d : ℝ) / 2 - 2) =
      (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul htR.le]
    congr 1
    ring
  unfold Parking.barDivisible Parking.latticePoint
  simp only [one_mul, Pi.zero_apply, mul_zero, Int.floor_zero, hpow,
    Real.sq_sqrt htR.le, Nat.floor_natCast]
  rfl

theorem Parking.CriticalScale.exists_moment_parameters (ν : Measure ℝ)
    (hv : 0 < variance (id : ℝ → ℝ) ν) :
    ∃ ν₀ M : ℝ, 0 < ν₀ ∧ ν₀ ^ 2 = variance (id : ℝ → ℝ) ν ∧
      (∫ z, |z| ^ 3 ∂ν) = M * variance (id : ℝ → ℝ) ν ^ ((3 : ℝ) / 2) := by
  refine ⟨Real.sqrt (variance id ν), (∫ z, |z| ^ 3 ∂ν) / variance id ν ^ ((3 : ℝ) / 2),
    Real.sqrt_pos.2 hv, Real.sq_sqrt hv.le, ?_⟩
  rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hv _).ne']

/-- Choose the source theorem's constants for the given critical parking law. -/
theorem Parking.exists_scaled_lower_tail_constants
    (hLower : Parking.External.CriticalScaleLowerTail)
    (hVar : Parking.External.VarianceScale) (hBerry : Parking.External.MultivariateBerryEsseen)
    {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ L : ℝ, 2 ≤ L →
      ∀ᶠ t : ℕ in atTop,
        (Parking.law d ν) {ω | (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) * Parking.uOf ω t 0 ≤ 1 / L} ≤
          ENNReal.ofReal (C * L ^ (-c) + C * Parking.CriticalScale.lowerTailRemainder d t L 1) := by
  haveI := hν.prob
  obtain ⟨ν₀, M, hν₀, hv, hM⟩ := exists_moment_parameters (Parking.realLaw ν)
    (realLaw_variance_pos ν hν)
  obtain ⟨c, C, hc, hC, hb⟩ := hLower hVar hBerry d hd hd3 ν₀ M hν₀ 1
    zero_lt_one (exponent_one_admissible hd hd3)
  have hvar : ENNReal.ofReal (ν₀ ^ 2) ≤ evariance (id : ℝ → ℝ) (Parking.realLaw ν) := by
    rw [hv]
    exact ENNReal.ofReal_toReal_le
  refine ⟨c, C, hc, hC, fun L hL => ?_⟩
  filter_upwards [eventually_threshold L 1] with t ht
  have htR : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hraw := hb (Parking.realLaw ν) inferInstance (Parking.realLaw_mean ν hν)
    (Parking.realLaw_evariance_pos ν hν) (Parking.realLaw_evariance_lt_top ν hν)
    (realLaw_thirdMoment ν hν) hvar hM.le t L ht.1 hL ht.2
  rw [odometer_lowerTail_eq hd, ← uOf_lowerTail_eq hd] at hraw
  have he : {ω : Parking.Data d | (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) * Parking.uOf ω t 0 ≤ 1 / L} =
      {ω : Parking.Data d | Parking.uOf ω t 0 ≤ (t : ℝ) ^ ((4 - (d : ℝ)) / 4) / L} := by
    ext ω
    simp only [Set.mem_setOf_eq, Real.rpow_neg htR.le]
    exact scaled_event (Real.rpow_pos_of_pos htR _)
  rw [he]
  exact hraw

/-- The normalized odometer has uniformly small lower tails near zero. -/
theorem Parking.scaled_lower_tails_small
    (hLower : Parking.External.CriticalScaleLowerTail)
    (hVar : Parking.External.VarianceScale) (hBerry : Parking.External.MultivariateBerryEsseen)
    {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ t : ℕ in atTop,
      (Parking.law d ν) {ω | (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) * Parking.uOf ω t 0 ≤ δ}
        ≤ ENNReal.ofReal ε := by
  obtain ⟨c, C, hc, _hC, hb⟩ :=
    Parking.exists_scaled_lower_tail_constants hLower hVar hBerry hd hd3 ν hν
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hdec : Tendsto (fun L : ℝ => C * L ^ (-c)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hc).const_mul C
  obtain ⟨L, hL, hval⟩ := ((eventually_ge_atTop (2 : ℝ)).and
    (hdec.eventually (eventually_lt_nhds hε2))).exists
  refine ⟨1 / L, one_div_pos.mpr (by linarith), ?_⟩
  have hrem : Tendsto (fun t : ℕ => C * lowerTailRemainder d t L 1) atTop (𝓝 0) := by
    simpa only [mul_zero] using (lowerTailRemainder_tendsto d L 1).const_mul C
  filter_upwards [hb L hL, hrem.eventually (eventually_lt_nhds hε2)] with t ht hr
  apply ht.trans
  apply ENNReal.ofReal_le_ofReal
  linarith

end
