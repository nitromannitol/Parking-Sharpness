/- `prop:oriented-scaling` reduced to its analytic clauses.

The frozen statement (`parking.tex:3151-3159`) asserts seven things about the limiting
value: its measurability, the convergence in distribution to it, its self-similarity, its
integrability, that `μ` is its mean, that `μ` is positive, and the convergence of the
rescaled means.  The last four are soft consequences of the convergence in distribution
and of the bounds the repository already has on the directed divisible odometer: the
uniform bound in `L^8` makes the family uniformly integrable, the mean bound of
`thm:oriented` makes the truncated means of the limit bounded, and the matching lower
bound makes the limiting mean positive.  What is left, and only that, is the measurability
of the limiting value, the convergence in distribution itself, and the self-similarity.
-/
import Parking.Support.OrientedMeanLimit
import Parking.Support.OrientedTwoLower

noncomputable section
namespace Parking
open MeasureTheory Filter Topology LatticeProb

/-- Every polynomial moment of a critical one-site law is finite. -/
theorem CriticalLaw.integrable_rpow {ν : Measure ℤ} (hν : CriticalLaw ν) {r : ℝ}
    (hr : 0 ≤ r) : Integrable (fun k : ℤ => |(k : ℝ)| ^ r) ν := by
  haveI := hν.prob
  obtain ⟨θ, hθ, hexp⟩ := hν.expMoment
  obtain ⟨K, _hK, hbd⟩ := rpow_le_const_mul_exp hr hθ
  refine Integrable.mono' (hexp.const_mul K)
    (measurable_from_countable' (fun k : ℤ => |(k : ℝ)| ^ r)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact hbd _ (abs_nonneg _)

/-- The truncations of a nonnegative real exhaust it. -/
theorem iSup_ofReal_truncBdd {y : ℝ} (hy : 0 ≤ y) :
    (⨆ M : ℕ, ENNReal.ofReal (max 0 (min y (M : ℝ)))) = ENNReal.ofReal y := by
  refine le_antisymm (iSup_le fun M => ENNReal.ofReal_le_ofReal (max_le hy (min_le_left _ _))) ?_
  refine le_iSup_of_le ⌈y⌉₊ ?_
  have h : y ≤ ((⌈y⌉₊ : ℕ) : ℝ) := Nat.le_ceil y
  rw [min_eq_left h, max_eq_right hy]

/-- **The integrability of the limit from the convergence in distribution.**  The rescaled
means are bounded by `thm:oriented`, so every truncated mean of the limit is bounded by the
same constant, and the limit is integrable. -/
theorem integrable_limit_of_weak (ν : Measure ℤ) (hν : CriticalLaw ν)
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (V : Ω → ℝ) (hVm : Measurable V)
    (hweak : ∀ F : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ => ∫ w : Data 2, F ((n : ℝ) ^ (-(1 : ℝ) / 4) *
            uOriented (fun y => (w.1 y : ℝ)) ⌊(n : ℝ) * (1 : ℝ)⌋₊ 0)
          ∂(orientedLaw 2 ν)) atTop (𝓝 (∫ ω, F (V ω) ∂Q))) :
    (∀ᵐ ω ∂Q, 0 ≤ V ω) ∧ Integrable V Q := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (orientedLaw 2 ν) := orientedLaw_isProbability (by norm_num) ν
  simp only [mul_one, Nat.floor_natCast] at hweak
  set X : ℕ → Data 2 → ℝ := fun n w =>
    (n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (fun y => (w.1 y : ℝ)) n 0 with hX
  have hXnn : ∀ n : ℕ, ∀ᵐ w ∂(orientedLaw 2 ν), 0 ≤ X n w := fun n =>
    Filter.Eventually.of_forall fun w =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (uOriented_nonneg _ n 0)
  have hnn : ∀ᵐ ω ∂Q, 0 ≤ V ω :=
    ae_nonneg_of_tendsto_integral_belowZero hVm.aestronglyMeasurable (hweak belowZero) hXnn
  obtain ⟨C, hC, hfacts⟩ := exists_rescaled_uOriented_eighth ν hν
  obtain ⟨D, hD, hup⟩ :=
    exists_meanuOriented_two_upper ν hν.mean 8 (by norm_num) (hν.integrable_rpow (by norm_num))
  have hXint : ∀ n : ℕ, Integrable (X n) (orientedLaw 2 ν) := fun n => (hfacts n).1
  have hXmean : ∀ n : ℕ, 1 ≤ n → ∫ w, X n w ∂(orientedLaw 2 ν) ≤ D := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have heq : ∫ w, X n w ∂(orientedLaw 2 ν)
        = (n : ℝ) ^ (-(1 : ℝ) / 4) * meanuOriented (orientedLaw 2 ν) n := by
      rw [hX, meanuOriented, ← integral_const_mul]
    rw [heq]
    have hA : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg hn0.le _
    have hfin : (n : ℝ) ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4) = 1 := by
      rw [← Real.rpow_add hn0]; norm_num
    calc (n : ℝ) ^ (-(1 : ℝ) / 4) * meanuOriented (orientedLaw 2 ν) n
        ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) * (D * (n : ℝ) ^ ((1 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left (hup n hn) hA
      _ = D * ((n : ℝ) ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4)) := by ring
      _ = D := by rw [hfin, mul_one]
  have htrunc : ∀ M : ℕ, ∫ ω, truncBdd (M : ℝ) (V ω) ∂Q ≤ D := by
    intro M
    refine le_of_tendsto (hweak (truncBdd (M : ℝ))) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine le_trans (integral_mono (integrable_truncBdd _ _ (hXint n).aestronglyMeasurable _)
      (hXint n) ?_) (hXmean n hn)
    intro w
    show truncBdd (M : ℝ) (X n w) ≤ X n w
    rw [truncBdd_apply]
    have hw : 0 ≤ X n w :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (uOriented_nonneg _ n 0)
    exact max_le hw (min_le_left _ _)
  refine ⟨hnn, ⟨hVm.aestronglyMeasurable, ?_⟩⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hmeasM : ∀ M : ℕ, Measurable
      (fun ω => ENNReal.ofReal (truncBdd (M : ℝ) (V ω))) := fun M =>
    ENNReal.measurable_ofReal.comp ((truncBdd (M : ℝ)).continuous.measurable.comp hVm)
  have hmono : Monotone (fun M : ℕ => fun ω => ENNReal.ofReal (truncBdd (M : ℝ) (V ω))) := by
    intro M N hMN ω
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [truncBdd_apply]
    have : min (V ω) (M : ℝ) ≤ min (V ω) (N : ℝ) :=
      min_le_min le_rfl (by exact_mod_cast hMN)
    exact max_le_max le_rfl this
  have hkey : ∫⁻ ω, ‖V ω‖ₑ ∂Q
      = ⨆ M : ℕ, ∫⁻ ω, ENNReal.ofReal (truncBdd (M : ℝ) (V ω)) ∂Q := by
    rw [← lintegral_iSup hmeasM hmono]
    refine lintegral_congr_ae ?_
    filter_upwards [hnn] with ω hω
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hω]
    exact (iSup_ofReal_truncBdd hω).symm
  rw [hkey]
  refine lt_of_le_of_lt (iSup_le fun M => ?_) (ENNReal.ofReal_lt_top (r := D))
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_truncBdd Q V hVm.aestronglyMeasurable _)
    (Filter.Eventually.of_forall fun ω => le_max_left _ _)]
  exact ENNReal.ofReal_le_ofReal (htrunc M)

/-- **`prop:oriented-scaling` from its three analytic clauses.**  The measurability of the
limiting value, the convergence in distribution and the self-similarity give the whole
proposition; the integrability of the limit, the identification and the positivity of `μ`
and the convergence of the rescaled means are proved here. -/
theorem oriented_scaling_of_weak (ν : Measure ℤ) (hν : CriticalLaw ν)
    (Ω : Type) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (hQ : IsProbabilityMeasure Q)
    (Uc : ℝ → Ω → ℝ)
    (hmeas : ∀ T : ℝ, 0 < T → Measurable (Uc T))
    (hlaw : ∀ T : ℝ, 0 < T → ∀ F : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ => ∫ w, F ((n : ℝ) ^ (-(1 : ℝ) / 4) *
            uOriented (fun y => (w.1 y : ℝ)) ⌊(n : ℝ) * T⌋₊ 0)
          ∂(orientedLaw 2 ν)) atTop (𝓝 (∫ ω, F (Uc T ω) ∂Q)))
    (hself : ∀ T : ℝ, 0 < T → Q.map (Uc T) = Q.map fun ω => T ^ ((1 : ℝ) / 4) * Uc 1 ω) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
      (Uc : ℝ → Ω → ℝ) (μ : ℝ),
      (∀ T : ℝ, 0 < T → Measurable (Uc T)) ∧
      (∀ T : ℝ, 0 < T → ∀ F : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n : ℕ => ∫ w, F ((n : ℝ) ^ (-(1 : ℝ) / 4) *
              uOriented (fun y => (w.1 y : ℝ)) ⌊(n : ℝ) * T⌋₊ 0)
            ∂(orientedLaw 2 ν)) atTop (𝓝 (∫ ω, F (Uc T ω) ∂Q))) ∧
      (∀ T : ℝ, 0 < T → Q.map (Uc T) = Q.map fun ω => T ^ ((1 : ℝ) / 4) * Uc 1 ω) ∧
      Integrable (Uc 1) Q ∧ μ = ∫ ω, Uc 1 ω ∂Q ∧ 0 < μ ∧
      Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 4) *
        meanuOriented (orientedLaw 2 ν) n) atTop (𝓝 μ) := by
  haveI := hν.prob
  haveI := hQ
  haveI : IsProbabilityMeasure (orientedLaw 2 ν) := orientedLaw_isProbability (by norm_num) ν
  obtain ⟨hnn, hint⟩ :=
    integrable_limit_of_weak ν hν Q (Uc 1) (hmeas 1 one_pos) (hlaw 1 one_pos)
  have hlim := meanuOriented_tendsto_of_weak ν hν Q (Uc 1)
    (hmeas 1 one_pos).aestronglyMeasurable hint (hlaw 1 one_pos)
  obtain ⟨c, hc, hlo⟩ :=
    exists_meanuOriented_two_lower ν hν.nonconst hν.integrable_abs hν.mean
  have hpos : 0 < ∫ ω, Uc 1 ω ∂Q := by
    refine lt_of_lt_of_le hc (ge_of_tendsto hlim ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hA : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg hn0.le _
    have hfin : (n : ℝ) ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4) = 1 := by
      rw [← Real.rpow_add hn0]; norm_num
    calc c = c * ((n : ℝ) ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4)) := by
          rw [hfin, mul_one]
      _ = (n : ℝ) ^ (-(1 : ℝ) / 4) * (c * (n : ℝ) ^ ((1 : ℝ) / 4)) := by ring
      _ ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) * meanuOriented (orientedLaw 2 ν) n :=
          mul_le_mul_of_nonneg_left (hlo n) hA
  exact ⟨Ω, mΩ, Q, hQ, Uc, ∫ ω, Uc 1 ω ∂Q, hmeas, hlaw, hself, hint, rfl, hpos, hlim⟩

end Parking
end
