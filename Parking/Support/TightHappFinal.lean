/-
The final assembly of `happ` (`Parking.oriented_scaling_of_cutoff`'s last remaining hypothesis):
for every cutoff level `A : ℕ` and scale `n : ℕ`,

  `∫ w, |n^{-1/4} u⃗_n(0;w) - Y A n w| ∂(orientedLaw 2 ν) ≤ e A`

for a sequence `e : ℕ → ℝ` with `e → 0`.  Three cases:

* `n = 0`: both `n^{-1/4} u⃗_n(0;w)` and `Y A n w` vanish identically (`orientedGridReward`'s own
  prefactor `n^{-1/4}` is the Lean junk value `0` at `n = 0`, and `u⃗_0 = 0` by definition), so the
  difference is exactly `0`.
* `A = 0`, `n ≥ 1`: a crude triangle-inequality bound, via the mean bound of `thm:oriented`
  (`Parking.exists_meanuOriented_two_upper`) for the odometer term and `Parking.
  exists_integral_norm_boxRewardMap_le` (read at `A = 0`) for the `Y` term, both UNIFORM in `n`.
* `A ≥ 1`, `n ≥ 1`: `Parking.abs_rescaled_uOriented_sub_Y_le` (the Dynkin-decomposition
  reduction) bounds the pointwise difference by the bad-event integral of `Parking.
  happBadBound`, whose two terms are closed by Hölder + Jensen (`Parking.
  integral_indicator_orientedMax_le`, `Parking.exists_integral_rNorm_orientedMax_le`, both
  ALREADY sealed) and by `Parking.exists_integral_norm_boxRewardMap_le` respectively, combined
  with the walk's own bad-event tail bound `Parking.measureReal_sup_walkPartialSum_sq_le`.
-/
import Parking.Support.TightHappStopping
import Parking.Support.TightHappJensen
import Parking.Support.TightHappCauchySchwarz
import Parking.Support.OrientedTwoMean
import Parking.Support.OrientedLaw
import Parking.Support.TightYCutoff
import Parking.Support.ConvexOrder
import Parking.Support.OrientedMeanLimit
import Parking.Support.OrientedScalingCutoff
import Parking.Support.TightYConvFinal
import Parking.Support.ConfMoments

open MeasureTheory Filter Topology LatticeProb

noncomputable section

namespace Parking

local instance instMeasurableSpaceRewardBoxTightHappFinal (T A : ℝ) :
    MeasurableSpace C(rewardBox T A, ℝ) := borel _
local instance instBorelSpaceRewardBoxTightHappFinal (T A : ℝ) :
    BorelSpace C(rewardBox T A, ℝ) := ⟨rfl⟩

/-! ### The scale-`0` case: both terms vanish identically -/

theorem orientedGridReward_zero_n (N : ℕ) (η : Site 2 → ℝ) (m j : ℤ) :
    orientedGridReward 0 N η m j = 0 := by
  unfold orientedGridReward
  norm_num

theorem boxRewardMap_zero_n (T : ℝ) (hT : 0 ≤ T) (A : ℝ) (hA : 0 ≤ A) (η : Site 2 → ℝ) :
    boxRewardMap T hT A hA 0 η = 0 := by
  rw [boxRewardMap_eq_boxFieldAssemble]
  simp only [Nat.cast_zero]
  have hVzero : orientedGridReward 0 ⌊(0 : ℝ) * T⌋₊ η = fun m j => 0 :=
    funext fun m => funext fun j => orientedGridReward_zero_n _ η m j
  rw [hVzero]
  ext p
  simp [boxFieldAssemble]

theorem Y_zero_n (A : ℕ) (w : Data 2) : Y A 0 w = 0 := by
  unfold Y
  rw [boxRewardMap_zero_n, orientedCutoffValuePot_zero]

theorem uOriented_confReal_zero_n (w : Data 2) : uOriented (confReal w) 0 0 = 0 := rfl

theorem happ_diff_eq_zero_of_n_zero (A : ℕ) (w : Data 2) :
    (0 : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (confReal w) 0 0 - Y A 0 w = 0 := by
  rw [uOriented_confReal_zero_n, Y_zero_n, mul_zero, sub_zero]

/-! ### The scenery-averaged `L¹` bound on the rescaled odometer, uniform in `n` -/

/-- **`E_w[|n^{-1/4} u⃗_n(0;w)|]` is bounded by a fixed constant, uniform in the scale `n`.** -/
theorem exists_uOriented_L1_bound (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ n : ℕ, ∫ w, |(n : ℝ) ^ (-(1 : ℝ) / 4) *
        uOriented (confReal w) n 0| ∂(orientedLaw 2 ν) ≤ C1 := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (orientedLaw 2 ν) := orientedLaw_isProbability (by norm_num) ν
  obtain ⟨C1, hC1pos, hC1⟩ := exists_meanuOriented_two_upper ν hν.mean 8 (by norm_num)
    (hν.integrable_rpow (by norm_num))
  refine ⟨C1, hC1pos, fun n => ?_⟩
  have hnn : ∀ w : Data 2, 0 ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (confReal w) n 0 :=
    fun w => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (uOriented_nonneg _ n 0)
  have habs : ∫ w, |(n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (confReal w) n 0|
      ∂(orientedLaw 2 ν) = (n : ℝ) ^ (-(1 : ℝ) / 4) * meanuOriented (orientedLaw 2 ν) n := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun w => abs_of_nonneg (hnn w))]
    rw [integral_const_mul]
    rfl
  rw [habs]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero]
    rw [Real.zero_rpow (by norm_num), zero_mul]
    exact hC1pos.le
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hA : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg hn0.le _
    have hfin : (n : ℝ) ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4) = 1 := by
      rw [← Real.rpow_add hn0]; norm_num
    calc (n : ℝ) ^ (-(1 : ℝ) / 4) * meanuOriented (orientedLaw 2 ν) n
        ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) * (C1 * (n : ℝ) ^ ((1 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left (hC1 n hn) hA
      _ = C1 * ((n : ℝ) ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4)) := by ring
      _ = C1 := by rw [hfin, mul_one]

/-! ### The `A = 0`, `n ≥ 1` case: a crude triangle-inequality bound -/

/-- **A fixed, `n`-uniform bound on `happ`'s integral at the cutoff level `A = 0`.** -/
theorem happ_bound_A_zero (ν : Measure ℤ) (hν : CriticalLaw ν) (p : ℝ) (hp : 12 < p) :
    ∃ B0 : ℝ, 0 ≤ B0 ∧ ∀ n : ℕ, 1 ≤ n →
      ∫ w, |(n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (confReal w) n 0 - Y 0 n w|
        ∂(orientedLaw 2 ν) ≤ B0 := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (orientedLaw 2 ν) := orientedLaw_isProbability (by norm_num) ν
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  obtain ⟨C1, hC1pos, hC1⟩ := exists_uOriented_L1_bound ν hν
  obtain ⟨K, hKnn, hKall⟩ := exists_integral_norm_boxRewardMap_le ν hν p hp
  refine ⟨C1 + 2 * K, by positivity, fun n hn => ?_⟩
  obtain ⟨C8, _, hC8all⟩ := exists_rescaled_uOriented_eighth ν hν
  have hXi : Integrable (fun w : Data 2 => (n : ℝ) ^ (-(1 : ℝ) / 4) *
      uOriented (confReal w) n 0) (orientedLaw 2 ν) := (hC8all n).1
  have hYi : Integrable (fun w : Data 2 => Y 0 n w) (orientedLaw 2 ν) := integrable_Y ν hν 0 n
  have hXai : Integrable (fun w : Data 2 => |(n : ℝ) ^ (-(1 : ℝ) / 4) *
      uOriented (confReal w) n 0|) (orientedLaw 2 ν) := hXi.abs
  have hYai : Integrable (fun w : Data 2 => |Y 0 n w|) (orientedLaw 2 ν) := hYi.abs
  have hpointwise : ∀ w : Data 2, |(n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (confReal w) n 0 -
      Y 0 n w| ≤ |(n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (confReal w) n 0| + |Y 0 n w| :=
    fun w => abs_sub_le_abs_add_abs _ _
  have hLHSi : Integrable (fun w : Data 2 => |(n : ℝ) ^ (-(1 : ℝ) / 4) *
      uOriented (confReal w) n 0 - Y 0 n w|) (orientedLaw 2 ν) := (hXi.sub hYi).abs
  have hstep : (∫ w, |(n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (confReal w) n 0 - Y 0 n w|
        ∂(orientedLaw 2 ν)) ≤
      (∫ w, |(n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (confReal w) n 0| ∂(orientedLaw 2 ν)) +
        ∫ w, |Y 0 n w| ∂(orientedLaw 2 ν) := by
    rw [← integral_add hXai hYai]
    exact integral_mono hLHSi (hXai.add hYai) hpointwise
  have hYbound : ∫ w, |Y 0 n w| ∂(orientedLaw 2 ν) ≤ 2 * K := by
    have hYple : ∀ w : Data 2, |Y 0 n w| ≤
        2 * ‖boxRewardMap 1 zero_le_one ((0:ℕ):ℝ) (Nat.cast_nonneg 0) n (confReal w)‖ := by
      intro w
      unfold Y
      exact abs_orientedCutoffValuePot_le zero_le_one (Nat.cast_nonneg 0) n
        (boxRewardMap 1 zero_le_one ((0:ℕ):ℝ) (Nat.cast_nonneg 0) n (confReal w))
    have hGmeas : Measurable (fun η : Site 2 → ℝ =>
        ‖boxRewardMap 1 zero_le_one ((0:ℕ):ℝ) (Nat.cast_nonneg 0) n η‖) :=
      (measurable_boxRewardMap 1 zero_le_one ((0:ℕ):ℝ) (Nat.cast_nonneg 0) n).norm
    obtain ⟨hGi, hKbound⟩ := hKall ((0:ℕ):ℝ) (Nat.cast_nonneg 0) n hn
    have hKbound' : (∫ η, ‖boxRewardMap 1 zero_le_one ((0:ℕ):ℝ) (Nat.cast_nonneg 0) n η‖
        ∂(iidLaw 2 (realLaw ν))) ≤ K := by
      have heq2 : K * (1 + ((0:ℕ):ℝ)) ^ (1 / 2 + 2 / p) = K := by norm_num
      linarith [hKbound, heq2]
    have hbridge : (∫ w, 2 * ‖boxRewardMap 1 zero_le_one ((0:ℕ):ℝ) (Nat.cast_nonneg 0) n (confReal w)‖
        ∂(orientedLaw 2 ν)) = 2 * ∫ η, ‖boxRewardMap 1 zero_le_one ((0:ℕ):ℝ) (Nat.cast_nonneg 0) n η‖
          ∂(iidLaw 2 (realLaw ν)) := by
      rw [integral_const_mul, integral_oriented_confReal (by norm_num) ν hGmeas]
    have hYai2 : Integrable (fun w : Data 2 =>
        2 * ‖boxRewardMap 1 zero_le_one ((0:ℕ):ℝ) (Nat.cast_nonneg 0) n (confReal w)‖) (orientedLaw 2 ν) := by
      have hcomp : Integrable (fun w : Data 2 =>
          ‖boxRewardMap 1 zero_le_one ((0:ℕ):ℝ) (Nat.cast_nonneg 0) n (confReal w)‖) (orientedLaw 2 ν) := by
        have : Integrable (fun η : Site 2 → ℝ =>
            ‖boxRewardMap 1 zero_le_one ((0:ℕ):ℝ) (Nat.cast_nonneg 0) n η‖) (iidLaw 2 (realLaw ν)) := hGi
        have heqI : Integrable ((fun η : Site 2 → ℝ =>
            ‖boxRewardMap 1 zero_le_one ((0:ℕ):ℝ) (Nat.cast_nonneg 0) n η‖) ∘ confReal)
            (orientedLaw 2 ν) := by
          rw [← orientedLaw_map_confReal (by norm_num : (1:ℕ) ≤ 2) ν] at this
          exact this.comp_measurable measurable_confReal
        exact heqI
      exact hcomp.const_mul 2
    calc (∫ w, |Y 0 n w| ∂(orientedLaw 2 ν)) ≤
        ∫ w, 2 * ‖boxRewardMap 1 zero_le_one ((0:ℕ):ℝ) (Nat.cast_nonneg 0) n (confReal w)‖
          ∂(orientedLaw 2 ν) := integral_mono hYai hYai2 hYple
      _ = 2 * ∫ η, ‖boxRewardMap 1 zero_le_one ((0:ℕ):ℝ) (Nat.cast_nonneg 0) n η‖
          ∂(iidLaw 2 (realLaw ν)) := hbridge
      _ ≤ 2 * K := by linarith [hKbound']
  calc (∫ w, |(n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (confReal w) n 0 - Y 0 n w|
        ∂(orientedLaw 2 ν)) ≤
      (∫ w, |(n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (confReal w) n 0| ∂(orientedLaw 2 ν)) +
        ∫ w, |Y 0 n w| ∂(orientedLaw 2 ν) := hstep
    _ ≤ C1 + 2 * K := add_le_add (hC1 n) hYbound

/-! ### The `A ≥ 1`, `n ≥ 1` case: the Hölder/Jensen assembly -/

/-- **A `(1+A)`-polynomial bound on `happ`'s integral, at every cutoff level `A ≥ 1` and every
scale `n ≥ 1`.** -/
theorem happ_bound_A_pos (ν : Measure ℤ) (hν : CriticalLaw ν) (p : ℝ) (hp : 12 < p) :
    ∃ Codom Krwd : ℝ, 0 ≤ Codom ∧ 0 ≤ Krwd ∧ ∀ (A : ℕ), 1 ≤ A → ∀ n : ℕ, 1 ≤ n →
      ∫ w, |(n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (confReal w) n 0 - Y A n w|
        ∂(orientedLaw 2 ν) ≤
        Codom * (1 / (16 * (A : ℝ) ^ 2)) ^ ((7 : ℝ) / 8) +
          Krwd * (1 + (A : ℝ)) ^ (1 / 2 + 2 / p) / (16 * (A : ℝ) ^ 2) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (orientedLaw 2 ν) := orientedLaw_isProbability (by norm_num) ν
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  obtain ⟨Codom, hCodompos, hCodomall⟩ := exists_integral_rNorm_orientedMax_le ν hν
  obtain ⟨Krwd, hKrwdnn, hKrwdall⟩ := exists_integral_norm_boxRewardMap_le ν hν p hp
  refine ⟨Codom, Krwd, hCodompos.le, hKrwdnn, fun A hA1 n hn => ?_⟩
  set Ar : ℝ := (A : ℝ) with hArdef
  have hAr0 : (0 : ℝ) < Ar := by rw [hArdef]; exact_mod_cast hA1
  have hAr0' : (0 : ℝ) ≤ Ar := hAr0.le
  -- The measure bridge from `orientedLaw` to `iidLaw`, and the identification of `Y A n w`.
  have hYAeq : ∀ w : Data 2, Y A n w = orientedCutoffValuePot zero_le_one hAr0' n
      (boxRewardMap 1 zero_le_one Ar hAr0' n (confReal w)) := fun w => rfl
  have hGmeas : Measurable (fun η : Site 2 → ℝ => |(n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented η n 0 -
      orientedCutoffValuePot zero_le_one hAr0' n
        (boxRewardMap 1 zero_le_one Ar hAr0' n η)|) := by
    apply Measurable.abs
    exact (measurable_const.mul (measurable_uOriented n 0)).sub
      ((measurable_orientedCutoffValuePot zero_le_one hAr0' n).comp
        (measurable_boxRewardMap 1 zero_le_one Ar hAr0' n))
  have hbridge : (∫ w, |(n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (confReal w) n 0 - Y A n w|
        ∂(orientedLaw 2 ν)) =
      ∫ η, |(n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented η n 0 -
          orientedCutoffValuePot zero_le_one hAr0' n
            (boxRewardMap 1 zero_le_one Ar hAr0' n η)|
        ∂(iidLaw 2 (realLaw ν)) := by
    rw [← integral_oriented_confReal (by norm_num) ν hGmeas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    show |(n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (confReal w) n 0 - Y A n w| = _
    rw [hYAeq w]
  rw [hbridge]
  -- The pointwise Dynkin-decomposition bound, at every scenery `η`.
  have hpt : ∀ η : Site 2 → ℝ, |(n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented η n 0 -
      orientedCutoffValuePot zero_le_one hAr0' n
        (boxRewardMap 1 zero_le_one Ar hAr0' n η)| ≤
      ∫ p, Set.indicator (walkBad n Ar) (happBadBound hAr0' n η) p ∂(walkLaw 2) :=
    fun η => abs_rescaled_uOriented_sub_Y_le hAr0 n hn η
  -- `orientedMax` depends on the walk only through its first `n` steps, so it (and its `8`-th
  -- power) is integrable unconditionally.
  have hgi1 : ∀ η : Site 2 → ℝ, Integrable (orientedMax (orientedPotential η) n 0) (walkLaw 2) :=
    fun η => integrable_of_finite_dependence (by norm_num) n _
      (fun p q hpq => orientedMax_congr (orientedPotential η) n 0 hpq)
  have hgi8 : ∀ η : Site 2 → ℝ, Integrable
      (fun p => |orientedMax (orientedPotential η) n 0 p| ^ (8 : ℝ)) (walkLaw 2) :=
    fun η => integrable_of_finite_dependence (by norm_num) n _
      (fun p q hpq => by rw [orientedMax_congr (orientedPotential η) n 0 hpq])
  -- Split `happBadBound`'s two terms.
  have hsplit : ∀ η : Site 2 → ℝ, happBadBound hAr0' n η =
      (fun p => (n : ℝ) ^ (-(1 : ℝ) / 4) * orientedMax (orientedPotential η) n 0 p) +
        (fun _ => ‖boxRewardMap 1 zero_le_one Ar hAr0' n η‖) := by
    intro η; funext p; rfl
  have hindsplit : ∀ η : Site 2 → ℝ, Set.indicator (walkBad n Ar) (happBadBound hAr0' n η) =
      Set.indicator (walkBad n Ar) (fun p => (n : ℝ) ^ (-(1 : ℝ) / 4) *
          orientedMax (orientedPotential η) n 0 p) +
        Set.indicator (walkBad n Ar) (fun _ => ‖boxRewardMap 1 zero_le_one Ar hAr0' n η‖) := by
    intro η
    rw [hsplit η, Set.indicator_add']
  have hgscale : ∀ η : Site 2 → ℝ, Integrable (fun p => (n : ℝ) ^ (-(1 : ℝ) / 4) *
      orientedMax (orientedPotential η) n 0 p) (walkLaw 2) := fun η => (hgi1 η).const_mul _
  have hscale_split : ∀ η : Site 2 → ℝ,
      (∫ p, Set.indicator (walkBad n Ar) (fun p => (n : ℝ) ^ (-(1 : ℝ) / 4) *
          orientedMax (orientedPotential η) n 0 p) p ∂(walkLaw 2)) =
        (n : ℝ) ^ (-(1 : ℝ) / 4) *
          ∫ p, Set.indicator (walkBad n Ar) (orientedMax (orientedPotential η) n 0) p
            ∂(walkLaw 2) := by
    intro η
    rw [← integral_const_mul]
    congr 1
    funext p
    classical
    rw [Set.indicator_apply, Set.indicator_apply]
    split_ifs <;> ring
  have hintsplit : ∀ η : Site 2 → ℝ,
      (∫ p, Set.indicator (walkBad n Ar) (happBadBound hAr0' n η) p ∂(walkLaw 2)) =
        (n : ℝ) ^ (-(1 : ℝ) / 4) *
            (∫ p, Set.indicator (walkBad n Ar) (orientedMax (orientedPotential η) n 0) p
              ∂(walkLaw 2)) +
          ‖boxRewardMap 1 zero_le_one Ar hAr0' n η‖ * (walkLaw 2).real (walkBad n Ar) := by
    intro η
    have hi1 : Integrable (fun p => Set.indicator (walkBad n Ar) (fun p => (n : ℝ) ^ (-(1 : ℝ) / 4) *
        orientedMax (orientedPotential η) n 0 p) p) (walkLaw 2) :=
      (hgscale η).indicator (measurableSet_walkBad n Ar)
    have hi2 : Integrable (fun p => Set.indicator (walkBad n Ar)
        (fun _ => ‖boxRewardMap 1 zero_le_one Ar hAr0' n η‖) p) (walkLaw 2) :=
      (integrable_const _).indicator (measurableSet_walkBad n Ar)
    calc (∫ p, Set.indicator (walkBad n Ar) (happBadBound hAr0' n η) p ∂(walkLaw 2))
        = ∫ p, (Set.indicator (walkBad n Ar) (fun p => (n : ℝ) ^ (-(1 : ℝ) / 4) *
              orientedMax (orientedPotential η) n 0 p) +
            Set.indicator (walkBad n Ar) (fun _ => ‖boxRewardMap 1 zero_le_one Ar hAr0' n η‖)) p
          ∂(walkLaw 2) := by rw [hindsplit η]
      _ = (∫ p, Set.indicator (walkBad n Ar) (fun p => (n : ℝ) ^ (-(1 : ℝ) / 4) *
              orientedMax (orientedPotential η) n 0 p) p ∂(walkLaw 2)) +
            ∫ p, Set.indicator (walkBad n Ar) (fun _ => ‖boxRewardMap 1 zero_le_one Ar hAr0' n η‖) p
              ∂(walkLaw 2) := integral_add hi1 hi2
      _ = _ := by
          rw [integral_indicator_const _ (measurableSet_walkBad n Ar), smul_eq_mul, hscale_split η,
            mul_comm ((walkLaw 2).real (walkBad n Ar))]
  -- Hölder's inequality bounds the first (odometer-side) term for every `η`.
  have hholder : ∀ η : Site 2 → ℝ, (∫ p, Set.indicator (walkBad n Ar)
      (orientedMax (orientedPotential η) n 0) p ∂(walkLaw 2)) ≤
      ((walkLaw 2).real (walkBad n Ar)) ^ ((7 : ℝ) / 8) *
        rNorm (walkLaw 2) 8 (orientedMax (orientedPotential η) n 0) :=
    fun η => integral_indicator_orientedMax_le hAr0 n η (hgi8 η)
  -- The bad-event tail bound, uniform in `n`.
  have htail : (walkLaw 2).real (walkBad n Ar) ≤ 1 / (16 * Ar ^ 2) :=
    measureReal_sup_walkPartialSum_sq_le n hn hAr0
  have htailnn : (0 : ℝ) ≤ (walkLaw 2).real (walkBad n Ar) := ENNReal.toReal_nonneg
  -- Assemble the pointwise-in-`η` bound.
  have hetabound : ∀ η : Site 2 → ℝ,
      (∫ p, Set.indicator (walkBad n Ar) (happBadBound hAr0' n η) p ∂(walkLaw 2)) ≤
        (n : ℝ) ^ (-(1 : ℝ) / 4) * (((walkLaw 2).real (walkBad n Ar)) ^ ((7 : ℝ) / 8) *
              rNorm (walkLaw 2) 8 (orientedMax (orientedPotential η) n 0)) +
          ‖boxRewardMap 1 zero_le_one Ar hAr0' n η‖ * (walkLaw 2).real (walkBad n Ar) := by
    intro η
    rw [hintsplit η]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (hholder η) (Real.rpow_nonneg (Nat.cast_nonneg n) _)) le_rfl
  -- Integrate the assembled bound over `η`.
  obtain ⟨hrNormInt, hrNormBound⟩ := hCodomall n hn
  obtain ⟨hGnInt, hGnBound⟩ := hKrwdall Ar hAr0' n hn
  have hRHSint : Integrable (fun η : Site 2 → ℝ =>
      (n : ℝ) ^ (-(1 : ℝ) / 4) * (((walkLaw 2).real (walkBad n Ar)) ^ ((7 : ℝ) / 8) *
            rNorm (walkLaw 2) 8 (orientedMax (orientedPotential η) n 0)) +
        ‖boxRewardMap 1 zero_le_one Ar hAr0' n η‖ * (walkLaw 2).real (walkBad n Ar))
      (iidLaw 2 (realLaw ν)) :=
    ((hrNormInt.const_mul _).const_mul _).add (hGnInt.mul_const _)
  have hLHSint : Integrable (fun η : Site 2 → ℝ => |(n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented η n 0 -
      orientedCutoffValuePot zero_le_one hAr0' n
        (boxRewardMap 1 zero_le_one Ar hAr0' n η)|) (iidLaw 2 (realLaw ν)) := by
    refine Integrable.mono' hRHSint hGmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun η => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact (hpt η).trans (hetabound η)
  have hintmono := integral_mono hLHSint hRHSint (fun η => (hpt η).trans (hetabound η))
  have hRHSeq : (∫ η, ((n : ℝ) ^ (-(1 : ℝ) / 4) * (((walkLaw 2).real (walkBad n Ar)) ^ ((7 : ℝ) / 8) *
        rNorm (walkLaw 2) 8 (orientedMax (orientedPotential η) n 0)) +
      ‖boxRewardMap 1 zero_le_one Ar hAr0' n η‖ * (walkLaw 2).real (walkBad n Ar))
      ∂(iidLaw 2 (realLaw ν))) =
      (n : ℝ) ^ (-(1 : ℝ) / 4) * ((walkLaw 2).real (walkBad n Ar)) ^ ((7 : ℝ) / 8) *
          (∫ η, rNorm (walkLaw 2) 8 (orientedMax (orientedPotential η) n 0)
            ∂(iidLaw 2 (realLaw ν))) +
        (∫ η, ‖boxRewardMap 1 zero_le_one Ar hAr0' n η‖ ∂(iidLaw 2 (realLaw ν))) *
          (walkLaw 2).real (walkBad n Ar) := by
    rw [integral_add ((hrNormInt.const_mul _).const_mul _) (hGnInt.mul_const _),
      integral_const_mul, integral_const_mul, integral_mul_const]
    ring
  rw [hRHSeq] at hintmono
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hncancel : (n : ℝ) ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4) = 1 := by
    rw [← Real.rpow_add hn0]; norm_num
  have hterm1 : (n : ℝ) ^ (-(1 : ℝ) / 4) * ((walkLaw 2).real (walkBad n Ar)) ^ ((7 : ℝ) / 8) *
      (∫ η, rNorm (walkLaw 2) 8 (orientedMax (orientedPotential η) n 0)
        ∂(iidLaw 2 (realLaw ν))) ≤ Codom * ((walkLaw 2).real (walkBad n Ar)) ^ ((7 : ℝ) / 8) := by
    have hstep : (n : ℝ) ^ (-(1 : ℝ) / 4) * ((walkLaw 2).real (walkBad n Ar)) ^ ((7 : ℝ) / 8) *
        (∫ η, rNorm (walkLaw 2) 8 (orientedMax (orientedPotential η) n 0)
          ∂(iidLaw 2 (realLaw ν))) ≤
        (n : ℝ) ^ (-(1 : ℝ) / 4) * ((walkLaw 2).real (walkBad n Ar)) ^ ((7 : ℝ) / 8) *
          (Codom * (n : ℝ) ^ ((1 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left hrNormBound (by positivity)
    calc (n : ℝ) ^ (-(1 : ℝ) / 4) * ((walkLaw 2).real (walkBad n Ar)) ^ ((7 : ℝ) / 8) *
          (∫ η, rNorm (walkLaw 2) 8 (orientedMax (orientedPotential η) n 0)
            ∂(iidLaw 2 (realLaw ν))) ≤
        (n : ℝ) ^ (-(1 : ℝ) / 4) * ((walkLaw 2).real (walkBad n Ar)) ^ ((7 : ℝ) / 8) *
          (Codom * (n : ℝ) ^ ((1 : ℝ) / 4)) := hstep
      _ = Codom * ((walkLaw 2).real (walkBad n Ar)) ^ ((7 : ℝ) / 8) *
          ((n : ℝ) ^ (-(1 : ℝ) / 4) * (n : ℝ) ^ ((1 : ℝ) / 4)) := by ring
      _ = Codom * ((walkLaw 2).real (walkBad n Ar)) ^ ((7 : ℝ) / 8) := by rw [hncancel, mul_one]
  have hterm1' : Codom * ((walkLaw 2).real (walkBad n Ar)) ^ ((7 : ℝ) / 8) ≤
      Codom * (1 / (16 * Ar ^ 2)) ^ ((7 : ℝ) / 8) :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow htailnn htail (by norm_num)) hCodompos.le
  have hterm2 : (∫ η, ‖boxRewardMap 1 zero_le_one Ar hAr0' n η‖ ∂(iidLaw 2 (realLaw ν))) *
      (walkLaw 2).real (walkBad n Ar) ≤ Krwd * (1 + Ar) ^ (1 / 2 + 2 / p) / (16 * Ar ^ 2) := by
    have hstep1 : (∫ η, ‖boxRewardMap 1 zero_le_one Ar hAr0' n η‖ ∂(iidLaw 2 (realLaw ν))) *
        (walkLaw 2).real (walkBad n Ar) ≤
        (Krwd * (1 + Ar) ^ (1 / 2 + 2 / p)) * (walkLaw 2).real (walkBad n Ar) :=
      mul_le_mul_of_nonneg_right hGnBound htailnn
    have hstep2 : (Krwd * (1 + Ar) ^ (1 / 2 + 2 / p)) * (walkLaw 2).real (walkBad n Ar) ≤
        (Krwd * (1 + Ar) ^ (1 / 2 + 2 / p)) * (1 / (16 * Ar ^ 2)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    calc (∫ η, ‖boxRewardMap 1 zero_le_one Ar hAr0' n η‖ ∂(iidLaw 2 (realLaw ν))) *
          (walkLaw 2).real (walkBad n Ar) ≤
        (Krwd * (1 + Ar) ^ (1 / 2 + 2 / p)) * (walkLaw 2).real (walkBad n Ar) := hstep1
      _ ≤ (Krwd * (1 + Ar) ^ (1 / 2 + 2 / p)) * (1 / (16 * Ar ^ 2)) := hstep2
      _ = Krwd * (1 + Ar) ^ (1 / 2 + 2 / p) / (16 * Ar ^ 2) := by ring
  calc (∫ η, |(n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented η n 0 -
        orientedCutoffValuePot zero_le_one hAr0' n
          (boxRewardMap 1 zero_le_one Ar hAr0' n η)| ∂(iidLaw 2 (realLaw ν))) ≤
      (n : ℝ) ^ (-(1 : ℝ) / 4) * ((walkLaw 2).real (walkBad n Ar)) ^ ((7 : ℝ) / 8) *
          (∫ η, rNorm (walkLaw 2) 8 (orientedMax (orientedPotential η) n 0)
            ∂(iidLaw 2 (realLaw ν))) +
        (∫ η, ‖boxRewardMap 1 zero_le_one Ar hAr0' n η‖ ∂(iidLaw 2 (realLaw ν))) *
          (walkLaw 2).real (walkBad n Ar) := hintmono
    _ ≤ Codom * (1 / (16 * Ar ^ 2)) ^ ((7 : ℝ) / 8) +
        Krwd * (1 + Ar) ^ (1 / 2 + 2 / p) / (16 * Ar ^ 2) :=
      add_le_add (hterm1.trans hterm1') hterm2
    _ = Codom * (1 / (16 * (A : ℝ) ^ 2)) ^ ((7 : ℝ) / 8) +
        Krwd * (1 + (A : ℝ)) ^ (1 / 2 + 2 / p) / (16 * (A : ℝ) ^ 2) := by rw [hArdef]

/-! ### The final assembly: `happ`, `e`, `he`, and `Parking.oriented_scaling_of_cutoff` -/

/-- **`Parking.oriented_scaling_of_cutoff`'s hypotheses, all closed**, giving
`prop:oriented-scaling` (`parking.tex:3151-3159`) in full. -/
theorem oriented_scaling_assembled
    (hStability : External.OrientedStoppingStability)
    (hBinomial : External.BinomialLocalCLT)
    (ν : Measure ℤ) (hν : CriticalLaw ν) :
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
  obtain ⟨B0, hB0nn, hB0all⟩ := happ_bound_A_zero ν hν 13 (by norm_num)
  obtain ⟨Codom, Krwd, hCodomnn, hKrwdnn, hPosall⟩ := happ_bound_A_pos ν hν 13 (by norm_num)
  set e : ℕ → ℝ := fun A => if A = 0 then B0 else
      Codom * (1 / (16 * (A : ℝ) ^ 2)) ^ ((7 : ℝ) / 8) +
        Krwd * (1 + (A : ℝ)) ^ ((1 : ℝ) / 2 + 2 / 13) / (16 * (A : ℝ) ^ 2) with hedef
  have he0nn : ∀ A : ℕ, 0 ≤ e A := by
    intro A
    simp only [hedef]
    by_cases hA : A = 0
    · simp only [hA, if_pos]; exact hB0nn
    · simp only [hA, if_false]
      positivity
  have he : Tendsto e atTop (𝓝 0) := by
    set e2 : ℝ := (1 : ℝ) / 2 + 2 / 13 with he2def
    have he2pos : 0 < e2 := by rw [he2def]; norm_num
    have he2lt2 : e2 < 2 := by rw [he2def]; norm_num
    have htendsto1 : Tendsto (fun A : ℕ => Codom * (1 / (16 * (A : ℝ) ^ 2)) ^ ((7 : ℝ) / 8))
        atTop (𝓝 0) := by
      have hsq : Tendsto (fun A : ℕ => (A : ℝ) ^ 2) atTop atTop :=
        (tendsto_pow_atTop (n := 2) (by norm_num)).comp tendsto_natCast_atTop_atTop
      have h1 : Tendsto (fun A : ℕ => (16 * (A : ℝ) ^ 2)) atTop atTop :=
        Tendsto.const_mul_atTop (by norm_num) hsq
      have h2 : Tendsto (fun A : ℕ => (1 : ℝ) / (16 * (A : ℝ) ^ 2)) atTop (𝓝 0) := by
        have heq : (fun A : ℕ => (1 : ℝ) / (16 * (A : ℝ) ^ 2)) =
            (fun A : ℕ => 16 * (A : ℝ) ^ 2)⁻¹ := by
          funext A; rw [Pi.inv_apply, inv_eq_one_div]
        rw [heq]
        exact h1.inv_tendsto_atTop
      have h3 : Tendsto (fun A : ℕ => (1 / (16 * (A : ℝ) ^ 2)) ^ ((7 : ℝ) / 8)) atTop (𝓝 0) :=
        h2.rpow_const_nhds_zero (by norm_num)
      simpa using h3.const_mul Codom
    have htendsto2 : Tendsto (fun A : ℕ => Krwd * (1 + (A : ℝ)) ^ e2 / (16 * (A : ℝ) ^ 2))
        atTop (𝓝 0) := by
      have hpow : Tendsto (fun A : ℕ => (A : ℝ) ^ (e2 - 2)) atTop (𝓝 0) := by
        have hy : (0 : ℝ) < 2 - e2 := by linarith
        have h0 := tendsto_rpow_neg_atTop hy
        have heq : (fun x : ℝ => x ^ (-(2 - e2))) = fun x : ℝ => x ^ (e2 - 2) := by
          funext x; congr 1; ring
        rw [heq] at h0
        exact h0.comp tendsto_natCast_atTop_atTop
      have hupper : ∀ᶠ A : ℕ in atTop, Krwd * (1 + (A : ℝ)) ^ e2 / (16 * (A : ℝ) ^ 2) ≤
          (Krwd * (2 : ℝ) ^ e2 / 16) * (A : ℝ) ^ (e2 - 2) := by
        filter_upwards [Filter.eventually_ge_atTop 1] with A hA1
        have hA1' : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA1
        have hA0 : (0 : ℝ) < (A : ℝ) := by linarith
        have hbound : (1 + (A : ℝ)) ^ e2 ≤ (2 * (A : ℝ)) ^ e2 :=
          Real.rpow_le_rpow (by linarith) (by linarith) he2pos.le
        have hexpand : (2 * (A : ℝ)) ^ e2 = 2 ^ e2 * (A : ℝ) ^ e2 :=
          Real.mul_rpow (by norm_num) hA0.le
        have hAe2 : (A : ℝ) ^ e2 = (A : ℝ) ^ (2 : ℝ) * (A : ℝ) ^ (e2 - 2) := by
          rw [← Real.rpow_add hA0]; congr 1; ring
        have hAsq : (A : ℝ) ^ (2 : ℝ) = (A : ℝ) ^ 2 := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        have hrhs_eq : (Krwd * (2 : ℝ) ^ e2 / 16) * (A : ℝ) ^ (e2 - 2) =
            Krwd * ((2 * (A : ℝ)) ^ e2) / (16 * (A : ℝ) ^ 2) := by
          rw [hexpand, hAe2, hAsq]; field_simp
        rw [hrhs_eq]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbound hKrwdnn) (by positivity)
      have hlower : ∀ᶠ A : ℕ in atTop, (0 : ℝ) ≤
          Krwd * (1 + (A : ℝ)) ^ e2 / (16 * (A : ℝ) ^ 2) := by
        filter_upwards with A
        positivity
      exact squeeze_zero' hlower hupper (by simpa using hpow.const_mul (Krwd * (2 : ℝ) ^ e2 / 16))
    have hcomb : Tendsto (fun A : ℕ => Codom * (1 / (16 * (A : ℝ) ^ 2)) ^ ((7 : ℝ) / 8) +
        Krwd * (1 + (A : ℝ)) ^ e2 / (16 * (A : ℝ) ^ 2)) atTop (𝓝 0) := by
      have := htendsto1.add htendsto2
      simpa using this
    refine hcomb.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with A hA
    simp only [hedef, if_neg hA.ne']
  have happ : ∀ A n : ℕ, ∫ w, |(n : ℝ) ^ (-(1 : ℝ) / 4) *
      uOriented (fun y => (w.1 y : ℝ)) n 0 - Y A n w| ∂(orientedLaw 2 ν) ≤ e A := by
    intro A n
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · have heq0 : (fun w : Data 2 => |((0 : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) *
          uOriented (fun y => (w.1 y : ℝ)) 0 0 - Y A 0 w|) = fun _ => 0 := by
        funext w
        have hd : (0 : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (confReal w) 0 0 - Y A 0 w = 0 :=
          happ_diff_eq_zero_of_n_zero A w
        have heqc : (fun y => (w.1 y : ℝ)) = confReal w := rfl
        rw [heqc]
        simp only [Nat.cast_zero]
        rw [hd]
        simp
      rw [heq0]
      simp only [integral_const, smul_eq_mul, mul_zero]
      exact he0nn A
    · rcases Nat.eq_zero_or_pos A with rfl | hApos
      · simp only [hedef, if_pos rfl]
        have hb := hB0all n hnpos
        have heqc : (fun w : Data 2 => |(n : ℝ) ^ (-(1 : ℝ) / 4) *
            uOriented (fun y => (w.1 y : ℝ)) n 0 - Y 0 n w|) =
            (fun w : Data 2 => |(n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (confReal w) n 0 -
              Y 0 n w|) := rfl
        rw [heqc]
        exact hb
      · simp only [hedef, if_neg hApos.ne']
        have hb := hPosall A hApos n hnpos
        have hbridge2 : (∫ w, |(n : ℝ) ^ (-(1 : ℝ) / 4) *
              uOriented (fun y => (w.1 y : ℝ)) n 0 - Y A n w| ∂(orientedLaw 2 ν)) =
            ∫ w, |(n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (confReal w) n 0 - Y A n w|
              ∂(orientedLaw 2 ν) := rfl
        rw [hbridge2]
        exact hb
  exact oriented_scaling_of_cutoff ν hν Y measurable_Y (fun A n => integrable_Y ν hν A n) e he happ
    (hYconv_unconditional ν hν hBinomial hStability)

end Parking

end
