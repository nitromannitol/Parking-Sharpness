/- The mean clause of `prop:oriented-scaling` from its convergence-in-distribution clause.

The proposition (`parking.tex:3151-3159`) asserts both that `n^{-1/4} u⃗_{⌊nT⌋}(0)`
converges in distribution and that `n^{-1/4} E u⃗_n(0) → μ`, the mean of the limit.
Convergence in distribution does not give convergence of means by itself.  What supplies
it is the uniform `L^r` bound of Step 2 at a fixed `r > 4`: the rescaled odometer is
bounded in `L^8` uniformly in the number of rounds, and a family bounded in `L^r` for one
`r > 1` is uniformly integrable, so its means converge along with its laws.
-/
import Parking.Support.MeanUniformInt
import Parking.Support.OrientedDivisibleMoment
import Parking.Support.OrientedDivisibleIntegrable
import Parking.Support.OrientedLaw
import Parking.Support.OrientedTwoMean
import Parking.Support.ScalParabolicScaling

noncomputable section
namespace Parking
open MeasureTheory Filter Topology LatticeProb

/-- The rescaled directed divisible odometer at the origin is integrable, has a finite
eighth moment, and that moment is bounded uniformly in the number of rounds.  This is the
uniform integrability behind the mean clause of `prop:oriented-scaling`. -/
theorem exists_rescaled_uOriented_eighth (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      Integrable (fun ω : Data 2 =>
        (n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (fun y => (ω.1 y : ℝ)) n 0) (orientedLaw 2 ν) ∧
      Integrable (fun ω : Data 2 =>
        ((n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (fun y => (ω.1 y : ℝ)) n 0) ^ (8 : ℝ))
        (orientedLaw 2 ν) ∧
      ∫ ω : Data 2, ((n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (fun y => (ω.1 y : ℝ)) n 0) ^ (8 : ℝ)
        ∂(orientedLaw 2 ν) ≤ C := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (orientedLaw 2 ν) := orientedLaw_isProbability (by norm_num) ν
  obtain ⟨θ, hθ, hexp⟩ := hν.expMoment
  have hmom8 : Integrable (fun k : ℤ => |(k : ℝ)| ^ (8 : ℝ)) ν := by
    obtain ⟨K, hK, hbd⟩ := rpow_le_const_mul_exp (by norm_num : (0:ℝ) ≤ (8:ℝ)) hθ
    refine Integrable.mono' (hexp.const_mul K)
      (measurable_from_countable' (fun k : ℤ => |(k : ℝ)| ^ (8 : ℝ))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact hbd _ (abs_nonneg _)
  have hμmom : Integrable (fun z : ℝ => |z| ^ (8:ℝ)) (realLaw ν) :=
    (realLaw_integrable_iff ν (measurable_abs.pow_const (8:ℝ))).mpr hmom8
  have hμmean : ∫ z : ℝ, z ∂(realLaw ν) = 0 :=
    (realLaw_integral ν measurable_id).trans hν.mean
  obtain ⟨C, hC, hu⟩ :=
    exists_uOriented_two_moment (realLaw ν) 8 (by norm_num) hμmom hμmean
  have hint8 : ∀ n : ℕ, Integrable
      (fun ω : Data 2 => uOriented (fun y => (ω.1 y : ℝ)) n 0 ^ (8:ℝ)) (orientedLaw 2 ν) := by
    intro n
    have h := integrable_oriented_uOriented_rpow (d := 2) (by norm_num) ν hν
      (by norm_num : (1:ℝ) ≤ (8:ℝ)) n 0
    simpa only [abs_of_nonneg (uOriented_nonneg _ n 0)] using h
  have hint1 : ∀ n : ℕ, Integrable
      (fun ω : Data 2 => uOriented (fun y => (ω.1 y : ℝ)) n 0) (orientedLaw 2 ν) := by
    intro n
    have h := integrable_oriented_uOriented_rpow (d := 2) (by norm_num) ν hν
      (le_refl (1:ℝ)) n 0
    simpa only [Real.rpow_one, abs_of_nonneg (uOriented_nonneg _ n 0)] using h
  have htrans : ∀ n : ℕ,
      (∫ ω : Data 2, |uOriented (fun y => (ω.1 y : ℝ)) n 0| ^ (8:ℝ) ∂(orientedLaw 2 ν))
        = ∫ η, |uOriented η n 0| ^ (8:ℝ) ∂(iidLaw 2 (realLaw ν)) := by
    intro n
    exact integral_oriented_confReal (by norm_num) ν
      ((measurable_uOriented n 0).abs.pow_const (8:ℝ))
  have hrn : ∀ n : ℕ, rNorm (orientedLaw 2 ν) 8
      (fun ω : Data 2 => uOriented (fun y => (ω.1 y : ℝ)) n 0) ≤ C * (n : ℝ) ^ ((1:ℝ)/4) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : ∀ ω : Data 2, |uOriented (fun y => (ω.1 y : ℝ)) 0 0| ^ (8:ℝ) = 0 := by
        intro ω
        simp [uOriented]
      rw [rNorm]
      simp only [h0, integral_zero, Nat.cast_zero]
      rw [Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num), mul_zero]
    · rw [rNorm, htrans n]
      simpa only [rNorm] using (hu n hn).2
  have hres := rNorm_rescaled_le_of_rNorm_le (orientedLaw 2 ν)
    (fun n (ω : Data 2) => uOriented (fun y => (ω.1 y : ℝ)) n 0) 8 (by norm_num) hC.le hrn
  refine ⟨C ^ (8:ℝ), by positivity, fun n => ⟨(hint1 n).const_mul _, ?_, ?_⟩⟩
  · have hrw : ∀ ω : Data 2,
        ((n : ℝ) ^ (-(1:ℝ)/4) * uOriented (fun y => (ω.1 y : ℝ)) n 0) ^ (8:ℝ)
          = ((n : ℝ) ^ (-(1:ℝ)/4)) ^ (8:ℝ) * uOriented (fun y => (ω.1 y : ℝ)) n 0 ^ (8:ℝ) :=
      fun ω => Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) _) (uOriented_nonneg _ n 0)
    simpa only [hrw] using (hint8 n).const_mul (((n : ℝ) ^ (-(1:ℝ)/4)) ^ (8:ℝ))
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : ∀ ω : Data 2,
          ((0 : ℕ) : ℝ) ^ (-(1:ℝ)/4) * uOriented (fun y => (ω.1 y : ℝ)) 0 0 = 0 := by
        intro ω
        rw [Nat.cast_zero, Real.zero_rpow (by norm_num), zero_mul]
      simp only [h0, Real.zero_rpow (by norm_num : (8:ℝ) ≠ 0), integral_zero]
      positivity
    · have habs : ∀ ω : Data 2,
          |(n : ℝ) ^ (-(1:ℝ)/4) * uOriented (fun y => (ω.1 y : ℝ)) n 0|
            = (n : ℝ) ^ (-(1:ℝ)/4) * uOriented (fun y => (ω.1 y : ℝ)) n 0 :=
        fun ω => abs_of_nonneg
          (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (uOriented_nonneg _ n 0))
      have hI0 : (0:ℝ) ≤ ∫ ω : Data 2,
          |(n : ℝ) ^ (-(1:ℝ)/4) * uOriented (fun y => (ω.1 y : ℝ)) n 0| ^ (8:ℝ)
            ∂(orientedLaw 2 ν) :=
        integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
      have hkey : rNorm (orientedLaw 2 ν) 8
          (fun ω : Data 2 => (n : ℝ) ^ (-(1:ℝ)/4) *
            uOriented (fun y => (ω.1 y : ℝ)) n 0) ≤ C := hres n hn
      rw [rNorm] at hkey
      simp only [habs] at hkey hI0
      have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) hkey (by norm_num : (0:ℝ) ≤ 8)
      rw [← Real.rpow_mul hI0, show ((1:ℝ)/8) * 8 = 1 by norm_num, Real.rpow_one] at hpow
      exact hpow

/-- **The mean clause of `prop:oriented-scaling` from its convergence-in-distribution
clause at `T = 1`.** -/
theorem meanuOriented_tendsto_of_weak (ν : Measure ℤ) (hν : CriticalLaw ν)
    {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (V : Ω → ℝ) (hVm : AEStronglyMeasurable V Q) (hVint : Integrable V Q)
    (hweak : ∀ F : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ => ∫ w : Data 2, F ((n : ℝ) ^ (-(1 : ℝ) / 4) *
            uOriented (fun y => (w.1 y : ℝ)) ⌊(n : ℝ) * (1 : ℝ)⌋₊ 0)
          ∂(orientedLaw 2 ν)) atTop (𝓝 (∫ ω, F (V ω) ∂Q))) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 4) * meanuOriented (orientedLaw 2 ν) n)
      atTop (𝓝 (∫ ω, V ω ∂Q)) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (orientedLaw 2 ν) := orientedLaw_isProbability (by norm_num) ν
  obtain ⟨C, hC, hfacts⟩ := exists_rescaled_uOriented_eighth ν hν
  simp only [mul_one, Nat.floor_natCast] at hweak
  have hmain := tendsto_integral_of_uniform_rpow
    (P := fun _ : ℕ => orientedLaw 2 ν)
    (X := fun (n : ℕ) (w : Data 2) =>
      (n : ℝ) ^ (-(1 : ℝ) / 4) * uOriented (fun y => (w.1 y : ℝ)) n 0)
    (Z := V) hweak
    (fun n => Filter.Eventually.of_forall fun w =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (uOriented_nonneg _ n 0))
    (fun n => (hfacts n).1) hVm hVint 8 C (by norm_num)
    (fun n => (hfacts n).2.1) (fun n => (hfacts n).2.2)
  refine hmain.congr fun n => ?_
  rw [meanuOriented, ← integral_const_mul]

end Parking
end
