/-
The concentration estimate and the moment norm of the sandpile odometer at a
REAL one-site law.

`Parking/Support/UConcBridge.lean` reads `lem:u-concentration` for the INTEGER
field of the parking model, transporting the law through `Int.cast`.  Step 1 of
`lem:mean-horizon` needs the same two statements at the real reference law of
`Parking/Support/ConvexOrder.lean`, and there the transport is not needed at all:
`Parking.External.UConcentration` is already stated for a real one-site law, so
only the kernel bridge (`kSol_kern`, `kGreen_kern`, `supAbs_green`) is applied.

`exists_uNormReal_le` is the real-field transcription of Step 1 of `thm:upper`:
Minkowski's inequality splits the odometer into its mean and its deviation, the
deviation is controlled by the concentration estimate, and the integrability the
splitting needs comes from `Parking/Support/URealMoment.lean` through the bound
`t^r ≤ 1 + t^{⌈r⌉}`.
-/
import Parking.Support.UConcBridge
import Parking.Support.URealMoment

noncomputable section

namespace Parking

open MeasureTheory LatticeProb

variable {d : ℕ}

theorem exists_uConcReal (hd : 1 ≤ d) (hConc : Parking.External.UConcentration)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun z : ℝ => Real.exp (θ * |z|)) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
      (∫ η, |u η n 0 - ∫ η', u η' n 0 ∂(LatticeProb.iidLaw d ν)| ^ r
          ∂(LatticeProb.iidLaw d ν)) ^ (1 / r)
        ≤ C * (Real.sqrt r * l2Norm (green d n) + r * greenMax d n) := by
  obtain ⟨C, hC, hCle⟩ := hConc d hd 1 (kern d) (isLatticeKernel_kern hd) ν inferInstance θ hθ hexp
  refine ⟨C, hC, fun n hn r hr => ?_⟩
  have h := hCle n hn r hr
  rw [kGreen_kern, supAbs_green] at h
  simpa only [kSol_kern] using h

theorem rpow_le_one_add_pow {t : ℝ} (ht : 0 ≤ t) {r : ℝ} (hr : 0 ≤ r) :
    t ^ r ≤ 1 + t ^ (⌈r⌉₊) := by
  by_cases h1 : t ≤ 1
  · have h0 : t ^ r ≤ 1 := Real.rpow_le_one ht h1 hr
    have h2 : (0:ℝ) ≤ t ^ (⌈r⌉₊) := pow_nonneg ht _
    linarith
  · replace h1 : 1 < t := not_le.mp h1
    have hrle : r ≤ (⌈r⌉₊ : ℝ) := Nat.le_ceil r
    have h3 : t ^ r ≤ t ^ ((⌈r⌉₊ : ℝ)) := Real.rpow_le_rpow_of_exponent_le h1.le hrle
    rw [Real.rpow_natCast] at h3
    linarith

theorem integrable_u_rpow_iid (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 0 ≤ r) (hpow : Integrable (fun t : ℝ => max t 0 ^ (⌈r⌉₊)) ν)
    (n : ℕ) (x : Site d) :
    Integrable (fun η : Site d → ℝ => |u η n x| ^ r) (LatticeProb.iidLaw d ν) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => ν))
  have hIp : Integrable (fun η : Site d → ℝ => u η n x ^ (⌈r⌉₊)) (LatticeProb.iidLaw d ν) :=
    integrable_u_pow_iid hd ν _ hpow n x
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hIp)
    (((measurable_u_eval n x).abs.pow_const r).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r),
    abs_of_nonneg (u_nonneg η n x)]
  exact rpow_le_one_add_pow (u_nonneg η n x) hr

/-- **The `r`-th moment norm of the sandpile odometer at a real one-site law.**  The
transcription of Step 1 of `thm:upper` for a real field: the norm is at most the mean
plus the concentration term. -/
theorem exists_uNormReal_le (hd : 1 ≤ d) (hConc : Parking.External.UConcentration)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun z : ℝ => Real.exp (θ * |z|)) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
      (∫ η, |u η n 0| ^ r ∂(LatticeProb.iidLaw d ν)) ^ (1 / r)
        ≤ Parking.External.meanSandpileReal d ν n
          + C * (Real.sqrt r * l2Norm (green d n) + r * greenMax d n) := by
  obtain ⟨C, hC, hCle⟩ := exists_uConcReal hd hConc ν hθ hexp
  refine ⟨C, hC, fun n hn r hr2 => ?_⟩
  have hr1 : (1 : ℝ) ≤ r := by linarith
  have hr0 : (0 : ℝ) < r := by linarith
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => ν))
  set μ : Measure (Site d → ℝ) := LatticeProb.iidLaw d ν with hμ
  set M : ℝ := Parking.External.meanSandpileReal d ν n with hM
  have hM0 : 0 ≤ M := by
    rw [hM, Parking.External.meanSandpileReal]
    exact integral_nonneg fun η => u_nonneg η n 0
  have hmaxpow : Integrable (fun t : ℝ => max t 0 ^ (⌈r⌉₊)) ν := by
    refine Integrable.mono' (integrable_abs_pow_of_exp_moment ν hθ hexp (⌈r⌉₊))
      ((measurable_id.max measurable_const).pow_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_max_right t 0) _)]
    exact pow_le_pow_left₀ (le_max_right t 0) (max_le (le_abs_self t) (abs_nonneg t)) _
  have hIu : Integrable (fun η : Site d → ℝ => |u η n 0| ^ r) μ :=
    integrable_u_rpow_iid hd ν (le_of_lt hr0) hmaxpow n 0
  have hIc : Integrable (fun _ : Site d → ℝ => |M| ^ r) μ := integrable_const _
  have hId : Integrable (fun η : Site d → ℝ => |u η n 0 - M| ^ r) μ := by
    have hdom : Integrable (fun η : Site d → ℝ =>
        2 ^ r * (|u η n 0| ^ r + |M| ^ r)) μ := (hIu.add hIc).const_mul _
    refine Integrable.mono' hdom
      (((measurable_u_eval n 0).sub measurable_const).abs.pow_const r).aestronglyMeasurable
      (Filter.Eventually.of_forall fun η => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r)]
    have habs : |u η n 0 - M| ≤ |u η n 0| + |M| := by
      rw [sub_eq_add_neg]
      exact (abs_add_le _ _).trans (by rw [abs_neg])
    calc |u η n 0 - M| ^ r ≤ (|u η n 0| + |M|) ^ r :=
          Real.rpow_le_rpow (abs_nonneg _) habs (le_of_lt hr0)
      _ ≤ 2 ^ r * (|u η n 0| ^ r + |M| ^ r) :=
          rpow_add_le_two_rpow (abs_nonneg _) (abs_nonneg _) (le_of_lt hr0)
  have hsplit : (fun η : Site d → ℝ => (u η n 0 - M) + M) = fun η : Site d → ℝ => u η n 0 := by
    funext η; ring
  have hIsum : Integrable (fun η : Site d → ℝ => |(u η n 0 - M) + M| ^ r) μ := by
    have heq : ∀ η : Site d → ℝ, (u η n 0 - M) + M = u η n 0 := fun η => by ring
    simpa only [heq] using hIu
  have hmeasD : AEStronglyMeasurable (fun η : Site d → ℝ => u η n 0 - M) μ :=
    ((measurable_u_eval n 0).sub measurable_const).aestronglyMeasurable
  have hmeasC : AEStronglyMeasurable (fun _ : Site d → ℝ => M) μ := aestronglyMeasurable_const
  have hmink := rNorm_add_le μ hr1 hmeasD hmeasC hId hIc hIsum
  rw [hsplit] at hmink
  have hYeq : rNorm μ r (fun η : Site d → ℝ => u η n 0)
      = (∫ η, |u η n 0| ^ r ∂μ) ^ (1 / r) := rfl
  have hDeq : rNorm μ r (fun η : Site d → ℝ => u η n 0 - M)
      = (∫ η, |u η n 0 - M| ^ r ∂μ) ^ (1 / r) := rfl
  have hCeq : rNorm μ r (fun _ : Site d → ℝ => M) = M := by
    rw [rNorm, integral_const, probReal_univ]
    simp only [smul_eq_mul, one_mul, abs_of_nonneg hM0]
    rw [← Real.rpow_mul hM0, mul_one_div_cancel (ne_of_gt hr0), Real.rpow_one]
  rw [hYeq, hDeq, hCeq] at hmink
  refine hmink.trans ?_
  have hkey := hCle n hn r hr2
  have hMeq : (∫ η, u η n 0 ∂μ) = M := rfl
  rw [hMeq] at hkey
  linarith

end Parking

end
