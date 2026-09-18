/-
The concentration estimate of `lem:u-concentration` read for the parking model.

`Parking.External.UConcentration` is stated for a general finite-range
translation-invariant kernel and a one-site law on `ℝ`, while the parking
configuration is integer valued and its law is `Parking.law d ν` with `ν` a
measure on `ℤ`.  Two bridges close the gap.  The kernel is identified with the
transition kernel of the simple random walk in
`Parking/Support/KernelBridge.lean`.  The law is transported here: the
configuration of a realization, read as a real field, has the law
`iidLaw d (ν.map Int.cast)` under `Parking.law d ν`, because pushing an
independent family forward coordinate by coordinate pushes the one-site law
forward (`MeasureTheory.Measure.infinitePi_map_pi`).

The output is `Parking.exists_uNorm_le`: the `r`-th moment norm of `u_n(0)` is
at most its mean plus `C(√r ‖g_n‖₂ + r max_x g_n(x))`, which is what Step 1 of
`thm:upper` is combined with.
-/
import Parking.Support.UpperProof
import Parking.External.UConcentration

noncomputable section

namespace Parking

open MeasureTheory LatticeProb

variable {d : ℕ}

/-! ### The configuration as a real field -/

/-- The configuration of a realization, read in the reals. -/
def confReal (ω : Data d) : Site d → ℝ := fun y => ((ω.1 y : ℤ) : ℝ)

theorem measurable_intCastReal : Measurable (fun k : ℤ => (k : ℝ)) :=
  measurable_from_countable' _

theorem measurable_confReal : Measurable (fun ω : Data d => confReal ω) :=
  measurable_pi_lambda _ fun y =>
    measurable_intCastReal.comp ((measurable_pi_apply y).comp measurable_fst)

theorem uOf_eq_u_confReal (ω : Data d) (n : ℕ) (x : Site d) :
    uOf ω n x = u (confReal ω) n x := rfl

/-- **The law of the configuration read in the reals.**  Pushing an independent
family forward coordinate by coordinate pushes the one-site law forward. -/
theorem law_map_confReal (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    (law d ν).map (fun ω : Data d => confReal ω)
      = LatticeProb.iidLaw d (ν.map (fun k : ℤ => (k : ℝ))) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => ν))
  have hcomp : (fun ω : Data d => confReal ω)
      = (fun η : Site d → ℤ => fun y => ((η y : ℤ) : ℝ)) ∘ (Prod.fst : Data d → (Site d → ℤ)) :=
    rfl
  have hmeas : Measurable (fun η : Site d → ℤ => fun y => ((η y : ℤ) : ℝ)) :=
    measurable_pi_lambda _ fun y => measurable_intCastReal.comp (measurable_pi_apply y)
  have hfst : (law d ν).map (Prod.fst : Data d → (Site d → ℤ)) = LatticeProb.iidLaw d ν :=
    dataLaw_map_fst hd (LatticeProb.iidLaw d ν)
  rw [hcomp, ← Measure.map_map hmeas measurable_fst, hfst, LatticeProb.iidLaw,
    LatticeProb.iidLaw]
  exact Measure.infinitePi_map_pi _ (fun _ : Site d => measurable_intCastReal)

/-- Integrating a function of the configuration alone, in the reals. -/
theorem integral_confReal (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {G : (Site d → ℝ) → ℝ} (hG : Measurable G) :
    ∫ ω, G (confReal ω) ∂(law d ν)
      = ∫ η, G η ∂(LatticeProb.iidLaw d (ν.map (fun k : ℤ => (k : ℝ)))) := by
  have h := integral_map (μ := law d ν) (φ := fun ω : Data d => confReal ω) (f := G)
    measurable_confReal.aemeasurable hG.aestronglyMeasurable
  rw [law_map_confReal hd ν] at h
  exact h.symm

/-! ### The sup norm of the Green function is its maximum -/

theorem supAbs_green (d : ℕ) (n : ℕ) : supAbs (green d n) = greenMax d n := by
  have habs : ∀ x : Site d, |green d n x| = green d n x :=
    fun x => abs_of_nonneg (green_nonneg n x)
  simp only [supAbs, greenMax, habs]

/-! ### The transported concentration estimate -/

theorem exists_uConc (hd : 1 ≤ d) (hConc : Parking.External.UConcentration)
    (ν : Measure ℤ) [IsProbabilityMeasure ν] {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
      (∫ ω, |uOf ω n 0 - meanu (law d ν) n| ^ r ∂(law d ν)) ^ (1 / r)
        ≤ C * (Real.sqrt r * l2Norm (green d n) + r * greenMax d n) := by
  set ν' : Measure ℝ := ν.map (fun k : ℤ => (k : ℝ)) with hν'
  haveI : IsProbabilityMeasure ν' := by
    rw [hν']
    exact Measure.isProbabilityMeasure_map measurable_intCastReal.aemeasurable
  have hexp' : Integrable (fun z : ℝ => Real.exp (θ * |z|)) ν' := by
    rw [hν']
    refine (integrable_map_measure ?_ measurable_intCastReal.aemeasurable).mpr hexp
    exact (Real.measurable_exp.comp (measurable_abs.const_mul θ)).aestronglyMeasurable
  obtain ⟨C, hC, hCle⟩ := hConc d hd 1 (kern d) (isLatticeKernel_kern hd) ν'
    inferInstance θ hθ hexp'
  refine ⟨C, hC, fun n hn r hr2 => ?_⟩
  have hmeanu : meanu (law d ν) n
      = ∫ η, kSol 1 (kern d) η n 0 ∂(LatticeProb.iidLaw d ν') := by
    rw [meanu]
    have hfun : (fun ω : Data d => uOf ω n 0)
        = fun ω : Data d => (fun η : Site d → ℝ => u η n 0) (confReal ω) := rfl
    rw [hfun, integral_confReal hd ν (measurable_u_eval n 0)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun η => by
      simp only [kSol_kern])
  have hint : (∫ ω, |uOf ω n 0 - meanu (law d ν) n| ^ r ∂(law d ν))
      = ∫ η, |kSol 1 (kern d) η n 0
          - ∫ η', kSol 1 (kern d) η' n 0 ∂(LatticeProb.iidLaw d ν')| ^ r
        ∂(LatticeProb.iidLaw d ν') := by
    rw [← hmeanu]
    have hfun : (fun ω : Data d => |uOf ω n 0 - meanu (law d ν) n| ^ r)
        = fun ω : Data d =>
          (fun η : Site d → ℝ => |u η n 0 - meanu (law d ν) n| ^ r) (confReal ω) := rfl
    rw [hfun, integral_confReal hd ν
      (G := fun η : Site d → ℝ => |u η n 0 - meanu (law d ν) n| ^ r)
      (((measurable_u_eval n 0).sub measurable_const).abs.pow_const r)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun η => by
      simp only [kSol_kern])
  rw [hint]
  have h := hCle n hn r hr2
  rwa [kGreen_kern, supAbs_green] at h

/-! ### The `r`-th moment norm of the sandpile odometer -/

theorem exists_uNorm_le (hd : 1 ≤ d) (hConc : Parking.External.UConcentration)
    (ν : Measure ℤ) [IsProbabilityMeasure ν] {θ : ℝ} (hθ : 0 < θ)
    (hexpabs : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
      (∫ ω, |uOf ω n 0| ^ r ∂(law d ν)) ^ (1 / r)
        ≤ meanu (law d ν) n
          + C * (Real.sqrt r * l2Norm (green d n) + r * greenMax d n) := by
  obtain ⟨C, hC, hCle⟩ := exists_uConc hd hConc ν hθ hexpabs
  refine ⟨C, hC, fun n hn r hr2 => ?_⟩
  have hr1 : (1 : ℝ) ≤ r := by linarith
  have hr0 : (0 : ℝ) < r := by linarith
  haveI := stackRankLaw_isProbability (d := d) hd
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => ν))
  haveI hlawP : IsProbabilityMeasure (law d ν) :=
    inferInstanceAs (IsProbabilityMeasure ((LatticeProb.iidLaw d ν).prod (stackRankLaw d)))
  set μ : Measure (Data d) := law d ν with hμ
  haveI : IsProbabilityMeasure μ := hlawP
  set M : ℝ := meanu μ n with hM
  have hM0 : 0 ≤ M := by
    rw [hM, meanu]
    exact integral_nonneg fun ω => uOf_nonneg ω n 0
  have hIu : Integrable (fun ω : Data d => |uOf ω n 0| ^ r) μ :=
    integrable_uOf_rpow hd ν hθ hexp hr1 n 0
  have hIc : Integrable (fun ω : Data d => |M| ^ r) μ := integrable_const _
  have hId : Integrable (fun ω : Data d => |uOf ω n 0 - M| ^ r) μ := by
    have hdom : Integrable (fun ω : Data d =>
        2 ^ r * (|uOf ω n 0| ^ r + |M| ^ r)) μ := (hIu.add hIc).const_mul _
    refine Integrable.mono' hdom
      (((measurable_uOf n 0).sub measurable_const).abs.pow_const r).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r)]
    have habs : |uOf ω n 0 - M| ≤ |uOf ω n 0| + |M| := by
      rw [sub_eq_add_neg]
      exact (abs_add_le _ _).trans (by rw [abs_neg])
    calc |uOf ω n 0 - M| ^ r ≤ (|uOf ω n 0| + |M|) ^ r :=
          Real.rpow_le_rpow (abs_nonneg _) habs (le_of_lt hr0)
      _ ≤ 2 ^ r * (|uOf ω n 0| ^ r + |M| ^ r) :=
          rpow_add_le_two_rpow (abs_nonneg _) (abs_nonneg _) (le_of_lt hr0)
  have hsplit : (fun ω : Data d => (uOf ω n 0 - M) + M) = fun ω : Data d => uOf ω n 0 := by
    funext ω; ring
  have hIsum : Integrable (fun ω : Data d => |(uOf ω n 0 - M) + M| ^ r) μ := by
    have heq : ∀ ω : Data d, (uOf ω n 0 - M) + M = uOf ω n 0 := fun ω => by ring
    simpa only [heq] using hIu
  have hmeasD : AEStronglyMeasurable (fun ω : Data d => uOf ω n 0 - M) μ :=
    ((measurable_uOf n 0).sub measurable_const).aestronglyMeasurable
  have hmeasC : AEStronglyMeasurable (fun _ : Data d => M) μ := aestronglyMeasurable_const
  have hmink := rNorm_add_le μ hr1 hmeasD hmeasC hId hIc hIsum
  rw [hsplit] at hmink
  have hYeq : rNorm μ r (fun ω : Data d => uOf ω n 0)
      = (∫ ω, |uOf ω n 0| ^ r ∂μ) ^ (1 / r) := rfl
  have hDeq : rNorm μ r (fun ω : Data d => uOf ω n 0 - M)
      = (∫ ω, |uOf ω n 0 - M| ^ r ∂μ) ^ (1 / r) := rfl
  have hCeq : rNorm μ r (fun _ : Data d => M) = M := by
    rw [rNorm, integral_const, probReal_univ]
    simp only [smul_eq_mul, one_mul, abs_of_nonneg hM0]
    rw [← Real.rpow_mul hM0, mul_one_div_cancel (ne_of_gt hr0), Real.rpow_one]
  rw [hYeq, hDeq, hCeq] at hmink
  refine hmink.trans ?_
  have := hCle n hn r hr2
  linarith

end Parking

end
