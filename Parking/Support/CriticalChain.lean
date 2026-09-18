/-
`cor:critical` (`parking.tex:1339-1352`) reduced to `lem:critical-density`.

The corollary's proof is two lines: `thm:comparison` gives `E U_n(0) ≥ E u_n(0)`
and `lem:critical-density` gives `E U_n(0) ≥ c log n - C`.  What the first line
needs beyond the SEALED `thm:comparison`, which is the pathwise inequality
`u_n(x) ≤ E[U_n(x) | η]`, is the two Fubini identities that turn it into an
inequality of means: the data is a product of the configuration with the stacks
and the uniform variables, the sandpile odometer reads only the configuration,
and the mean of the particle odometer is the mean of its conditional mean.  Both
integrands are integrable under a first moment alone, the particle odometer
because it is at most the sum of the configuration over the boxes it has grown
through and the sandpile odometer because it is at most `n` times the
configuration summed over the box of radius `n`.

The reduction is stated so that `cor:critical` follows from `lem:critical-density`
by application, with nothing left over.
-/
import Parking.Frozen.Comparison
import Parking.Frozen.Transport
import Parking.Support.UBound
import Parking.Support.CriticalReduction
import Parking.Support.Invariance

noncomputable section

open MeasureTheory Filter

namespace Parking

open LatticeProb

variable {d : ℕ}

/-! ### Integrability under a first moment -/

/-- The sandpile odometer is integrable when the one-site law has a first
moment: it is at most `n` times the configuration summed over the box of radius
`n`. -/
theorem integrable_uOf (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (n : ℕ) (x : Site d) :
    Integrable (fun ω : Data d => uOf ω n x) (law d ν) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hti : TranslationInvariant (LatticeProb.iidLaw d ν) :=
    fun v => iidLaw_map_shiftConf' ν v
  have hint0 : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) (LatticeProb.iidLaw d ν) := by
    have hmap : (LatticeProb.iidLaw d ν).map (fun η : Site d → ℤ => η 0) = ν := by
      show (MeasureTheory.Measure.infinitePi fun _ : Site d => ν).map
        (fun η : Site d → ℤ => η 0) = ν
      exact Measure.infinitePi_map_eval _ 0
    refine (integrable_map_measure (g := fun k : ℤ => |(k : ℝ)|)
      (f := fun η : Site d → ℤ => η 0) (μ := LatticeProb.iidLaw d ν) ?_
      (measurable_pi_apply (0 : Site d)).aemeasurable).mp ?_
    · rw [hmap]; exact hint.aestronglyMeasurable
    · rw [hmap]; exact hint
  have hdom : Integrable (fun ω : Data d => (n : ℝ) * confBox ω x n) (law d ν) :=
    (integrable_boxSum hd hti hint0 x n).const_mul _
  refine Integrable.mono' hdom ((measurable_uOf n x).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (uOf_nonneg ω n x)]
  exact uOf_le_confBox hd ω n x

/-- The particle odometer is integrable when the one-site law has a first
moment. -/
theorem integrable_U_law (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (n : ℕ) (x : Site d) :
    Integrable (fun ω : Data d => (U ω n x : ℝ)) (law d ν) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hti : TranslationInvariant (LatticeProb.iidLaw d ν) :=
    fun v => iidLaw_map_shiftConf' ν v
  have hint0 : Integrable (fun η : Site d → ℤ => |((η 0 : ℤ) : ℝ)|) (LatticeProb.iidLaw d ν) := by
    have hmap : (LatticeProb.iidLaw d ν).map (fun η : Site d → ℤ => η 0) = ν := by
      show (MeasureTheory.Measure.infinitePi fun _ : Site d => ν).map
        (fun η : Site d → ℤ => η 0) = ν
      exact Measure.infinitePi_map_eval _ 0
    refine (integrable_map_measure (g := fun k : ℤ => |(k : ℝ)|)
      (f := fun η : Site d → ℤ => η 0) (μ := LatticeProb.iidLaw d ν) ?_
      (measurable_pi_apply (0 : Site d)).aemeasurable).mp ?_
    · rw [hmap]; exact hint.aestronglyMeasurable
    · rw [hmap]; exact hint
  exact integrable_U_data hd hti hint0 n x

/-! ### The two Fubini identities -/

/-- The mean particle odometer is the mean of its conditional mean. -/
theorem meanU_eq_integral_meanUgiven (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (n : ℕ) :
    meanU (law d ν) n = ∫ η, meanUgiven d η n 0 ∂(LatticeProb.iidLaw d ν) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI := stackRankLaw_isProbability (d := d) hd
  have hlaw : law d ν = (LatticeProb.iidLaw d ν).prod (stackRankLaw d) := rfl
  have hI : Integrable (fun ω : Data d => (U ω n 0 : ℝ))
      ((LatticeProb.iidLaw d ν).prod (stackRankLaw d)) := by
    rw [← hlaw]; exact integrable_U_law hd ν hint n 0
  show ∫ ω, (U ω n 0 : ℝ) ∂(law d ν) = _
  rw [hlaw, integral_prod _ hI]
  rfl

/-- The mean sandpile odometer reads only the configuration. -/
theorem meanu_eq_integral_u (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (n : ℕ) :
    meanu (law d ν) n = ∫ η, u (fun y => ((η y : ℤ) : ℝ)) n 0 ∂(LatticeProb.iidLaw d ν) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI := stackRankLaw_isProbability (d := d) hd
  have hlaw : law d ν = (LatticeProb.iidLaw d ν).prod (stackRankLaw d) := rfl
  have hI : Integrable (fun ω : Data d => uOf ω n 0)
      ((LatticeProb.iidLaw d ν).prod (stackRankLaw d)) := by
    rw [← hlaw]; exact integrable_uOf hd ν hint n 0
  show ∫ ω, uOf ω n 0 ∂(law d ν) = _
  rw [hlaw, integral_prod _ hI]
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  simp [uOf]

/-! ### The comparison of the two means -/

/-- **`thm:comparison` in the mean.**  `E u_n(0) ≤ E U_n(0)`. -/
theorem meanu_le_meanU (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (n : ℕ) :
    meanu (law d ν) n ≤ meanU (law d ν) n := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI := stackRankLaw_isProbability (d := d) hd
  have hlaw : law d ν = (LatticeProb.iidLaw d ν).prod (stackRankLaw d) := rfl
  have hIu : Integrable (fun ω : Data d => uOf ω n 0)
      ((LatticeProb.iidLaw d ν).prod (stackRankLaw d)) := by
    rw [← hlaw]; exact integrable_uOf hd ν hint n 0
  have hIU : Integrable (fun ω : Data d => (U ω n 0 : ℝ))
      ((LatticeProb.iidLaw d ν).prod (stackRankLaw d)) := by
    rw [← hlaw]; exact integrable_U_law hd ν hint n 0
  rw [meanu_eq_integral_u hd ν hint n, meanU_eq_integral_meanUgiven hd ν hint n]
  refine integral_mono ?_ ?_ fun η => Parking.Frozen.comparison d hd η n 0
  · have := hIu.integral_prod_left
    refine Integrable.congr this (Filter.Eventually.of_forall fun η => ?_)
    haveI := stackRankLaw_isProbability (d := d) hd
    simp [uOf]
  · exact hIU.integral_prod_left

/-! ### `cor:critical` from `lem:critical-density` -/

/-- **`cor:critical` reduced to `lem:critical-density`.**  Applying this to
`Parking.Frozen.critical_density` proves `Parking.Frozen.cor_critical`. -/
theorem cor_critical_of_critical_density
    (hcd : ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (ν : Measure ℤ), IsProbabilityMeasure ν →
      (∀ k : ℤ, ν {k} ≠ 1) → Integrable (fun k : ℤ => |(k : ℝ)|) ν →
      ∫ k, (k : ℝ) ∂ν = 0 →
      (∀ᶠ t : ℕ in atTop, c ≤ (t : ℝ) * Parking.S (Parking.law d ν) t) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
          c * Real.log n - C ≤ Parking.meanU (Parking.law d ν) n) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (ν : Measure ℤ), IsProbabilityMeasure ν →
      (∀ k : ℤ, ν {k} ≠ 1) → Integrable (fun k : ℤ => |(k : ℝ)|) ν →
      ∫ k, (k : ℝ) ∂ν = 0 →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        max (Parking.meanu (Parking.law d ν) n) (c * Real.log n - C)
          ≤ Parking.meanU (Parking.law d ν) n := by
  obtain ⟨c, hc, hall⟩ := hcd
  refine ⟨c, hc, fun d hd ν hprob hnc hint hmean => ?_⟩
  haveI := hprob
  obtain ⟨C, hC, hlog⟩ := (hall d hd ν hprob hnc hint hmean).2
  exact ⟨C, hC, fun n hn => max_le (meanu_le_meanU hd ν hint n) (hlog n hn)⟩

end Parking

end
