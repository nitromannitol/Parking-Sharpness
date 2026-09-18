/-
The standing hypotheses of the critical density, read for the real one-site law.

`Parking.CriticalLaw ν` is a hypothesis on a measure on `ℤ`, while
`Parking.External.SandpileGrowth` and `Parking.External.UConcentration` are
stated for a measure on `ℝ`.  This file checks the four hypotheses of `thm:BP`
for the pushforward `ν.map Int.cast`: it is a probability measure, its mean
vanishes, its variance is positive and finite, and it has an exponential moment.
Positivity of the variance is where "nonconstant" is used: a vanishing variance
makes the coordinate almost surely equal to its mean, which is zero, and then
`ν {0} = 1`.
-/
import Parking.Support.UConcBridge
import Parking.External.SandpileGrowth

noncomputable section

namespace Parking

open MeasureTheory ProbabilityTheory LatticeProb

variable {d : ℕ}

/-- The one-site law read in the reals. -/
def realLaw (ν : Measure ℤ) : Measure ℝ := ν.map (fun k : ℤ => (k : ℝ))

instance realLaw_isProbability (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (realLaw ν) := by
  rw [realLaw]
  exact Measure.isProbabilityMeasure_map measurable_intCastReal.aemeasurable

theorem realLaw_integrable_iff (ν : Measure ℤ) [IsProbabilityMeasure ν] {f : ℝ → ℝ}
    (hf : Measurable f) :
    Integrable f (realLaw ν) ↔ Integrable (fun k : ℤ => f (k : ℝ)) ν := by
  rw [realLaw]
  exact integrable_map_measure hf.aestronglyMeasurable measurable_intCastReal.aemeasurable

theorem realLaw_integral (ν : Measure ℤ) [IsProbabilityMeasure ν] {f : ℝ → ℝ}
    (hf : Measurable f) :
    ∫ z, f z ∂(realLaw ν) = ∫ k, f (k : ℝ) ∂ν := by
  rw [realLaw, integral_map measurable_intCastReal.aemeasurable hf.aestronglyMeasurable]

theorem realLaw_mean (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∫ z, z ∂(realLaw ν) = 0 := by
  haveI := hν.prob
  have h : ∫ z, (id z : ℝ) ∂(realLaw ν) = ∫ k, ((k : ℤ) : ℝ) ∂ν :=
    realLaw_integral ν measurable_id
  simpa using h.trans hν.mean

/-- The exponential moment, transported. -/
theorem realLaw_expMoment (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ θ : ℝ, 0 < θ ∧ Integrable (fun z : ℝ => Real.exp (θ * |z|)) (realLaw ν) := by
  haveI := hν.prob
  obtain ⟨θ, hθ, hint⟩ := hν.expMoment
  refine ⟨θ, hθ, ?_⟩
  rw [realLaw_integrable_iff ν (f := fun z : ℝ => Real.exp (θ * |z|))
    (Real.measurable_exp.comp (measurable_abs.const_mul θ))]
  exact hint

/-- The second moment is finite, so the coordinate is in `L²`. -/
theorem realLaw_memLp_two (ν : Measure ℤ) (hν : CriticalLaw ν) :
    MemLp (id : ℝ → ℝ) 2 (realLaw ν) := by
  haveI := hν.prob
  obtain ⟨θ, hθ, hint⟩ := hν.expMoment
  obtain ⟨C, hC, hbound⟩ := rpow_le_const_mul_exp (r := (2 : ℝ)) (by norm_num) hθ
  have hsq : Integrable (fun k : ℤ => (((k : ℤ) : ℝ)) ^ 2) ν := by
    refine Integrable.mono' (hint.const_mul C)
      ((measurable_from_countable' fun k : ℤ => (((k : ℤ) : ℝ)) ^ 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => ?_)
    have h0 : (0 : ℝ) ≤ |((k : ℤ) : ℝ)| := abs_nonneg _
    have hrp : |((k : ℤ) : ℝ)| ^ (2 : ℝ) = (((k : ℤ) : ℝ)) ^ 2 := by
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    have := hbound _ h0
    rw [hrp] at this
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact this
  refine (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr ?_
  rw [show (fun z : ℝ => (id z) ^ 2) = fun z : ℝ => z ^ 2 from rfl,
    realLaw_integrable_iff ν (f := fun z : ℝ => z ^ 2) (measurable_id.pow_const 2)]
  exact hsq

theorem realLaw_evariance_lt_top (ν : Measure ℤ) (hν : CriticalLaw ν) :
    evariance (id : ℝ → ℝ) (realLaw ν) < ⊤ := by
  haveI := hν.prob
  exact evariance_lt_top (realLaw_memLp_two ν hν)

theorem realLaw_evariance_pos (ν : Measure ℤ) (hν : CriticalLaw ν) :
    0 < evariance (id : ℝ → ℝ) (realLaw ν) := by
  haveI := hν.prob
  refine pos_iff_ne_zero.mpr fun hzero => ?_
  · have hae := (evariance_eq_zero_iff (X := (id : ℝ → ℝ)) (μ := realLaw ν)
      measurable_id.aemeasurable).mp hzero
    have hmean : ∫ z, (id z : ℝ) ∂(realLaw ν) = 0 := by
      simpa using realLaw_mean ν hν
    rw [hmean] at hae
    -- almost surely the coordinate is zero, so the law of `η(0)` is the point mass at zero
    have hcompl : (realLaw ν) {z : ℝ | z ≠ 0} = 0 := by
      have : {z : ℝ | ¬ (id z = (0 : ℝ))} = {z : ℝ | z ≠ 0} := rfl
      rw [← this]
      exact hae
    have hsingle : (realLaw ν) {(0 : ℝ)} = 1 := by
      have huniv : (realLaw ν) Set.univ = 1 := measure_univ
      have hsplit : Set.univ = {(0 : ℝ)} ∪ {z : ℝ | z ≠ 0} := by
        ext z; by_cases hz : z = 0 <;> simp [hz]
      have hle : (realLaw ν) Set.univ ≤ (realLaw ν) {(0 : ℝ)} + (realLaw ν) {z : ℝ | z ≠ 0} := by
        rw [hsplit]; exact measure_union_le _ _
      rw [huniv, hcompl, add_zero] at hle
      exact le_antisymm (by simpa using prob_le_one) hle
    have hpre : (fun k : ℤ => (k : ℝ)) ⁻¹' {(0 : ℝ)} = ({0} : Set ℤ) := by
      ext k
      simp
    have : ν ({0} : Set ℤ) = 1 := by
      rw [← hpre, ← Measure.map_apply measurable_intCastReal (measurableSet_singleton _)]
      exact hsingle
    exact hν.nonconst 0 this

/-! ### The mean sandpile odometer of the parking law -/

theorem meanu_eq_meanSandpileReal (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (n : ℕ) :
    meanu (law d ν) n = Parking.External.meanSandpileReal d (realLaw ν) n := by
  rw [meanu, Parking.External.meanSandpileReal, realLaw]
  have hfun : (fun ω : Data d => uOf ω n 0)
      = fun ω : Data d => (fun η : Site d → ℝ => u η n 0) (confReal ω) := rfl
  rw [hfun, integral_confReal hd ν (measurable_u_eval n 0)]

end Parking

end
