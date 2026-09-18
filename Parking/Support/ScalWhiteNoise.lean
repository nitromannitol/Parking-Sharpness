/-
The canonical spatial white noise of the scaling limit (`parking.tex:1679-1737`).

`prop:spatial-scaling` asserts the joint convergence of the rescaled scenery, the
rescaled divisible odometer and the rescaled odometer to a spatial white noise
`W` of intensity `v = variance(η)`, together with a jointly measurable field
`U` solving the parabolic obstacle problem driven by `W`.  The proposition's
limit objects are asserted to exist; this module builds the canonical
realisation of `W` on the Gaussian product space of the library, so that the
measurability clauses of the frozen statement are discharged by construction
rather than assumed.

`contW v φ` is the white-noise integral of the test function `φ` at intensity
`v`, i.e. `√v · whiteNoiseOf volume φ`.  The lemmas below are its measurability,
its centred Gaussian law, its mean, its covariance `v ∫ φ ψ`, and its
linearity in the test function.
-/
import Parking.Support.Continuum
import LatticeProb.Gauss.WhiteNoise
import LatticeProb.Gauss.Brownian

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- The canonical spatial white noise of intensity `v` on `R^d`. -/
def contW {d : ℕ} (v : ℝ) (φ : (Fin d → ℝ) → ℝ) :
    (↥(LatticeProb.l2Basis (volume : Measure (Fin d → ℝ))) → ℝ) → ℝ :=
  fun ω => Real.sqrt v * LatticeProb.whiteNoiseOf (volume : Measure (Fin d → ℝ)) φ ω

/-- **The canonical spatial white noise is measurable at every test function.** -/
theorem measurable_contW {d : ℕ} (v : ℝ) (φ : (Fin d → ℝ) → ℝ) :
    Measurable (contW (d := d) v φ) :=
  (LatticeProb.measurable_whiteNoiseOf (volume : Measure (Fin d → ℝ)) φ).const_mul (Real.sqrt v)


/-- **The canonical spatial white noise has mean zero and is integrable at every
test function.** -/
theorem contW_integral {d : ℕ} {v : ℝ} (_hv : 0 ≤ v) (φ : (Fin d → ℝ) → ℝ)
    (_hφ : IsTestFun φ) :
    Integrable (contW (d := d) v φ)
        (LatticeProb.whiteNoiseLaw (volume : Measure (Fin d → ℝ))) ∧
      ∫ ω, contW (d := d) v φ ω
        ∂(LatticeProb.whiteNoiseLaw (volume : Measure (Fin d → ℝ))) = 0 := by
  have hmem : MemLp (LatticeProb.whiteNoiseOf (volume : Measure (Fin d → ℝ)) φ) 2
      (LatticeProb.whiteNoiseLaw (volume : Measure (Fin d → ℝ))) :=
    LatticeProb.memLp_whiteNoise (LatticeProb.l2HilbertBasis (volume : Measure (Fin d → ℝ))) φ
  constructor
  · exact (hmem.integrable (by norm_num)).const_mul (Real.sqrt v)
  · simp only [contW]
    rw [MeasureTheory.integral_const_mul, LatticeProb.integral_whiteNoiseOf (volume : Measure (Fin d → ℝ)) φ, mul_zero]


/-- **The canonical spatial white noise is a centred Gaussian process.** -/
theorem isGaussianProcess_contW {d : ℕ} {v : ℝ} (_hv : 0 ≤ v) :
    IsGaussianProcess (contW (d := d) v)
      (LatticeProb.whiteNoiseLaw (volume : Measure (Fin d → ℝ))) := by
  have h := (LatticeProb.isGaussianProcess_whiteNoiseOf (μ := (volume : Measure (Fin d → ℝ)))).smul
    (fun _ : (Fin d → ℝ) → ℝ => Real.sqrt v)
  exact h.congr (fun t => Filter.EventuallyEq.of_eq (by ext ω; simp only [contW, smul_eq_mul]))


/-- **The covariance of the canonical spatial white noise.** -/
theorem integral_contW_mul {d : ℕ} {v : ℝ} (hv : 0 ≤ v) (φ ψ : (Fin d → ℝ) → ℝ)
    (hφ : IsTestFun φ) (hψ : IsTestFun ψ) :
    ∫ ω, contW (d := d) v φ ω * contW (d := d) v ψ ω
        ∂(LatticeProb.whiteNoiseLaw (volume : Measure (Fin d → ℝ)))
      = v * ∫ x, φ x * ψ x := by
  have hf : MemLp φ 2 (volume : Measure (Fin d → ℝ)) := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2
  have hg : MemLp ψ 2 (volume : Measure (Fin d → ℝ)) := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2
  simp only [contW]
  have hpt : (fun ω => Real.sqrt v * LatticeProb.whiteNoiseOf (volume : Measure (Fin d → ℝ)) φ ω
        * (Real.sqrt v * LatticeProb.whiteNoiseOf (volume : Measure (Fin d → ℝ)) ψ ω))
      = fun ω => v * (LatticeProb.whiteNoiseOf (volume : Measure (Fin d → ℝ)) φ ω
        * LatticeProb.whiteNoiseOf (volume : Measure (Fin d → ℝ)) ψ ω) := by
    ext ω; have hs : Real.sqrt v * Real.sqrt v = v := by rw [← sq, Real.sq_sqrt hv]
    linear_combination (LatticeProb.whiteNoiseOf (volume : Measure (Fin d → ℝ)) φ ω * LatticeProb.whiteNoiseOf (volume : Measure (Fin d → ℝ)) ψ ω) * hs
  rw [hpt, MeasureTheory.integral_const_mul,
    LatticeProb.integral_whiteNoiseOf_mul (volume : Measure (Fin d → ℝ)) hf hg]


/-- **Linearity of the canonical spatial white noise in the test function.** -/
theorem contW_linear {d : ℕ} {v : ℝ} (_hv : 0 ≤ v) (φ ψ : (Fin d → ℝ) → ℝ)
    (hφ : IsTestFun φ) (hψ : IsTestFun ψ) (a b : ℝ) :
    contW (d := d) v (fun x => a * φ x + b * ψ x)
      =ᵐ[LatticeProb.whiteNoiseLaw (volume : Measure (Fin d → ℝ))]
      fun ω => a * contW (d := d) v φ ω + b * contW (d := d) v ψ ω := by
  have hf : MemLp φ 2 (volume : Measure (Fin d → ℝ)) := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2
  have hg : MemLp ψ 2 (volume : Measure (Fin d → ℝ)) := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2
  have haf : MemLp (a • φ) 2 (volume : Measure (Fin d → ℝ)) := hf.const_smul a
  have hbg : MemLp (b • ψ) 2 (volume : Measure (Fin d → ℝ)) := hg.const_smul b
  have harg : (fun x => a * φ x + b * ψ x) = a • φ + b • ψ := by
    ext x; simp [smul_eq_mul]
  filter_upwards [LatticeProb.whiteNoiseOf_add (volume : Measure (Fin d → ℝ)) haf hbg,
    LatticeProb.whiteNoiseOf_smul (volume : Measure (Fin d → ℝ)) a hf,
    LatticeProb.whiteNoiseOf_smul (volume : Measure (Fin d → ℝ)) b hg] with ω h1 h2 h3
  simp only [contW]
  rw [harg, h1, h2, h3]
  ring

/-- **The law of the white-noise integral of a square-integrable test function
is centred Gaussian with variance its squared `L²` norm.** -/
theorem map_whiteNoiseOf {d : ℕ} (φ : (Fin d → ℝ) → ℝ)
    (_hφ : MemLp φ 2 (volume : Measure (Fin d → ℝ))) :
    (LatticeProb.whiteNoiseLaw (volume : Measure (Fin d → ℝ))).map
        (LatticeProb.whiteNoiseOf (volume : Measure (Fin d → ℝ)) φ)
      = ProbabilityTheory.gaussianReal 0
          (‖LatticeProb.toLpOrZero (volume : Measure (Fin d → ℝ)) φ‖ ^ 2).toNNReal := by
  rw [LatticeProb.whiteNoiseOf, LatticeProb.whiteNoiseLaw, LatticeProb.whiteNoise]
  exact LatticeProb.map_isoProc (LatticeProb.l2HilbertBasis (volume : Measure (Fin d → ℝ)))
    (LatticeProb.toLpOrZero (volume : Measure (Fin d → ℝ)) φ)


/-- **The squared `L²` norm of the `L²` class of a square-integrable function is
the integral of its square.** -/
theorem norm_toLpOrZero_sq {d : ℕ} (φ : (Fin d → ℝ) → ℝ)
    (hφ : MemLp φ 2 (volume : Measure (Fin d → ℝ))) :
    ‖LatticeProb.toLpOrZero (volume : Measure (Fin d → ℝ)) φ‖ ^ 2
      = ∫ x, φ x ^ 2 := by
  rw [LatticeProb.toLpOrZero_of_memLp hφ, MeasureTheory.Lp.norm_toLp φ hφ,
    MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hφ]
  rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_two, ← Real.rpow_mul (by positivity)]
  norm_num

/-- **The canonical spatial white noise is square integrable at every test
function.** -/
theorem memLp_contW {d : ℕ} (v : ℝ) (φ : (Fin d → ℝ) → ℝ) :
    MemLp (contW (d := d) v φ) 2
      (LatticeProb.whiteNoiseLaw (volume : Measure (Fin d → ℝ))) :=
  (LatticeProb.memLp_whiteNoise (LatticeProb.l2HilbertBasis (volume : Measure (Fin d → ℝ))) φ).const_mul (Real.sqrt v)

/-- **The law of the canonical spatial white noise at a test function is
centred Gaussian with variance `v ∫ φ²`.** -/
theorem map_contW {d : ℕ} {v : ℝ} (hv : 0 ≤ v) (φ : (Fin d → ℝ) → ℝ)
    (hφ : MemLp φ 2 (volume : Measure (Fin d → ℝ))) :
    (LatticeProb.whiteNoiseLaw (volume : Measure (Fin d → ℝ))).map (contW (d := d) v φ)
      = ProbabilityTheory.gaussianReal 0 (v * ∫ x, φ x ^ 2).toNNReal := by
  have hpt : contW (d := d) v φ = (fun x : ℝ => Real.sqrt v * x) ∘ LatticeProb.whiteNoiseOf (volume : Measure (Fin d → ℝ)) φ := rfl
  rw [hpt, ← Measure.map_map (by fun_prop : Measurable fun x : ℝ => Real.sqrt v * x) (LatticeProb.measurable_whiteNoiseOf (volume : Measure (Fin d → ℝ)) φ)]
  rw [map_whiteNoiseOf φ hφ, norm_toLpOrZero_sq φ hφ]
  rw [ProbabilityTheory.gaussianReal_map_const_mul]
  congr 1
  · ring
  · rw [Real.toNNReal_mul hv]
    congr 1
    rw [Real.toNNReal_of_nonneg hv]
    congr 1
    rw [Real.sq_sqrt hv]

/-- **The canonical spatial white noise is a spatial white noise of intensity
`v` in the sense of the frozen statement.** -/
theorem isSpatialWhiteNoise_contW {d : ℕ} {v : ℝ} (hv : 0 ≤ v) :
    IsSpatialWhiteNoise d v (LatticeProb.whiteNoiseLaw (volume : Measure (Fin d → ℝ)))
      (contW (d := d) v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro φ ψ hφ hψ a b; exact contW_linear hv φ ψ hφ hψ a b
  · intro φ hφ; exact contW_integral hv φ hφ
  · intro φ ψ hφ hψ
    exact ⟨(memLp_contW v φ).integrable_mul (memLp_contW v ψ), integral_contW_mul hv φ ψ hφ hψ⟩
  · intro φ hφ
    have hmem : MemLp φ 2 (volume : Measure (Fin d → ℝ)) := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2
    exact ⟨(v * ∫ x, φ x ^ 2).toNNReal, Real.coe_toNNReal _ (mul_nonneg hv (integral_nonneg fun x => sq_nonneg _)), map_contW hv φ hmem⟩


end Parking
end
