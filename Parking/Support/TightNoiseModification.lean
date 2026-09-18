/-
The box-clamped noise field and the Gaussianity of its increments.

`Parking.contZBoxProcess` is `contZ` pre-composed with clamping its space-time argument
to the box `[0,T] × [-2A,2A]` via `Set.projIcc`.  Its increment at two points is exactly
Gaussian (a single white-noise evaluation, by linearity), with variance `v ·
noiseVarDiff` at the CLAMPED points — the quantity `TightNoiseHolder.lean`'s
`noiseVarDiff_projIcc_le` bounds by a single exponent `1/2`, valid at every scale of the
original (unclamped) argument.  Combined with `TightGaussianMoment.lean`'s general-`p`
absolute moment scaling, this closes a genuine `q > 2` Kolmogorov condition on
`contZBoxProcess` at `p = 16`, `q = 4`: the increment is exactly Gaussian with variance
`≤ v · K · √ρ` (`ρ` the plain distance of the two points), so its `16`-th absolute
moment is `≤ (v · K) ^ 8 · ρ ^ 4 · gaussianAbsMoment 16`, an exponent `4` bound, above
the space-time index dimension `2`.  `LatticeProb.exists_continuous_modification_pi`
then gives a modification with continuous paths on the whole plane; redefining it to
the zero function off its (null) exceptional set makes the continuity hold at every
point of probability space, and restricting to the box (where `Set.projIcc` is the
identity) makes it a genuine continuous modification of `contZ` there.
-/
import Parking.Support.TightNoiseHolder
import Parking.Support.TightGaussianMoment
import Parking.Support.TightKolmogorov
import Parking.Support.ScalNoiseModification
import LatticeProb.Gauss.WhiteNoise
import LatticeProb.Prob.ChentsovPiModification

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- **The noise field clamped to the box** `[0,T] × [-2A,2A]`. -/
def contZBoxProcess (v T A : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A) : (Fin 2 → ℝ) → contNoiseSpace → ℝ :=
  fun u => contZ v T (Set.projIcc (0 : ℝ) T hT (u 0))
    (Set.projIcc (-(2 * A)) (2 * A) (by linarith) (u 1))

theorem measurable_contZBoxProcess (v T A : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A) (u : Fin 2 → ℝ) :
    Measurable (contZBoxProcess v T A hT hA u) := measurable_contZ _ _ _ _

/-- **The increment of `contZ` at two points is a.e. a single white-noise evaluation**,
by linearity of `whiteNoiseOf`. -/
theorem contZ_sub_ae_eq (v T s x s' x' : ℝ) :
    (fun ω => contZ v T s x ω - contZ v T s' x' ω)
      =ᵐ[contNoiseLaw] fun ω => Real.sqrt v * LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ))
        (contNoiseTest T s x - contNoiseTest T s' x') ω := by
  have hf : MemLp (contNoiseTest T s x) 2 (volume : Measure (ℝ × ℝ)) := memLp_contNoiseTest T s x
  have hg : MemLp (contNoiseTest T s' x') 2 (volume : Measure (ℝ × ℝ)) :=
    memLp_contNoiseTest T s' x'
  filter_upwards [LatticeProb.whiteNoiseOf_add (volume : Measure (ℝ × ℝ)) hf hg.neg,
    LatticeProb.whiteNoiseOf_smul (volume : Measure (ℝ × ℝ)) (-1) hg] with ω h1 h2
  have h2' : LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) (-contNoiseTest T s' x') ω
      = -LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) (contNoiseTest T s' x') ω := by
    simpa using h2
  have h1' : LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ))
      (contNoiseTest T s x - contNoiseTest T s' x') ω
      = LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) (contNoiseTest T s x) ω
        - LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ)) (contNoiseTest T s' x') ω := by
    rw [sub_eq_add_neg, h1, h2']; ring
  simp only [contZ]
  rw [h1']
  ring

/-- **The increment of `contZ` at two points has an exactly Gaussian law**, mean `0`
and variance `v · noiseVarDiff T ![s,x] ![s',x']`. -/
theorem hasGaussianLaw_contZ_sub (v T s x s' x' : ℝ) :
    HasGaussianLaw (fun ω => contZ v T s x ω - contZ v T s' x' ω) contNoiseLaw := by
  have hg : HasGaussianLaw (LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ))
      (contNoiseTest T s x - contNoiseTest T s' x')) contNoiseLaw :=
    (LatticeProb.isGaussianProcess_whiteNoiseOf (volume : Measure (ℝ × ℝ))).hasGaussianLaw_eval _
  exact (hg.smul (Real.sqrt v)).congr (contZ_sub_ae_eq v T s x s' x').symm

/-- `contZ` is integrable: it is a constant multiple of a Gaussian, hence integrable. -/
theorem integrable_contZ (v T s x : ℝ) : Integrable (contZ v T s x) contNoiseLaw := by
  have hg : HasGaussianLaw (LatticeProb.whiteNoiseOf (volume : Measure (ℝ × ℝ))
      (contNoiseTest T s x)) contNoiseLaw :=
    (LatticeProb.isGaussianProcess_whiteNoiseOf (volume : Measure (ℝ × ℝ))).hasGaussianLaw_eval _
  exact hg.integrable.const_mul (Real.sqrt v)

/-- **The variance of the increment**, matching `noiseVarDiff`. -/
theorem variance_contZ_sub {v : ℝ} (hv : 0 ≤ v) (T s x s' x' : ℝ) :
    variance (fun ω => contZ v T s x ω - contZ v T s' x' ω) contNoiseLaw
      = v * noiseVarDiff T ![s, x] ![s', x'] := by
  have hmeas : Measurable (fun ω => contZ v T s x ω - contZ v T s' x' ω) :=
    (measurable_contZ v T s x).sub (measurable_contZ v T s' x')
  have hmean : ∫ ω, (contZ v T s x ω - contZ v T s' x' ω) ∂contNoiseLaw = 0 := by
    rw [integral_sub (integrable_contZ v T s x) (integrable_contZ v T s' x'),
      integral_contZ, integral_contZ, sub_zero]
  rw [variance_eq_integral hmeas.aemeasurable, hmean]
  simp only [sub_zero]
  rw [integral_contZ_sub_sq hv T s x s' x', noiseVarDiff_eq]

/-- **The mean of the box-clamped field's increment is `0`.** -/
theorem integral_contZBoxProcess_sub (v T A : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A) (u u' : Fin 2 → ℝ) :
    (∫ ω, (contZBoxProcess v T A hT hA u ω - contZBoxProcess v T A hT hA u' ω)
        ∂contNoiseLaw) = 0 := by
  have h1 : Integrable (contZBoxProcess v T A hT hA u) contNoiseLaw := integrable_contZ v T _ _
  have h2 : Integrable (contZBoxProcess v T A hT hA u') contNoiseLaw := integrable_contZ v T _ _
  rw [integral_sub h1 h2]
  have e1 : (∫ ω, contZBoxProcess v T A hT hA u ω ∂contNoiseLaw) = 0 := integral_contZ v T _ _
  have e2 : (∫ ω, contZBoxProcess v T A hT hA u' ω ∂contNoiseLaw) = 0 := integral_contZ v T _ _
  rw [e1, e2, sub_zero]

/-- **The increment of the box-clamped field has an exactly Gaussian law.** -/
theorem hasGaussianLaw_contZBoxProcess_sub (v T A : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A)
    (u u' : Fin 2 → ℝ) :
    HasGaussianLaw (fun ω => contZBoxProcess v T A hT hA u ω - contZBoxProcess v T A hT hA u' ω)
      contNoiseLaw :=
  hasGaussianLaw_contZ_sub v T _ _ _ _

/-- **The variance of the box-clamped field's increment, bounded by the global Hölder rate.**
Combines the exact variance identity (`variance_contZ_sub`, at the clamped points) with the
clamped Hölder bound (`noiseVarDiff_projIcc_le`). -/
theorem variance_contZBoxProcess_sub_le {v : ℝ} (hv : 0 ≤ v) (T A : ℝ) (hT : 0 ≤ T)
    (hA : 0 ≤ A) (u u' : Fin 2 → ℝ) :
    variance (fun ω => contZBoxProcess v T A hT hA u ω - contZBoxProcess v T A hT hA u' ω)
      contNoiseLaw
      ≤ v * ((4 * Real.sqrt (2 / Real.pi)
          + 8 * Real.sqrt (2 / Real.pi) * (2 : ℝ) ^ ((1 : ℝ) / 4) * (2 * T) ^ ((1 : ℝ) / 4))
        * Real.sqrt (|u 0 - u' 0| + |u 1 - u' 1|)) :=
  (variance_contZ_sub hv T (Set.projIcc (0 : ℝ) T hT (u 0) : ℝ)
      (Set.projIcc (-(2 * A)) (2 * A) (by linarith) (u 1) : ℝ)
      (Set.projIcc (0 : ℝ) T hT (u' 0) : ℝ)
      (Set.projIcc (-(2 * A)) (2 * A) (by linarith) (u' 1) : ℝ)).trans_le
    (mul_le_mul_of_nonneg_left (noiseVarDiff_projIcc_le hT hA (u 0) (u 1) (u' 0) (u' 1)) hv)

/-- **The `16`-th absolute moment of the box-clamped field's increment**, bounded via its exact
Gaussianity and the global Hölder variance bound: an exponent-`4` Kolmogorov condition, above
the space-time index dimension `2`. -/
theorem lintegral_edist_contZBoxProcess_rpow_sixteen_le {v : ℝ} (hv : 0 ≤ v) (T A : ℝ)
    (hT : 0 ≤ T) (hA : 0 ≤ A) (u u' : Fin 2 → ℝ) :
    (∫⁻ ω, edist (contZBoxProcess v T A hT hA u ω) (contZBoxProcess v T A hT hA u' ω)
        ^ (16 : ℝ) ∂contNoiseLaw)
      ≤ ENNReal.ofReal
          ((v * (4 * Real.sqrt (2 / Real.pi)
              + 8 * Real.sqrt (2 / Real.pi) * (2 : ℝ) ^ ((1 : ℝ) / 4)
                * (2 * T) ^ ((1 : ℝ) / 4))) ^ 8 * gaussianAbsMoment 16 * 16)
        * edist u u' ^ (4 : ℝ) := by
  set K : ℝ := 4 * Real.sqrt (2 / Real.pi)
      + 8 * Real.sqrt (2 / Real.pi) * (2 : ℝ) ^ ((1 : ℝ) / 4) * (2 * T) ^ ((1 : ℝ) / 4) with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  set Δ : contNoiseSpace → ℝ :=
    fun ω => contZBoxProcess v T A hT hA u ω - contZBoxProcess v T A hT hA u' ω with hΔdef
  have hΔmeas : Measurable Δ :=
    (measurable_contZBoxProcess v T A hT hA u).sub (measurable_contZBoxProcess v T A hT hA u')
  set σ2 : ℝ := variance Δ contNoiseLaw with hσ2def
  have hσ2nn : 0 ≤ σ2 := variance_nonneg Δ contNoiseLaw
  have hgauss : HasGaussianLaw Δ contNoiseLaw := hasGaussianLaw_contZBoxProcess_sub v T A hT hA u u'
  have hmean : (∫ ω, Δ ω ∂contNoiseLaw) = 0 := integral_contZBoxProcess_sub v T A hT hA u u'
  have hmap : contNoiseLaw.map Δ = gaussianReal 0 σ2.toNNReal := by
    have h := hgauss.map_eq_gaussianReal
    rwa [hmean] at h
  have hσdef : σ2 = Real.sqrt σ2 ^ 2 := (Real.sq_sqrt hσ2nn).symm
  have hmap' : contNoiseLaw.map Δ = gaussianReal 0 (Real.sqrt σ2 ^ 2).toNNReal := by
    rw [← hσdef]; exact hmap
  have hpt : ∀ ω, edist (contZBoxProcess v T A hT hA u ω) (contZBoxProcess v T A hT hA u' ω)
      ^ (16 : ℝ) = ‖Δ ω‖ₑ ^ (16 : ℝ) := by
    intro ω
    rw [edist_eq_enorm_sub, hΔdef]
  have hfmeas : Measurable fun y : ℝ => ‖y‖ₑ ^ (16 : ℝ) := by fun_prop
  have hlint : (∫⁻ ω, ‖Δ ω‖ₑ ^ (16 : ℝ) ∂contNoiseLaw) = ∫⁻ y, ‖y‖ₑ ^ (16 : ℝ) ∂(contNoiseLaw.map Δ) :=
    (lintegral_map hfmeas hΔmeas).symm
  have hgaussmom : (∫⁻ y, ‖y‖ₑ ^ (16 : ℝ) ∂(gaussianReal (0 : ℝ) (Real.sqrt σ2 ^ 2).toNNReal))
      = ENNReal.ofReal (Real.sqrt σ2 ^ (16 : ℝ)) * ENNReal.ofReal (gaussianAbsMoment 16) := by
    have h := lintegral_enorm_rpow_gaussianReal (16 : ℝ≥0) (by norm_num)
      (σ := Real.sqrt σ2) (Real.sqrt_nonneg σ2)
    simpa using h
  have hrhs16 : Real.sqrt σ2 ^ (16 : ℝ) = σ2 ^ (8 : ℕ) := by
    rw [show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      show (16 : ℕ) = 2 * 8 from rfl, pow_mul, ← hσdef]
  have hstep : σ2 ^ (8 : ℕ) ≤ (v * K) ^ 8 * (|u 0 - u' 0| + |u 1 - u' 1|) ^ 4 := by
    have hbound : σ2 ≤ v * (K * Real.sqrt (|u 0 - u' 0| + |u 1 - u' 1|)) := by
      rw [hKdef]; exact variance_contZBoxProcess_sub_le hv T A hT hA u u'
    have hsqrt8 : (Real.sqrt (|u 0 - u' 0| + |u 1 - u' 1|)) ^ 8
        = (|u 0 - u' 0| + |u 1 - u' 1|) ^ 4 := by
      rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ |u 0 - u' 0| + |u 1 - u' 1|)]
    calc σ2 ^ 8 ≤ (v * (K * Real.sqrt (|u 0 - u' 0| + |u 1 - u' 1|))) ^ 8 :=
          pow_le_pow_left₀ hσ2nn hbound 8
      _ = (v * K) ^ 8 * (Real.sqrt (|u 0 - u' 0| + |u 1 - u' 1|)) ^ 8 := by ring
      _ = (v * K) ^ 8 * (|u 0 - u' 0| + |u 1 - u' 1|) ^ 4 := by rw [hsqrt8]
  have hchain : (∫⁻ ω, edist (contZBoxProcess v T A hT hA u ω)
      (contZBoxProcess v T A hT hA u' ω) ^ (16 : ℝ) ∂contNoiseLaw)
      ≤ ENNReal.ofReal ((v * K) ^ 8 * (|u 0 - u' 0| + |u 1 - u' 1|) ^ 4)
        * ENNReal.ofReal (gaussianAbsMoment 16) := by
    calc (∫⁻ ω, edist (contZBoxProcess v T A hT hA u ω)
        (contZBoxProcess v T A hT hA u' ω) ^ (16 : ℝ) ∂contNoiseLaw)
        = ∫⁻ ω, ‖Δ ω‖ₑ ^ (16 : ℝ) ∂contNoiseLaw := lintegral_congr hpt
      _ = ∫⁻ y, ‖y‖ₑ ^ (16 : ℝ) ∂(contNoiseLaw.map Δ) := hlint
      _ = ∫⁻ y, ‖y‖ₑ ^ (16 : ℝ) ∂(gaussianReal (0 : ℝ) (Real.sqrt σ2 ^ 2).toNNReal) := by
          rw [hmap']
      _ = ENNReal.ofReal (Real.sqrt σ2 ^ (16 : ℝ)) * ENNReal.ofReal (gaussianAbsMoment 16) :=
          hgaussmom
      _ = ENNReal.ofReal (σ2 ^ (8 : ℕ)) * ENNReal.ofReal (gaussianAbsMoment 16) := by rw [hrhs16]
      _ ≤ ENNReal.ofReal ((v * K) ^ 8 * (|u 0 - u' 0| + |u 1 - u' 1|) ^ 4)
          * ENNReal.ofReal (gaussianAbsMoment 16) := by
          gcongr
  have hed : edist u u' ^ (4 : ℝ) = ENNReal.ofReal ((max |u 0 - u' 0| |u 1 - u' 1|) ^ (4 : ℝ)) := by
    rw [edist_pi_def, Finset.univ_fin2]
    rw [Finset.sup_insert, Finset.sup_singleton]
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq]
    rw [← ENNReal.ofReal_max, ← ENNReal.ofReal_rpow_of_nonneg
      (le_max_of_le_left (abs_nonneg _)) (by norm_num : (0:ℝ) ≤ 4)]
  have hsum : (|u 0 - u' 0| + |u 1 - u' 1|) ^ (4:ℝ) ≤ (2:ℝ) ^ (4:ℝ) * (max |u 0 - u' 0| |u 1 - u' 1|) ^ (4:ℝ) := by
    set a := |u 0 - u' 0| with ha
    set b := |u 1 - u' 1| with hb
    set m := max a b with hm
    have h1 : a ≤ m := le_max_left a b
    have h2' : b ≤ m := le_max_right a b
    have h0 : (0 : ℝ) ≤ m := le_max_of_le_left (abs_nonneg _)
    have ha0 : 0 ≤ a := abs_nonneg _
    have hb0 : 0 ≤ b := abs_nonneg _
    have hab : a + b ≤ 2 * m := by linarith
    calc (a + b) ^ (4:ℝ) ≤ (2 * m) ^ (4:ℝ) := Real.rpow_le_rpow (by positivity) hab (by norm_num)
      _ = 2 ^ (4:ℝ) * m ^ (4:ℝ) := Real.mul_rpow (by norm_num) h0
  have hsum4 : (|u 0 - u' 0| + |u 1 - u' 1|) ^ (4:ℕ) ≤ 16 * (max |u 0 - u' 0| |u 1 - u' 1|) ^ (4:ℕ) := by
    have e1 : (|u 0 - u' 0| + |u 1 - u' 1|) ^ (4:ℝ) = (|u 0 - u' 0| + |u 1 - u' 1|) ^ (4:ℕ) := by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    have e2 : (max |u 0 - u' 0| |u 1 - u' 1|) ^ (4:ℝ) = (max |u 0 - u' 0| |u 1 - u' 1|) ^ (4:ℕ) := by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    have e3 : (2:ℝ) ^ (4:ℝ) = 16 := by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [e1, e2, e3] at hsum
    exact hsum
  calc (∫⁻ ω, edist (contZBoxProcess v T A hT hA u ω)
      (contZBoxProcess v T A hT hA u' ω) ^ (16 : ℝ) ∂contNoiseLaw)
      ≤ ENNReal.ofReal ((v * K) ^ 8 * (|u 0 - u' 0| + |u 1 - u' 1|) ^ 4)
        * ENNReal.ofReal (gaussianAbsMoment 16) := hchain
    _ ≤ ENNReal.ofReal ((v * K) ^ 8 * (16 * (max |u 0 - u' 0| |u 1 - u' 1|) ^ 4))
        * ENNReal.ofReal (gaussianAbsMoment 16) := by
        gcongr
    _ = ENNReal.ofReal ((v * K) ^ 8 * gaussianAbsMoment 16 * 16)
        * ENNReal.ofReal ((max |u 0 - u' 0| |u 1 - u' 1|) ^ (4:ℕ)) := by
        have hmomnn : (0:ℝ) ≤ gaussianAbsMoment 16 := ENNReal.toReal_nonneg
        rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (v * K) ^ 8
            * (16 * (max |u 0 - u' 0| |u 1 - u' 1|) ^ 4)),
          ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (v * K) ^ 8 * gaussianAbsMoment 16 * 16)]
        congr 1
        ring
    _ = ENNReal.ofReal ((v * K) ^ 8 * gaussianAbsMoment 16 * 16) * edist u u' ^ (4 : ℝ) := by
        rw [hed]
        congr 2
        rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]

/-- **The Kolmogorov condition for the box-clamped field, at exponent `p = 16`, `q = 4`.** -/
theorem isKolmogorovProcess_contZBoxProcess {v T A : ℝ} (hv : 0 ≤ v) (hT : 0 ≤ T) (hA : 0 ≤ A) :
    IsKolmogorovProcess (contZBoxProcess v T A hT hA) contNoiseLaw 16 4
      ⟨(v * (4 * Real.sqrt (2 / Real.pi)
          + 8 * Real.sqrt (2 / Real.pi) * (2 : ℝ) ^ ((1 : ℝ) / 4)
            * (2 * T) ^ ((1 : ℝ) / 4))) ^ 8 * gaussianAbsMoment 16 * 16, by
        have : (0:ℝ) ≤ gaussianAbsMoment 16 := ENNReal.toReal_nonneg
        positivity⟩ := by
  refine ⟨?_, ?_, by norm_num, by norm_num⟩
  · intro s t
    exact ((measurable_contZBoxProcess v T A hT hA s).prodMk
      (measurable_contZBoxProcess v T A hT hA t)).mono le_rfl
      (le_of_eq (Prod.borelSpace (α := ℝ) (β := ℝ)).measurable_eq.symm)
  · intro s t
    rw [ENNReal.coe_nnreal_eq]
    exact lintegral_edist_contZBoxProcess_rpow_sixteen_le hv T A hT hA s t

/-- **The jointly continuous modification of the box-clamped noise field.**  The Kolmogorov
condition above holds at exponent `q = 4`, above the space-time index dimension `2`, so the
multi-parameter Kolmogorov-Chentsov theorem gives a modification with continuous sample paths
on the whole plane. -/
theorem exists_continuous_modification_contZBoxProcess {v T A : ℝ} (hv : 0 ≤ v) (hT : 0 ≤ T)
    (hA : 0 ≤ A) :
    ∃ Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ, (∀ z, Measurable (Y z)) ∧
      (∀ z, contZBoxProcess v T A hT hA z =ᵐ[contNoiseLaw] Y z) ∧
      ∀ᵐ ω ∂contNoiseLaw, Continuous fun z => Y z ω :=
  LatticeProb.exists_continuous_modification_pi (isKolmogorovProcess_contZBoxProcess hv hT hA)
    (by norm_num)

/-- **The everywhere-continuous version.**  Redefining the modification to the zero function
off its (null) exceptional set turns "continuous almost surely" into "continuous at every
point of probability space", without disturbing the modification property (the redefinition
only touches a `contNoiseLaw`-null set). -/
theorem exists_continuous_modification_contZBoxProcess_everywhere {v T A : ℝ} (hv : 0 ≤ v)
    (hT : 0 ≤ T) (hA : 0 ≤ A) :
    ∃ Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ, (∀ z, Measurable (Y z)) ∧
      (∀ z, contZBoxProcess v T A hT hA z =ᵐ[contNoiseLaw] Y z) ∧
      ∀ ω, Continuous fun z => Y z ω := by
  obtain ⟨Y, hYmeas, hYmod, hYcont⟩ := exists_continuous_modification_contZBoxProcess hv hT hA
  classical
  have hnull : contNoiseLaw {ω | ¬ Continuous fun z => Y z ω} = 0 := ae_iff.mp hYcont
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ := exists_measurable_superset_of_null hnull
  set Y' : (Fin 2 → ℝ) → contNoiseSpace → ℝ :=
    fun z ω => if ω ∈ N then 0 else Y z ω with hY'def
  have hagree : ∀ z, {ω | Y z ω ≠ Y' z ω} ⊆ N := by
    intro z ω hω
    by_contra hωN
    apply hω
    rw [hY'def]
    simp only [if_neg hωN]
  refine ⟨Y', fun z => Measurable.ite hNmeas measurable_const (hYmeas z), fun z => ?_, fun ω => ?_⟩
  · have hYY' : Y z =ᵐ[contNoiseLaw] Y' z :=
      ae_iff.mpr (measure_mono_null (hagree z) hNnull)
    exact (hYmod z).trans hYY'
  · by_cases hωN : ω ∈ N
    · have heq : (fun z => Y' z ω) = fun _ => (0 : ℝ) := by
        funext z; rw [hY'def]; simp [hωN]
      rw [heq]; exact continuous_const
    · have heq : (fun z => Y' z ω) = fun z => Y z ω := by
        funext z; rw [hY'def]; simp [hωN]
      rw [heq]
      have hωnotbad : ω ∉ {ω | ¬ Continuous fun z => Y z ω} := fun h => hωN (hNsub h)
      simpa using hωnotbad

/-- **Restricted to the box, the clamped field is exactly `contZ` itself** (not merely a.e.):
`Set.projIcc` is the identity there, so a continuous modification of `contZBoxProcess` is a
genuine continuous modification of `contZ` on the box. -/
theorem contZBoxProcess_eq_contZ_of_mem {v T A : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) {z : Fin 2 → ℝ}
    (hz0 : z 0 ∈ Set.Icc (0 : ℝ) T) (hz1 : z 1 ∈ Set.Icc (-(2 * A)) (2 * A)) :
    contZBoxProcess v T A hT hA z = contZ v T (z 0) (z 1) := by
  show contZ v T (Set.projIcc (0 : ℝ) T hT (z 0) : ℝ)
      (Set.projIcc (-(2 * A)) (2 * A) (by linarith) (z 1) : ℝ) = contZ v T (z 0) (z 1)
  rw [Set.projIcc_of_mem hT hz0, Set.projIcc_of_mem (by linarith) hz1]

/-- **`hgc`: the noise field has an everywhere-defined modification with paths continuous on
the box `orientedBox T A`.**  Restricting the everywhere-continuous modification of the
box-clamped field (above) to the box gives a genuine modification of `contZ` there, with
continuous paths at every sample point of `contNoiseSpace`, not merely almost every one — the
form `parking.tex:3199-3203`'s cutoff construction (`rewardBox`, `boxPoint` of
`OrientedCutoffValue.lean`) actually needs. -/
theorem exists_continuousOn_modification_contZ_box {v T A : ℝ} (hv : 0 ≤ v) (hT : 0 ≤ T)
    (hA : 0 ≤ A) :
    ∃ Y : (Fin 2 → ℝ) → contNoiseSpace → ℝ, (∀ z, Measurable (Y z)) ∧
      (∀ z ∈ orientedBox T A, contZ v T (z 0) (z 1) =ᵐ[contNoiseLaw] Y z) ∧
      ∀ ω, ContinuousOn (fun z => Y z ω) (orientedBox T A) := by
  obtain ⟨Y, hYmeas, hYmod, hYcont⟩ :=
    exists_continuous_modification_contZBoxProcess_everywhere hv hT hA
  refine ⟨Y, hYmeas, ?_, fun ω => (hYcont ω).continuousOn⟩
  intro z hz
  rw [orientedBox, Set.mem_Icc] at hz
  have hz0 : z 0 ∈ Set.Icc (0 : ℝ) T := ⟨by simpa using hz.1 0, by simpa using hz.2 0⟩
  have hz1 : z 1 ∈ Set.Icc (-(2 * A)) (2 * A) := ⟨by simpa using hz.1 1, by simpa using hz.2 1⟩
  rw [← contZBoxProcess_eq_contZ_of_mem hT hA hz0 hz1]
  exact hYmod z

end Parking

end
