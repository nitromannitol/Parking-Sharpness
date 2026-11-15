import Parking.External.LinearFieldScaling
import Sandpile.Continuum.Kernel
import Sandpile.Support.ContBMSquare
import Sandpile.Support.ContBMTimeBound
import Sandpile.Support.ExplNoiseFubini
import Sandpile.Support.ExplGreenFubini
import Parking.Support.SpatialGreenPairing

/-!
# Brownian Green kernels and spatial white noise in coordinates
-/

open MeasureTheory ProbabilityTheory

namespace Parking

/-- The finite-time Green kernels agree under the Euclidean coordinate equivalence. -/
theorem contFiniteGreen_eq_greenTimeBM (d : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (x y : Fin d → ℝ) :
    External.contFiniteGreen d t x y =
      Sandpile.Continuum.greenTimeBM d t (WithLp.toLp 2 x) (WithLp.toLp 2 y) := by
  have hnorm : ‖(WithLp.toLp 2 x : Sandpile.Continuum.Space d) - WithLp.toLp 2 y‖ ^ 2 =
      ∑ i, (x i - y i) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  unfold External.contFiniteGreen Sandpile.Continuum.greenTimeBM
  rw [intervalIntegral.integral_of_le ht]
  congr 1
  funext s
  simp only [External.contHeatKernel, Sandpile.Continuum.heatKernelBM, hnorm]

/-- The finite-time Green kernel is square integrable in dimensions at most three. -/
theorem memLp_contFiniteGreen (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (t : ℝ) (ht : 0 ≤ t) (x : Fin d → ℝ) :
    MemLp (External.contFiniteGreen d t x) 2 volume := by
  have h := (Sandpile.Support.memLp_greenTimeBM hd hd3 ht (WithLp.toLp 2 x)).comp_measurePreserving
    (PiLp.volume_preserving_toLp (Fin d))
  convert h using 1
  ext y
  exact contFiniteGreen_eq_greenTimeBM d t ht x y

/-- Away from the diagonal the finite-time Green kernel is positive at positive times. -/
theorem contFiniteGreen_pos_of_ne {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t)
    {x y : Fin d → ℝ} (hxy : x ≠ y) : 0 < External.contFiniteGreen d t x y := by
  have hne : (WithLp.toLp 2 x : Sandpile.Continuum.Space d) ≠ WithLp.toLp 2 y := by
    intro h
    exact hxy (congrArg WithLp.ofLp h)
  rw [contFiniteGreen_eq_greenTimeBM d t ht.le x y,
    Sandpile.Continuum.greenTimeBM, intervalIntegral.integral_of_le ht.le,
    integral_Ioc_eq_integral_Ioo]
  have hint := Sandpile.Support.integrableOn_heatKernelBM_time hd (t := t) hne
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) t)]
      fun s => Sandpile.Continuum.heatKernelBM d s (WithLp.toLp 2 x) (WithLp.toLp 2 y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact Sandpile.Support.heatKernelBM_nonneg d hs.1.le _ _
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg hint]
  refine ((Measure.measure_Ioo_pos volume).2 ht).trans_le (measure_mono ?_)
  intro s hs
  exact ⟨ne_of_gt (Sandpile.Support.heatKernelBM_pos hd hs.1 _ _), hs⟩

/-- A positive-time Green kernel is not a compactly supported test function. -/
theorem not_isTestFun_contFiniteGreen {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t)
    (x : Fin d → ℝ) : ¬ IsTestFun (External.contFiniteGreen d t x) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hsub : ({x}ᶜ : Set (Fin d → ℝ)) ⊆
      Function.support (External.contFiniteGreen d t x) := by
    intro y hy
    have hxy : x ≠ y := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq,
      eq_comm] using hy
    exact ne_of_gt (contFiniteGreen_pos_of_ne hd ht hxy)
  have hfull : tsupport (External.contFiniteGreen d t x) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← (dense_compl_singleton x).closure_eq]
    exact closure_mono hsub
  intro htest
  have hcompact : IsCompact (tsupport (External.contFiniteGreen d t x)) := htest.2
  rw [hfull] at hcompact
  exact (not_compactSpace_iff.mpr inferInstance) (isCompact_univ_iff.mp hcompact)

/-- Coordinate transport followed by the white-noise isometry. -/
noncomputable def sandpileNoiseMap {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) :
    Lp ℝ 2 (volume : Measure (Fin d → ℝ)) →L[ℝ] Lp ℝ 2 P :=
  (Sandpile.Support.whiteNoiseLinearIsometry hW).toContinuousLinearMap.comp
    (Lp.compMeasurePreservingₗᵢ ℝ (WithLp.ofLp : Sandpile.Continuum.Space d → Fin d → ℝ)
      (PiLp.volume_preserving_ofLp (Fin d))).toContinuousLinearMap

/-- The transported white-noise map preserves the `L²` norm. -/
theorem norm_sandpileNoiseMap {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P)
    (f : Lp ℝ 2 (volume : Measure (Fin d → ℝ))) :
    ‖sandpileNoiseMap hW f‖ = ‖f‖ := by
  change ‖Sandpile.Support.whiteNoiseLinearIsometry hW
    (Lp.compMeasurePreservingₗᵢ ℝ (WithLp.ofLp : Sandpile.Continuum.Space d → Fin d → ℝ)
      (PiLp.volume_preserving_ofLp (Fin d)) f)‖ = ‖f‖
  rw [LinearIsometry.norm_map, LinearIsometry.norm_map]

/-- The transported map agrees almost everywhere with each square-integrable coordinate. -/
theorem sandpileNoiseMap_toLp_ae_eq {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) (f : (Fin d → ℝ) → ℝ)
    (hf : MemLp f 2 volume) :
    (fun ω => sandpileNoiseMap hW (hf.toLp f) ω) =ᵐ[P]
      W (fun y => f (WithLp.ofLp y)) := by
  exact Sandpile.Support.whiteNoiseLinearIsometry_toLp_ae_eq hW _
    (hf.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin d)))

/-- The Gaussian potential is the `L²` Green pairing of the transported noise. -/
theorem sandpile_isSpatialGreenPairing {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) (v : ℝ)
    (Z : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hZ : ∀ t x, 0 ≤ t → (fun ω => Z ω t x) =ᵐ[P]
      fun ω => Sandpile.Continuum.gaussianPotential d v W t (WithLp.toLp 2 x) ω) :
    IsSpatialGreenPairing d v P
      (fun φ ω => Real.sqrt v * W (fun y => φ (WithLp.ofLp y)) ω) Z := by
  let I := Real.sqrt v • sandpileNoiseMap hW
  refine ⟨I, ?_, ?_, ?_⟩
  · intro f
    simp only [I, smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg v), norm_sandpileNoiseMap]
  · intro φ hφ
    have hf : MemLp φ 2 volume := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2
    refine ⟨hf, ?_⟩
    filter_upwards [Lp.coeFn_smul (Real.sqrt v) (sandpileNoiseMap hW (hf.toLp φ)),
      sandpileNoiseMap_toLp_ae_eq hW φ hf] with ω h₁ h₂
    simpa only [I, smul_apply, Pi.smul_apply, smul_eq_mul, h₂] using h₁
  · intro t x ht
    have hg := memLp_contFiniteGreen d hd hd3 t ht x
    refine ⟨hg, ?_⟩
    filter_upwards [Lp.coeFn_smul (Real.sqrt v)
      (sandpileNoiseMap hW (hg.toLp (External.contFiniteGreen d t x))),
      sandpileNoiseMap_toLp_ae_eq hW (External.contFiniteGreen d t x) hg,
      hZ t x ht] with ω h₁ h₂ h₃
    have heq : (fun y : Sandpile.Continuum.Space d =>
        External.contFiniteGreen d t x (WithLp.ofLp y)) =
        Sandpile.Continuum.greenTimeBM d t (WithLp.toLp 2 x) := by
      funext y
      simpa only [WithLp.toLp_ofLp] using
        contFiniteGreen_eq_greenTimeBM d t ht x (WithLp.ofLp y)
    simp only [heq] at h₂
    simpa only [I, smul_apply, Pi.smul_apply, smul_eq_mul, h₂,
      Sandpile.Continuum.gaussianPotential, h₃] using h₁

/-- Spatial integration is preserved by the Euclidean coordinate equivalence. -/
theorem integral_comp_ofLp (d : ℕ) (f : (Fin d → ℝ) → ℝ) :
    (∫ y : Sandpile.Continuum.Space d, f (WithLp.ofLp y)) = ∫ x, f x := by
  exact (PiLp.volume_preserving_ofLp (Fin d)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding f

/-- The spatial mass of the finite-time Green kernel is its time horizon. -/
theorem integral_contFiniteGreen (d : ℕ) (hd : 1 ≤ d) (t : ℝ) (ht : 0 ≤ t)
    (x : Fin d → ℝ) : (∫ y, External.contFiniteGreen d t x y) = t := by
  rw [← integral_comp_ofLp d (External.contFiniteGreen d t x)]
  simp_rw [contFiniteGreen_eq_greenTimeBM d t ht]
  simpa only [WithLp.toLp_ofLp] using
    (Sandpile.Support.integrable_greenTimeBM_and_integral_eq hd ht (WithLp.toLp 2 x)).2

/-- Two distinct heat-kernel centers can be separated by a spatial point. -/
theorem heatKernelBM_lt_at_reflection {d : ℕ} (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a)
    (x z : Sandpile.Continuum.Space d) (hxz : x ≠ z) :
    Sandpile.Continuum.heatKernelBM d a z (x + (x - z)) <
      Sandpile.Continuum.heatKernelBM d a x (x + (x - z)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hn : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
  have hx : x - (x + (x - z)) = -(x - z) := by abel
  have hz : z - (x + (x - z)) = -((2 : ℝ) • (x - z)) := by
    simp only [two_smul]
    abel
  have hnorm : ‖x - (x + (x - z))‖ ^ 2 < ‖z - (x + (x - z))‖ ^ 2 := by
    rw [hx, hz, norm_neg, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [sq_pos_of_pos hn]
  unfold Sandpile.Continuum.heatKernelBM
  apply mul_lt_mul_of_pos_left _ (Real.rpow_pos_of_pos (by positivity) _)
  apply Real.exp_lt_exp.mpr
  have hden : 0 < 2 * a := by positivity
  apply (div_lt_div_iff_of_pos_right hden).2
  nlinarith

/-- Distinct positive-time Green kernels differ at a point off both diagonals. -/
theorem greenTimeBM_lt_at_reflection {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t)
    (x z : Sandpile.Continuum.Space d) (hxz : x ≠ z) :
    Sandpile.Continuum.greenTimeBM d t z (x + (x - z)) <
      Sandpile.Continuum.greenTimeBM d t x (x + (x - z)) := by
  let y := x + (x - z)
  have hx : x ≠ y := by
    intro heq
    apply hxz
    dsimp [y] at heq
    have h : x - z = 0 := by
      have := congrArg (fun w : Sandpile.Continuum.Space d => w - x) heq
      simpa using this.symm
    exact sub_eq_zero.mp h
  have hz : z ≠ y := by
    intro heq
    apply hxz
    dsimp [y] at heq
    have hid : z - (x + (x - z)) = -((2 : ℝ) • (x - z)) := by
      simp only [two_smul]
      abel
    have h : (2 : ℝ) • (x - z) = 0 := by
      have hzero : z - (x + (x - z)) = 0 := sub_eq_zero.mpr heq
      simpa only [hid, neg_eq_zero] using hzero
    exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_left (by norm_num))
  have hxi := Sandpile.Support.integrableOn_heatKernelBM_time hd (t := t) hx
  have hzi := Sandpile.Support.integrableOn_heatKernelBM_time hd (t := t) hz
  have hlt : ∀ a : ℝ, 0 < a →
      Sandpile.Continuum.heatKernelBM d a z y < Sandpile.Continuum.heatKernelBM d a x y :=
    fun _ ha => heatKernelBM_lt_at_reflection hd ha x z hxz
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) t)]
      (fun a => Sandpile.Continuum.heatKernelBM d a x y -
        Sandpile.Continuum.heatKernelBM d a z y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
    exact (sub_pos.mpr (hlt a ha.1)).le
  have hpos : 0 < ∫ a in Set.Ioo (0 : ℝ) t,
      (Sandpile.Continuum.heatKernelBM d a x y - Sandpile.Continuum.heatKernelBM d a z y) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg (hxi.sub hzi)]
    refine ((Measure.measure_Ioo_pos volume).2 ht).trans_le (measure_mono ?_)
    intro a ha
    exact ⟨ne_of_gt (sub_pos.mpr (hlt a ha.1)), ha⟩
  rw [integral_sub hxi hzi] at hpos
  change Sandpile.Continuum.greenTimeBM d t z y < Sandpile.Continuum.greenTimeBM d t x y
  rw [Sandpile.Continuum.greenTimeBM, Sandpile.Continuum.greenTimeBM,
    intervalIntegral.integral_of_le ht.le, intervalIntegral.integral_of_le ht.le,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  linarith

/-- A positive-time Green kernel determines both its horizon and its center. -/
theorem contFiniteGreen_inj {d : ℕ} (hd : 1 ≤ d) {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (x z : Fin d → ℝ) (h : External.contFiniteGreen d t x = External.contFiniteGreen d s z) :
    t = s ∧ x = z := by
  have hts : t = s := by
    calc
      t = ∫ y, External.contFiniteGreen d t x y := (integral_contFiniteGreen d hd t ht.le x).symm
      _ = ∫ y, External.contFiniteGreen d s z y := by rw [h]
      _ = s := integral_contFiniteGreen d hd s hs.le z
  refine ⟨hts, ?_⟩
  subst s
  by_contra hxz
  have hne : (WithLp.toLp 2 x : Sandpile.Continuum.Space d) ≠ WithLp.toLp 2 z := by
    intro heq
    exact hxz (congrArg WithLp.ofLp heq)
  let y : Sandpile.Continuum.Space d := WithLp.toLp 2 x + (WithLp.toLp 2 x - WithLp.toLp 2 z)
  have hlt := greenTimeBM_lt_at_reflection hd ht (WithLp.toLp 2 x) (WithLp.toLp 2 z) hne
  have heq := congrFun h (WithLp.ofLp y)
  rw [contFiniteGreen_eq_greenTimeBM d t ht.le x (WithLp.ofLp y),
    contFiniteGreen_eq_greenTimeBM d t ht.le z (WithLp.ofLp y)] at heq
  simp only [WithLp.toLp_ofLp] at heq
  exact (ne_of_gt hlt) heq

/-- A test function remains square integrable in Euclidean coordinates. -/
theorem memLp_test_comp_ofLp {d : ℕ} (φ : (Fin d → ℝ) → ℝ) (hφ : IsTestFun φ) :
    MemLp (fun y : Sandpile.Continuum.Space d => φ (WithLp.ofLp y)) 2 volume :=
  (hφ.1.continuous.memLp_of_hasCompactSupport hφ.2).comp_measurePreserving
    (PiLp.volume_preserving_ofLp (Fin d))

/-- The transported Sandpile noise is measurable at every spatial test function. -/
theorem measurable_sandpileNoise {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) (v : ℝ)
    (φ : (Fin d → ℝ) → ℝ) (hφ : IsTestFun φ) :
    Measurable (fun ω => Real.sqrt v * W (fun y => φ (WithLp.ofLp y)) ω) :=
  (hW.meas _ (memLp_test_comp_ofLp φ hφ)).const_mul (Real.sqrt v)

/-- Sandpile white noise transported to coordinates and scaled by `√v`. -/
theorem sandpile_isSpatialWhiteNoise {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) (v : ℝ) (hv : 0 ≤ v) :
    IsSpatialWhiteNoise d v P
      (fun φ ω => Real.sqrt v * W (fun y => φ (WithLp.ofLp y)) ω) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro φ ψ hφ hψ a b
    let f : Sandpile.Continuum.Space d → ℝ := fun y => φ (WithLp.ofLp y)
    let g : Sandpile.Continuum.Space d → ℝ := fun y => ψ (WithLp.ofLp y)
    have hf : MemLp f 2 volume := memLp_test_comp_ofLp φ hφ
    have hg : MemLp g 2 volume := memLp_test_comp_ofLp ψ hψ
    filter_upwards [hW.add (a • f) (b • g) (hf.const_smul a) (hg.const_smul b),
      hW.smul a f hf, hW.smul b g hg] with ω hadd ha hb
    change Real.sqrt v * W (a • f + b • g) ω = _
    rw [hadd, ha, hb]
    ring
  · intro φ hφ
    let f : Sandpile.Continuum.Space d → ℝ := fun y => φ (WithLp.ofLp y)
    have hf : MemLp f 2 volume := memLp_test_comp_ofLp φ hφ
    constructor
    · exact ((hW.gaussian.hasGaussianLaw_eval f).memLp_two.integrable (by norm_num)).const_mul _
    · rw [integral_const_mul, hW.mean f hf, mul_zero]
  · intro φ ψ hφ hψ
    let f : Sandpile.Continuum.Space d → ℝ := fun y => φ (WithLp.ofLp y)
    let g : Sandpile.Continuum.Space d → ℝ := fun y => ψ (WithLp.ofLp y)
    have hf : MemLp f 2 volume := memLp_test_comp_ofLp φ hφ
    have hg : MemLp g 2 volume := memLp_test_comp_ofLp ψ hψ
    have hfm := (hW.gaussian.hasGaussianLaw_eval f).memLp_two.const_mul (Real.sqrt v)
    have hgm := (hW.gaussian.hasGaussianLaw_eval g).memLp_two.const_mul (Real.sqrt v)
    refine ⟨hfm.integrable_mul hgm, ?_⟩
    have hs : Real.sqrt v * Real.sqrt v = v := by rw [← sq, Real.sq_sqrt hv]
    calc
      _ = ∫ ω, v * (W f ω * W g ω) ∂P := by
        apply integral_congr_ae
        filter_upwards with ω
        change Real.sqrt v * W f ω * (Real.sqrt v * W g ω) = v * (W f ω * W g ω)
        calc
          _ = (Real.sqrt v * Real.sqrt v) * (W f ω * W g ω) := by ring
          _ = _ := by rw [hs]
      _ = v * ∫ y, f y * g y := by rw [integral_const_mul, hW.cov f g hf hg]
      _ = _ := by rw [integral_comp_ofLp d (fun x => φ x * ψ x)]
  · intro φ hφ
    let f : Sandpile.Continuum.Space d → ℝ := fun y => φ (WithLp.ofLp y)
    have hf : MemLp f 2 volume := memLp_test_comp_ofLp φ hφ
    have hvar : variance (W f) P = ∫ y, f y * f y := by
      rw [variance_eq_integral (hW.meas f hf).aemeasurable, hW.mean f hf]
      simp only [sub_zero]
      rw [← hW.cov f f hf hf]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => sq (W f ω))
    have hmap : P.map (W f) = gaussianReal 0 (Real.toNNReal (∫ y, f y * f y)) := by
      rw [(hW.gaussian.hasGaussianLaw_eval f).map_eq_gaussianReal, hW.mean f hf, hvar]
    have hint : (∫ y, f y * f y) = ∫ x, φ x ^ 2 := by
      simpa only [f, sq] using integral_comp_ofLp d (fun x => φ x * φ x)
    refine ⟨(v * ∫ x, φ x ^ 2).toNNReal,
      Real.coe_toNNReal _ (mul_nonneg hv (integral_nonneg fun x => sq_nonneg _)), ?_⟩
    change P.map ((fun x : ℝ => Real.sqrt v * x) ∘ W f) = _
    rw [← Measure.map_map (by fun_prop) (hW.meas f hf), hmap, hint,
      gaussianReal_map_const_mul]
    congr 1
    · ring
    · rw [Real.toNNReal_mul hv]
      congr 1
      rw [Real.toNNReal_of_nonneg hv]
      apply NNReal.eq
      exact Real.sq_sqrt hv

/-- The coordinate noise and every version of the Gaussian potential form a Green pairing. -/
theorem parking_noise_of_sandpile {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) (v : ℝ) (hv : 0 ≤ v) :
    IsSpatialWhiteNoise d v P
        (fun φ ω => Real.sqrt v * W (fun y => φ (WithLp.ofLp y)) ω) ∧
      (∀ φ, IsTestFun φ →
        Measurable (fun ω => Real.sqrt v * W (fun y => φ (WithLp.ofLp y)) ω)) ∧
      ∀ Z : Ω → ℝ → (Fin d → ℝ) → ℝ,
        (∀ t x, 0 ≤ t → (fun ω => Z ω t x) =ᵐ[P]
          fun ω => Sandpile.Continuum.gaussianPotential d v W t (WithLp.toLp 2 x) ω) →
        IsSpatialGreenPairing d v P
          (fun φ ω => Real.sqrt v * W (fun y => φ (WithLp.ofLp y)) ω) Z :=
  ⟨sandpile_isSpatialWhiteNoise hW v hv, measurable_sandpileNoise hW v,
    sandpile_isSpatialGreenPairing hd hd3 hW v⟩

/-- Extend prescribed test coordinates to an injectively indexed family disjoint from the tests. -/
theorem exists_noise_with_prescribed_coordinates {X Ω A : Type*}
    (test : (X → ℝ) → Prop) (kernel : A → X → ℝ)
    (hinj : Function.Injective kernel) (hdisjoint : ∀ a, ¬ test (kernel a))
    (W : (X → ℝ) → Ω → ℝ) (Y : A → Ω → ℝ) :
    ∃ W' : (X → ℝ) → Ω → ℝ,
      (∀ f, test f → W' f = W f) ∧ ∀ a, W' (kernel a) = Y a := by
  classical
  let W' : (X → ℝ) → Ω → ℝ := fun f =>
    if test f then W f
    else if h : ∃ a, kernel a = f then Y (Classical.choose h) else 0
  refine ⟨W', ?_, ?_⟩
  · intro f hf
    simp [W', hf]
  · intro a
    have h : ∃ b, kernel b = kernel a := ⟨a, rfl⟩
    have heq : Classical.choose h = a := hinj (Classical.choose_spec h)
    simp only [W', ite_eq_right (hdisjoint a), dite_eq_left h, heq]

end Parking
