import Parking.Support.SandpileNoiseBridge
import Parking.Support.SpatialNoiseCongruence
import Sandpile.Support.MeanAVersion
import Sandpile.Support.LimFieldVersion

/-!
# Continuous versions of the finite-time Green field
-/

open MeasureTheory Filter Topology
open Sandpile.Continuum
open scoped NNReal

namespace Parking

/-- The zero coordinate of Sandpile white noise vanishes almost surely. -/
theorem sandpile_whiteNoise_zero_ae {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) : W 0 =ᵐ[P] (fun _ => 0) := by
  have h := hW.smul 0 (0 : Sandpile.Continuum.Space d → ℝ) (by simp)
  simpa only [zero_smul, zero_mul] using h

/-- Prescribed test coordinates can be extended to pair a zero-at-zero field with Green kernels. -/
theorem exists_noise_with_green_coordinates {d : ℕ} (hd : 1 ≤ d) (v : ℝ) (hv : 0 < v)
    {Ω : Type} (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ)
    (Z : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hW0 : ∀ ω, W 0 ω = 0) (hZ0 : ∀ ω x, Z ω 0 x = 0) :
    ∃ W' : ((Fin d → ℝ) → ℝ) → Ω → ℝ,
      (∀ φ, IsTestFun φ → W' φ = W φ) ∧
      (∀ ω t x, 0 ≤ t → Z ω t x = Real.sqrt v * W' (External.contFiniteGreen d t x) ω) := by
  classical
  let A := {p : ℝ × (Fin d → ℝ) // 0 < p.1}
  let K : A → (Fin d → ℝ) → ℝ := fun p => External.contFiniteGreen d p.1.1 p.1.2
  have hK : Function.Injective K := by
    intro p q hpq
    obtain ⟨ht, hx⟩ := contFiniteGreen_inj hd p.2 q.2 p.1.2 q.1.2 hpq
    exact Subtype.ext (Prod.ext ht hx)
  have hdis : ∀ p : A, ¬ IsTestFun (K p) :=
    fun p => not_isTestFun_contFiniteGreen hd p.2 p.1.2
  obtain ⟨W', htest, hgreen⟩ := exists_noise_with_prescribed_coordinates
    IsTestFun K hK hdis W (fun p ω => Z ω p.1.1 p.1.2 / Real.sqrt v)
  refine ⟨W', htest, ?_⟩
  intro ω t x ht
  rcases ht.eq_or_lt with rfl | ht
  · have hz : External.contFiniteGreen d 0 x = 0 := by
      ext y
      simp [External.contFiniteGreen]
    rw [hz, htest 0 ⟨contDiff_const, HasCompactSupport.zero⟩, hW0 ω, mul_zero, hZ0]
  · have hg := congrFun (hgreen ⟨(t, x), ht⟩) ω
    have hs : Real.sqrt v ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hv)
    change W' (External.contFiniteGreen d t x) ω = Z ω t x / Real.sqrt v at hg
    rw [hg]
    exact (mul_div_cancel₀ (Z ω t x) hs).symm

/-- Stripwise almost-sure continuity gives continuity on nonnegative time. -/
theorem ae_continuous_of_strips {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (F : ℝ → Space d → Ω → ℝ)
    (hF : ∀ n : ℕ, ∀ᵐ ω ∂P,
      ContinuousOn (fun p : ℝ × Space d => F p.1 p.2 ω)
        (Set.Icc (0 : ℝ) ((n : ℝ) + 1) ×ˢ (Set.univ : Set (Space d)))) :
    ∀ᵐ ω ∂P, Continuous (fun p : ℝ≥0 × (Fin d → ℝ) => F p.1 (WithLp.toLp 2 p.2) ω) := by
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ContinuousOn (fun p : ℝ × Space d => F p.1 p.2 ω)
        (Set.Icc (0 : ℝ) ((n : ℝ) + 1) ×ˢ (Set.univ : Set (Space d))) :=
    ae_all_iff.mpr hF
  filter_upwards [hall] with ω hω
  apply continuous_iff_continuousAt.mpr
  intro p
  let n := ⌈(p.1 : ℝ)⌉₊
  let U : Set (ℝ≥0 × (Fin d → ℝ)) := {q | (q.1 : ℝ) < (n : ℝ) + 1}
  have hopen : IsOpen U := isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const
  have hp : p ∈ U := by
    dsimp [U, n]
    have := Nat.le_ceil (p.1 : ℝ)
    linarith
  have hmap : Continuous (fun q : ℝ≥0 × (Fin d → ℝ) =>
      ((q.1 : ℝ), (WithLp.toLp 2 q.2 : Space d))) := by
    exact (continuous_subtype_val.comp continuous_fst).prodMk
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.continuous.comp continuous_snd)
  have hmaps : Set.MapsTo (fun q : ℝ≥0 × (Fin d → ℝ) =>
      ((q.1 : ℝ), (WithLp.toLp 2 q.2 : Space d))) U
      (Set.Icc (0 : ℝ) ((n : ℝ) + 1) ×ˢ (Set.univ : Set (Space d))) := by
    intro q hq
    exact ⟨⟨q.1.2, hq.le⟩, Set.mem_univ _⟩
  exact ((hω n).comp hmap.continuousOn hmaps).continuousAt (hopen.mem_nhds hp)

/-- The Gaussian potential has a measurable, everywhere continuous version. -/
theorem exists_measurable_continuous_gaussianPotential {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {v : ℝ} (hv : 0 ≤ v)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (Space d → ℝ) → Ω → ℝ) (hW : IsWhiteNoise d W P) :
    ∃ Y : (ℝ≥0 × (Fin d → ℝ)) → Ω → ℝ,
      (∀ p, Measurable (Y p)) ∧ (∀ ω, Continuous fun p => Y p ω) ∧
      ∀ p, Y p =ᵐ[P] fun ω => gaussianPotential d v W p.1 (WithLp.toLp 2 p.2) ω := by
  obtain ⟨F, hFmod, hFcont⟩ := Sandpile.Support.exists_continuous_version hd hd3 hv P W hW
  let F' : (ℝ≥0 × (Fin d → ℝ)) → Ω → ℝ :=
    fun p ω => F p.1 (WithLp.toLp 2 p.2) ω
  let X : (ℝ≥0 × (Fin d → ℝ)) → Ω → ℝ :=
    fun p ω => gaussianPotential d v W p.1 (WithLp.toLp 2 p.2) ω
  have hX : ∀ p, Measurable (X p) := by
    intro p
    exact (hW.meas _ (Sandpile.Support.memLp_greenTimeBM hd hd3 p.1.2
      (WithLp.toLp 2 p.2))).const_mul (Real.sqrt v)
  have hFX : ∀ p, F' p =ᵐ[P] X p := fun p => hFmod p.1 (WithLp.toLp 2 p.2)
  have hcont : ∀ᵐ ω ∂P, Continuous fun p => F' p ω :=
    ae_continuous_of_strips F (fun n => hFcont ((n : ℝ) + 1) (by positivity))
  obtain ⟨Y, hYm, hYc, hYeq⟩ :=
    Sandpile.Support.exists_measurable_continuous_version F' X hX hFX hcont
  refine ⟨Y, hYm, hYc, ?_⟩
  intro p
  filter_upwards [hYeq, hFX p] with ω hω hω'
  exact (hω p).trans hω'

/-- Every continuous version of the Gaussian potential vanishes initially almost surely. -/
theorem ae_zero_time {d : ℕ} {v : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (Y : (ℝ≥0 × (Fin d → ℝ)) → Ω → ℝ)
    (hYcont : ∀ ω, Continuous fun p => Y p ω)
    (hYmod : ∀ p, Y p =ᵐ[P] fun ω => gaussianPotential d v W p.1 (WithLp.toLp 2 p.2) ω) :
    ∀ᵐ ω ∂P, ∀ x, Y (0, x) ω = 0 := by
  have hzero : W 0 =ᵐ[P] (fun _ => 0) := by
    have h := hW.smul 0 (0 : Space d → ℝ) (by simp)
    simpa only [zero_smul, zero_mul] using h
  have hmod : ∀ x : Fin d → ℝ, (fun ω => Y (0, x) ω) =ᵐ[P] fun _ => 0 := by
    intro x
    filter_upwards [hYmod (0, x), hzero] with ω hω hz
    rw [hω]
    simp only [NNReal.coe_zero, gaussianPotential]
    have hg : (fun y : Space d => greenTimeBM d 0 (WithLp.toLp 2 x) y) = 0 := by
      ext y
      simp [greenTimeBM]
    rw [hg, hz, mul_zero]
  apply Sandpile.Support.ae_forall_eq_of_continuous_modifications P
    (fun x ω => Y (0, x) ω) (fun _ _ => 0)
  · exact Filter.Eventually.of_forall fun ω => (hYcont ω).comp (continuous_const.prodMk continuous_id)
  · exact Filter.Eventually.of_forall fun _ => continuous_const
  · exact hmod

/-- Extending a continuous field by its time-zero value preserves continuity. -/
theorem continuous_extend_nonnegative {d : ℕ} {Ω : Type}
    (Y : (ℝ≥0 × (Fin d → ℝ)) → Ω → ℝ)
    (hY : ∀ ω, Continuous fun p => Y p ω) (ω : Ω) :
    Continuous fun p : ℝ × (Fin d → ℝ) => Y (Real.toNNReal p.1, p.2) ω :=
  (hY ω).comp ((continuous_real_toNNReal.comp continuous_fst).prodMk continuous_snd)

/-- A continuous Gaussian potential admits a measurable version with growth on every strip. -/
theorem exists_everywhere_regular_version {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {v : ℝ} (hv : 0 ≤ v) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (Space d → ℝ) → Ω → ℝ) (hW : IsWhiteNoise d W P)
    (Y : (ℝ≥0 × (Fin d → ℝ)) → Ω → ℝ)
    (hYm : ∀ p, Measurable (Y p)) (hYc : ∀ ω, Continuous fun p => Y p ω)
    (hYmod : ∀ p, Y p =ᵐ[P] fun ω => gaussianPotential d v W p.1 (WithLp.toLp 2 p.2) ω) :
    ∃ Z : Ω → ℝ → (Fin d → ℝ) → ℝ,
      (∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Z ω p.1 p.2) ∧
      (∀ t x, Measurable fun ω => Z ω t x) ∧
      (∀ t x, 0 ≤ t → (fun ω => Z ω t x) =ᵐ[P]
        fun ω => gaussianPotential d v W t (WithLp.toLp 2 x) ω) ∧
      (∀ ω x, Z ω 0 x = 0) ∧
      (∀ ω T, 0 < T → ∃ C k : ℝ, ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Fin d → ℝ)),
        |Z ω p.1 p.2| ≤ C * (1 + ‖p.2‖) ^ k) := by
  classical
  let Y' : ℝ × (Fin d → ℝ) → Ω → ℝ := fun p => Y (Real.toNNReal p.1, p.2)
  have hY'm : ∀ p, Measurable (Y' p) := fun p => hYm _
  have hY'c : ∀ ω, Continuous fun p => Y' p ω := continuous_extend_nonnegative Y hYc
  have hY'mod : ∀ p : ℝ × (Fin d → ℝ), 0 ≤ p.1 → Y' p =ᵐ[P]
      fun ω => gaussianPotential d v W p.1 (WithLp.toLp 2 p.2) ω := by
    intro p hp
    have h := hYmod (Real.toNNReal p.1, p.2)
    simpa only [Y', Real.coe_toNNReal p.1 hp] using h
  have hzero := ae_zero_time hW Y hYc hYmod
  have henvelope : ∀ n : ℕ, ∀ᵐ ω ∂P, ∃ C : ℝ,
      ∀ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1), ∀ x : Space d,
        |Y' (t, WithLp.ofLp x) ω| ≤ C * (1 + ‖x‖) := by
    intro n
    apply Sandpile.Support.exists_ae_linear_envelope hd hd3 hv (by positivity) P W hW
      Y' hY'm _ hY'c
    intro p hp
    exact hY'mod p hp.1
  have hgood : ∀ᵐ ω ∂P, (∀ x, Y (0, x) ω = 0) ∧ ∀ n : ℕ, ∃ C : ℝ,
      ∀ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1), ∀ x : Space d,
        |Y' (t, WithLp.ofLp x) ω| ≤ C * (1 + ‖x‖) :=
    hzero.and (ae_all_iff.mpr henvelope)
  obtain ⟨N, hNsub, hNm, hNnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  let Z : Ω → ℝ → (Fin d → ℝ) → ℝ := fun ω t x => if ω ∈ N then 0 else Y' (t, x) ω
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa using hNnull
  refine ⟨Z, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ N
    · simpa only [Z, ite_eq_left hω] using (continuous_const :
        Continuous (fun _ : ℝ × (Fin d → ℝ) => (0 : ℝ)))
    · simpa only [Z, ite_eq_right hω] using hY'c ω
  · intro t x
    exact measurable_const.ite hNm (hY'm (t, x))
  · intro t x ht
    filter_upwards [hNae, hY'mod (t, x) ht] with ω hω hω'
    simpa only [Z, ite_eq_right hω] using hω'
  · intro ω x
    by_cases hω : ω ∈ N
    · simp only [Z, ite_eq_left hω]
    · have hg := not_not.mp (fun h => hω (hNsub h))
      simpa only [Z, ite_eq_right hω, Y', Real.toNNReal_zero] using hg.1 x
  · intro ω T hT
    by_cases hω : ω ∈ N
    · refine ⟨0, 1, ?_⟩
      intro p hp
      simp only [Z, ite_eq_left hω, abs_zero, zero_mul, le_refl]
    · have hg := not_not.mp (fun h => hω (hNsub h))
      let n := ⌈T⌉₊
      obtain ⟨C, hC⟩ := hg.2 n
      let L : (Fin d → ℝ) →L[ℝ] Space d :=
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap
      let M : ℝ := max 1 ‖L‖
      have hM : 1 ≤ M := le_max_left _ _
      have hLM : ‖L‖ ≤ M := le_max_right _ _
      refine ⟨|C| * M, 1, ?_⟩
      intro p hp
      have ht : p.1 ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1) := ⟨hp.1.1, by
        have hceil : T ≤ n := Nat.le_ceil T
        linarith [hp.1.2]⟩
      have hb := hC p.1 ht (WithLp.toLp 2 p.2)
      have hL : ‖(WithLp.toLp 2 p.2 : Space d)‖ ≤ ‖L‖ * ‖p.2‖ := L.le_opNorm p.2
      have harg : 1 + ‖(WithLp.toLp 2 p.2 : Space d)‖ ≤ M * (1 + ‖p.2‖) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hLM) (norm_nonneg p.2)]
      have hb' : |Y' (p.1, p.2) ω| ≤ |C| * (M * (1 + ‖p.2‖)) :=
        hb.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
          (mul_le_mul_of_nonneg_left harg (abs_nonneg C)))
      simpa only [Z, ite_eq_right hω, Real.rpow_one, mul_assoc] using hb'

/-- Products of coordinatewise versions of scaled white noise have the expected integral. -/
theorem scaled_whiteNoise_product {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (f g : Space d → ℝ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (a b : ℝ) (X Y : Ω → ℝ)
    (hX : X =ᵐ[P] fun ω => a * W f ω) (hY : Y =ᵐ[P] fun ω => b * W g ω) :
    Integrable (fun ω => X ω * Y ω) P ∧
      ∫ ω, X ω * Y ω ∂P = (a * b) * ∫ x, f x * g x := by
  have hXm : MemLp X 2 P := (memLp_congr_ae hX).2 ((hW.gaussian.hasGaussianLaw_eval f).memLp_two.const_mul a)
  have hYm : MemLp Y 2 P := (memLp_congr_ae hY).2 ((hW.gaussian.hasGaussianLaw_eval g).memLp_two.const_mul b)
  refine ⟨hXm.integrable_mul hYm, ?_⟩
  calc
    _ = ∫ ω, (a * b) * (W f ω * W g ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [hX, hY] with ω hx hy
      rw [hx, hy]
      ring
    _ = _ := by rw [integral_const_mul, hW.cov f g hf hg]

/-- The covariance of any coordinatewise version of the Gaussian potential. -/
theorem gaussianPotential_version_covariance {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {v : ℝ} (hv : 0 ≤ v) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (Z : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hZ : ∀ t x, 0 ≤ t → (fun ω => Z ω t x) =ᵐ[P]
      fun ω => gaussianPotential d v W t (WithLp.toLp 2 x) ω)
    (r s : ℝ) (x y : Fin d → ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    Integrable (fun ω => Z ω r x * Z ω s y) P ∧
      ∫ ω, Z ω r x * Z ω s y ∂P =
        v * ∫ a in Set.Ioc (0 : ℝ) r, ∫ b in Set.Ioc (0 : ℝ) s,
          External.contHeatKernel d (a + b) x y := by
  have h := scaled_whiteNoise_product hW
    (greenTimeBM d r (WithLp.toLp 2 x)) (greenTimeBM d s (WithLp.toLp 2 y))
    (Sandpile.Support.memLp_greenTimeBM hd hd3 hr _) (Sandpile.Support.memLp_greenTimeBM hd hd3 hs _)
    (Real.sqrt v) (Real.sqrt v) (fun ω => Z ω r x) (fun ω => Z ω s y)
    (hZ r x hr) (hZ s y hs)
  refine ⟨h.1, ?_⟩
  rw [h.2, ← sq, Real.sq_sqrt hv,
    Sandpile.Support.integral_greenTimeBM_mul_two_interval hd hd3 hr hs,
    intervalIntegral.integral_of_le hr]
  congr 1
  apply integral_congr_ae
  filter_upwards with a
  rw [intervalIntegral.integral_of_le hs]
  apply integral_congr_ae
  filter_upwards with b
  have hnorm : ‖(WithLp.toLp 2 x : Space d) - WithLp.toLp 2 y‖ ^ 2 =
      ∑ i, (x i - y i) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  simp only [External.contHeatKernel, heatKernelBM, hnorm]

/-- The covariance of a transported test coordinate and a Gaussian potential version. -/
theorem gaussianPotential_version_test_covariance {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {v : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {WD : (Space d → ℝ) → Ω → ℝ} (hWD : IsWhiteNoise d WD P)
    (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ) (Z : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hW : ∀ φ, IsTestFun φ → W φ =ᵐ[P] WD (fun y => φ (WithLp.ofLp y)))
    (hZ : ∀ t x, 0 ≤ t → (fun ω => Z ω t x) =ᵐ[P]
      fun ω => gaussianPotential d v WD t (WithLp.toLp 2 x) ω)
    (φ : (Fin d → ℝ) → ℝ) (hφ : IsTestFun φ) (t : ℝ) (x : Fin d → ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω => W φ ω * Z ω t x) P ∧
      ∫ ω, W φ ω * Z ω t x ∂P =
        Real.sqrt v * ∫ y, φ y * External.contFiniteGreen d t x y := by
  have h := scaled_whiteNoise_product hWD (fun y => φ (WithLp.ofLp y))
    (greenTimeBM d t (WithLp.toLp 2 x)) (memLp_test_comp_ofLp φ hφ)
    (Sandpile.Support.memLp_greenTimeBM hd hd3 ht _) 1 (Real.sqrt v)
    (W φ) (fun ω => Z ω t x) (by simpa only [one_mul] using hW φ hφ) (hZ t x ht)
  refine ⟨h.1, ?_⟩
  rw [h.2, one_mul, ← integral_comp_ofLp d (fun y => φ y * External.contFiniteGreen d t x y)]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  rw [contFiniteGreen_eq_greenTimeBM d t ht x (WithLp.ofLp y)]

/-- A continuous Green field and its spatial white noise on a common probability space. -/
theorem exists_continuous_green_field (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (v : ℝ) (hv : 0 < v) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (WD : (Space d → ℝ) → Ω → ℝ)
      (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ) (Z : Ω → ℝ → (Fin d → ℝ) → ℝ),
      IsWhiteNoise d WD P ∧
      (∀ φ, IsTestFun φ → W φ =ᵐ[P] WD (fun y => φ (WithLp.ofLp y))) ∧
      (∀ t x, 0 ≤ t → (fun ω => Z ω t x) =ᵐ[P]
        fun ω => gaussianPotential d v WD t (WithLp.toLp 2 x) ω) ∧
      (∀ ω, Continuous fun p : ℝ × (Fin d → ℝ) => Z ω p.1 p.2) ∧
      (∀ ω T, 0 < T → ∃ C k : ℝ, ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Fin d → ℝ)),
        |Z ω p.1 p.2| ≤ C * (1 + ‖p.2‖) ^ k) ∧
      IsSpatialWhiteNoise d 1 P W ∧
      (∀ φ, IsTestFun φ → Measurable (W φ)) ∧
      (∀ ω t x, 0 ≤ t → Z ω t x = Real.sqrt v * W (External.contFiniteGreen d t x) ω) ∧
      (∀ ω x, Z ω 0 x = 0) ∧
      (∀ t x, Measurable fun ω => Z ω t x) ∧
      (∀ r x s y, 0 ≤ r → 0 ≤ s →
        Integrable (fun ω => Z ω r x * Z ω s y) P ∧
        ∫ ω, Z ω r x * Z ω s y ∂P =
          v * ∫ a in Set.Ioc (0 : ℝ) r, ∫ b in Set.Ioc (0 : ℝ) s,
            External.contHeatKernel d (a + b) x y) ∧
      (∀ φ, IsTestFun φ → ∀ t x, 0 ≤ t →
        Integrable (fun ω => W φ ω * Z ω t x) P ∧
        ∫ ω, W φ ω * Z ω t x ∂P =
          Real.sqrt v * ∫ y, φ y * External.contFiniteGreen d t x y) := by
  classical
  obtain ⟨Ω, mΩ, P, hP, WD, hWD⟩ := Sandpile.Continuum.exists_isWhiteNoise d
  let _ : MeasurableSpace Ω := mΩ
  let _ : IsProbabilityMeasure P := hP
  obtain ⟨Y, hYm, hYc, hYmod⟩ := exists_measurable_continuous_gaussianPotential hd hd3 hv.le P WD hWD
  obtain ⟨Z, hZc, hZm, hZmod, hZ0, hZgrowth⟩ :=
    exists_everywhere_regular_version hd hd3 hv.le P WD hWD Y hYm hYc hYmod
  let W0 : ((Fin d → ℝ) → ℝ) → Ω → ℝ :=
    fun φ ω => if φ = 0 then 0 else WD (fun y => φ (WithLp.ofLp y)) ω
  have hW0eq : ∀ φ, W0 φ =ᵐ[P] WD (fun y => φ (WithLp.ofLp y)) := by
    intro φ
    by_cases hφ : φ = 0
    · subst φ
      have hz : (fun y : Space d => (0 : (Fin d → ℝ) → ℝ) (WithLp.ofLp y)) = 0 := by
        ext y
        simp only [Pi.zero_apply]
      simp only [W0, ite_true, hz]
      exact (sandpile_whiteNoise_zero_ae hWD).symm
    · exact Filter.Eventually.of_forall fun ω => by simp only [W0, ite_eq_right hφ]
  have hW0m : ∀ φ, IsTestFun φ → Measurable (W0 φ) := by
    intro φ hφ
    by_cases hz : φ = 0
    · simp only [W0, hz, ↓reduceIte]; exact measurable_const
    · simpa only [W0, ite_eq_right hz] using hWD.meas _ (memLp_test_comp_ofLp φ hφ)
  obtain ⟨W, htest, hpair⟩ := exists_noise_with_green_coordinates hd v hv W0 Z
    (fun ω => by simp [W0]) hZ0
  have hWeq : ∀ φ, IsTestFun φ → W φ =ᵐ[P] WD (fun y => φ (WithLp.ofLp y)) := by
    intro φ hφ
    rw [htest φ hφ]
    exact hW0eq φ
  have hbase : IsSpatialWhiteNoise d 1 P (fun φ ω => WD (fun y => φ (WithLp.ofLp y)) ω) := by
    simpa only [Real.sqrt_one, one_mul] using sandpile_isSpatialWhiteNoise hWD 1 (by norm_num)
  refine ⟨Ω, mΩ, P, hP, WD, W, Z, hWD, hWeq, hZmod, hZc, hZgrowth,
    isSpatialWhiteNoise_congr hbase hWeq, ?_, hpair, hZ0, hZm, ?_, ?_⟩
  · intro φ hφ
    rw [htest φ hφ]
    exact hW0m φ hφ
  · intro r x s y hr hs
    exact gaussianPotential_version_covariance hd hd3 hv.le hWD Z hZmod r s x y hr hs
  · intro φ hφ t x ht
    exact gaussianPotential_version_test_covariance hd hd3 hWD W Z hWeq hZmod φ hφ t x ht

end Parking
