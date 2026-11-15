import Parking.Support.SandpileNoiseBridge
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

end Parking
