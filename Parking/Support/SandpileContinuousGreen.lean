import Parking.Support.SandpileNoiseBridge

/-!
# Continuous versions of the finite-time Green field
-/

open MeasureTheory

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

end Parking
