/- The finite-time Green field as the L² extension of spatial white noise. -/
import Parking.External.LinearFieldScaling
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory

noncomputable section
namespace Parking

/-- The Green field is obtained from the same noise by its continuous linear
extension to spatial `L²`. The norm identity is the white-noise isometry at
intensity `v`. Agreement with test coordinates determines the extension, since
smooth compactly supported functions are dense in spatial `L²`.

Both agreements are coordinatewise almost everywhere. In particular the Green
kernel is used as an `L²` equivalence class, independently of its diagonal value,
and `Z` may be a continuous modification of the resulting random variables. -/
def IsSpatialGreenPairing (d : ℕ) (v : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure Ω) (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ)
    (Z : Ω → ℝ → (Fin d → ℝ) → ℝ) : Prop :=
  ∃ I : Lp ℝ 2 (volume : Measure (Fin d → ℝ)) →L[ℝ] Lp ℝ 2 Q,
    (∀ f, ‖I f‖ = Real.sqrt v * ‖f‖) ∧
    (∀ φ, IsTestFun φ → ∃ hφ : MemLp φ 2 volume,
      (I (hφ.toLp φ) : Ω → ℝ) =ᵐ[Q] W φ) ∧
    (∀ t x, 0 ≤ t → ∃ hg : MemLp (External.contFiniteGreen d t x) 2 volume,
      (I (hg.toLp (External.contFiniteGreen d t x)) : Ω → ℝ) =ᵐ[Q]
        fun ω => Z ω t x)

/-- Changing the test coordinates on null sets preserves their `L²` extension
and the Green field it defines. -/
theorem IsSpatialGreenPairing.congr_noise {d : ℕ} {v : ℝ}
    {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
    {W W' : ((Fin d → ℝ) → ℝ) → Ω → ℝ} {Z : Ω → ℝ → (Fin d → ℝ) → ℝ}
    (h : IsSpatialGreenPairing d v Q W Z)
    (heq : ∀ φ, IsTestFun φ → W' φ =ᵐ[Q] W φ) :
    IsSpatialGreenPairing d v Q W' Z := by
  obtain ⟨I, hnorm, htest, hgreen⟩ := h
  refine ⟨I, hnorm, ?_, hgreen⟩
  intro φ hφ
  obtain ⟨hmem, hI⟩ := htest φ hφ
  exact ⟨hmem, hI.trans (heq φ hφ).symm⟩

end Parking
