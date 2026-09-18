/-
The one-sided time mollifier of `parking.tex:1813-1814`, and the space-time test
functions it builds.

The continuum statement (S) is obtained from the distributional equation of
`prop:spatial-scaling` by testing it against `ψ_h(s,x) = ρ_h(s) φ(x)`, where `φ`
is a nonnegative test function supported where `U(1,·) > 0` and `ρ_h` is a
nonnegative smooth kernel of integral one supported in `[1, 1+h]`.  The support
of `ρ_h` is placed to the RIGHT of `s = 1` on purpose: `U` is nondecreasing in
`s`, so `U(s,x) ≥ U(1,x) > 0` for every `s ≥ 1`, and the closed support of
`ψ_h` then lies inside `{U > 0}` for EVERY `h`, which is what the equation
requires.  A kernel straddling `s = 1` would not have that property.
-/
import Parking.Support.Continuum
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Parking

/-- **The one-sided time mollifier**: nonnegative, smooth, of integral one, and
supported in `[1, 1+h]`. -/
theorem exists_timeMollifier {h : ℝ} (hh : 0 < h) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧ (∀ s, 0 ≤ ρ s) ∧
      tsupport ρ ⊆ Set.Icc (1 : ℝ) (1 + h) ∧ ∫ s, ρ s = 1 := by
  let f : ContDiffBump (1 + h / 2 : ℝ) := ⟨h / 4, h / 2, by linarith, by linarith⟩
  refine ⟨f.normed (volume : Measure ℝ), f.contDiff_normed, f.hasCompactSupport_normed,
    f.nonneg_normed, ?_, f.integral_normed⟩
  rw [f.tsupport_normed_eq]
  intro s hs
  have hb : |s - (1 + h / 2)| ≤ h / 2 := by
    simpa [Real.dist_eq] using hs
  rw [abs_le] at hb
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

/-- The closed support of a product `ρ(s) φ(x)` lies in the product of the two
closed supports. -/
theorem tsupport_mul_prod_subset {d : ℕ} (ρ : ℝ → ℝ) (φ : (Fin d → ℝ) → ℝ) :
    tsupport (fun p : ℝ × (Fin d → ℝ) => ρ p.1 * φ p.2)
      ⊆ tsupport ρ ×ˢ tsupport φ := by
  have hsupp : Function.support (fun p : ℝ × (Fin d → ℝ) => ρ p.1 * φ p.2)
      ⊆ Function.support ρ ×ˢ Function.support φ := by
    intro p hp
    have hp' : ρ p.1 * φ p.2 ≠ 0 := hp
    exact ⟨fun hc => hp' (by rw [hc, zero_mul]), fun hc => hp' (by rw [hc, mul_zero])⟩
  calc tsupport (fun p : ℝ × (Fin d → ℝ) => ρ p.1 * φ p.2)
      ⊆ closure (Function.support ρ ×ˢ Function.support φ) := closure_mono hsupp
    _ = tsupport ρ ×ˢ tsupport φ := closure_prod_eq

/-- **The product of a time kernel and a space test function is a space-time test
function.** -/
theorem isSpaceTimeTest_mul {d : ℕ} {ρ : ℝ → ℝ} {φ : (Fin d → ℝ) → ℝ}
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (hρs : ∀ s ∈ tsupport ρ, 0 < s) (hφ : IsTestFun φ) :
    IsSpaceTimeTest (fun p : ℝ × (Fin d → ℝ) => ρ p.1 * φ p.2) := by
  have hsub := tsupport_mul_prod_subset ρ φ
  refine ⟨(hρ.comp contDiff_fst).mul (hφ.1.comp contDiff_snd), ?_, ?_⟩
  · exact IsCompact.of_isClosed_subset (hρc.prod hφ.2) isClosed_closure hsub
  · intro p hp
    exact hρs p.1 (hsub hp).1

/-- **The closed support of the mollified test function lies where the continuum
field is positive**, for every `h`: the kernel sits to the right of `s = 1` and
the field is nondecreasing in time. -/
theorem tsupport_mul_subset_pos {d : ℕ} {ρ : ℝ → ℝ} {φ : (Fin d → ℝ) → ℝ}
    {U : ℝ → (Fin d → ℝ) → ℝ} {h : ℝ}
    (hρ : tsupport ρ ⊆ Set.Icc (1 : ℝ) (1 + h))
    (hmono : ∀ x, Monotone fun s => U s x)
    (hpos : ∀ x ∈ tsupport φ, 0 < U 1 x) :
    tsupport (fun p : ℝ × (Fin d → ℝ) => ρ p.1 * φ p.2)
      ⊆ {p : ℝ × (Fin d → ℝ) | 0 < U p.1 p.2} := by
  intro p hp
  obtain ⟨hp1, hp2⟩ := tsupport_mul_prod_subset ρ φ hp
  exact lt_of_lt_of_le (hpos p.2 hp2) (hmono p.2 (hρ hp1).1)

end Parking

end
