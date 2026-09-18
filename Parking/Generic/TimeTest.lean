/-
Time differentiation preserves smooth compactly supported test functions. Its
integral along a time slice vanishes by the fundamental theorem of calculus.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory
noncomputable section
namespace Parking.Generic.TimeTest
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A time difference quotient of a continuous field is continuous. -/
theorem continuous_time_difference_quotient {u : ℝ × E → ℝ} (hu : Continuous u) (h : ℝ) :
    Continuous (fun p : ℝ × E => (u (p.1 + h, p.2) - u p) / h) :=
  ((hu.comp ((continuous_fst.add_const h).prodMk continuous_snd)).sub hu).div_const h

/-- The time derivative of a scalar function on space-time. -/
def timeDeriv (ψ : ℝ × E → ℝ) (p : ℝ × E) : ℝ :=
  deriv (fun s => ψ (s, p.2)) p.1

theorem timeDeriv_eq_fderiv {ψ : ℝ × E → ℝ} (hψ : Differentiable ℝ ψ) :
    timeDeriv ψ = fun p => fderiv ℝ ψ p (1, 0) := by
  funext p
  exact ((hψ p).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))).deriv

theorem contDiff_timeDeriv {ψ : ℝ × E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (timeDeriv ψ) := by
  rw [timeDeriv_eq_fderiv (hψ.differentiable (by simp))]
  exact (hψ.fderiv_right (by simp)).clm_apply contDiff_const

theorem tsupport_timeDeriv_subset {ψ : ℝ × E → ℝ}
    (hψ : Differentiable ℝ ψ) : tsupport (timeDeriv ψ) ⊆ tsupport ψ := by
  rw [timeDeriv_eq_fderiv hψ]
  exact tsupport_fderiv_apply_subset ℝ (1, 0)

theorem hasCompactSupport_timeDeriv {ψ : ℝ × E → ℝ}
    (hψ : Differentiable ℝ ψ) (hc : HasCompactSupport ψ) :
    HasCompactSupport (timeDeriv ψ) := by
  rw [timeDeriv_eq_fderiv hψ]
  exact hc.fderiv_apply ℝ (1, 0)


theorem integral_timeDeriv_eq_zero {ψ : ℝ × E → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (x : E) :
    (∫ s : ℝ, timeDeriv ψ (s, x)) = 0 := by
  have hs : ContDiff ℝ 1 (fun s : ℝ => ψ (s, x)) :=
    (hψ.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
  have hcs : HasCompactSupport (fun s : ℝ => ψ (s, x)) :=
    hc.comp_isClosedEmbedding ⟨isEmbedding_prodMkLeft x, by
      have hr : Set.range (fun s : ℝ => (s, x)) = Set.univ ×ˢ ({x} : Set E) := by
        ext ⟨s, y⟩
        simp [eq_comm]
      rw [hr]
      exact isClosed_univ.prod isClosed_singleton⟩
  exact integral_eq_zero_of_hasDerivAt_of_integrable
    (fun s => (hs.differentiable one_ne_zero s).hasDerivAt)
    ((hs.continuous_deriv le_rfl).integrable_of_hasCompactSupport hcs.deriv)
    (hs.continuous.integrable_of_hasCompactSupport hcs)

end Parking.Generic.TimeTest
