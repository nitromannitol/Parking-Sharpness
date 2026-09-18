/-
The Paley-Zygmund lower bound of Step 2 of `prop:everyone-settles`
(`parking.tex:1510-1522`).

`thm:master` bounds `E U_n(0)` below by `c (E u_n(0) + log n)` and
`Parking.exists_second_moment` bounds `E U_n(0)^2` above by
`C (E u_n(0) + log n)^2`.  Paley-Zygmund at `θ = 1/2` therefore gives a
probability bounded away from zero, uniformly in `n`, that the odometer at the
origin exceeds a fixed multiple of `E u_n(0) + log n`.
-/
import Parking.Support.SecondMoment
import Parking.Frozen.Master
import LatticeProb.Prob.PaleyZygmund

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Filter

variable {d : ℕ}

theorem exists_odometer_lower_prob (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration)
    (hGreenNorms : Parking.External.GreenNorms)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ c a : ℝ, 0 < c ∧ 0 < a ∧ ∀ n : ℕ, 2 ≤ n →
      a ≤ (law d ν).real
        {ω : Data d | c * (meanu (law d ν) n + Real.log n) < ((U ω n 0 : ℕ) : ℝ)} := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  obtain ⟨θ, hθ, hexpabs⟩ := hν.expMoment
  obtain ⟨c₁, C₁, hc₁, hc₁C₁, hmaster⟩ :=
    Parking.Frozen.master hGrowth hBernstein hConcentration hGreenNorms d hd ν
      inferInstance hν.nonconst hν.mean θ hθ hexpabs
  obtain ⟨C₂, hC₂, hsecond⟩ := exists_second_moment hd hBernstein hConcentration hGrowth
    hGreenNorms ν hν
  refine ⟨min (c₁ / 2) 1, c₁ ^ 2 / (4 * C₂), lt_min (by positivity) one_pos, by positivity,
    fun n hn => ?_⟩
  set m : ℝ := meanu (law d ν) n + Real.log n with hm
  have hm0 : 0 < m := by
    have h1 : (0 : ℝ) ≤ meanu (law d ν) n := integral_nonneg fun ω => uOf_nonneg ω n 0
    have h2 : (0 : ℝ) < Real.log n := log_pos_of_two_le hn
    simp only [hm]; linarith
  set X : Data d → ℝ := fun ω => ((U ω n 0 : ℕ) : ℝ) with hX
  have hXm : Measurable X := (measurable_from_countable' fun k : ℕ => (k : ℝ)).comp
    (measurable_U n 0)
  have hXnn : ∀ ω, 0 ≤ X ω := fun ω => Nat.cast_nonneg _
  have hX2 : Integrable (fun ω => X ω ^ 2) (law d ν) := (hsecond n hn).1
  have hIX : ∫ ω, X ω ∂(law d ν) = meanU (law d ν) n := rfl
  have hPZ := LatticeProb.paley_zygmund (law d ν) hXm hXnn hX2
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 ≤ 1)
  rw [hIX] at hPZ
  have hlow : c₁ * m ≤ meanU (law d ν) n := (hmaster n hn).1
  have hup : ∫ ω, X ω ^ 2 ∂(law d ν) ≤ C₂ * m ^ 2 := (hsecond n hn).2
  set A : Set (Data d) := {ω : Data d | 1/2 * meanU (law d ν) n < X ω} with hA
  have hp0 : (0 : ℝ) ≤ (law d ν).real A := measureReal_nonneg
  have hkey : c₁ ^ 2 / (4 * C₂) ≤ (law d ν).real A := by
    norm_num at hPZ
    have hsq : c₁ ^ 2 * m ^ 2 ≤ meanU (law d ν) n ^ 2 := by
      have hcm : 0 < c₁ * m := mul_pos hc₁ hm0
      nlinarith [hlow, hcm]
    have hQp : (∫ ω, X ω ^ 2 ∂(law d ν)) * (law d ν).real A ≤ C₂ * m ^ 2 * (law d ν).real A :=
      mul_le_mul_of_nonneg_right hup hp0
    have h4 : c₁ ^ 2 * m ^ 2 / 4 ≤ C₂ * m ^ 2 * (law d ν).real A := by linarith
    have hm2 : (0:ℝ) < m ^ 2 := by positivity
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * C₂)]
    nlinarith [h4, hm2]
  refine le_trans hkey ?_
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  have h1 : 1/2 * meanU (law d ν) n < X ω := hω
  have h2 : min (c₁ / 2) 1 * m ≤ 1/2 * meanU (law d ν) n := by
    have h3 : min (c₁ / 2) 1 ≤ c₁ / 2 := min_le_left _ _
    nlinarith [hm0.le, hlow]
  exact lt_of_le_of_lt h2 h1

end Parking
