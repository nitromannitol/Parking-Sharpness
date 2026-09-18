/-
The tilting interval of `thm:subcritical`, and the bound in the form the tail
theorem consumes (`parking.tex:2303-2320`, `parking.tex:2497-2502`).

`parking.tex:2303-2320` chooses `0 < λ₁ < θ` so small that the tilted law has
nonpositive mean on `[0, λ₁]`, "by continuity"; `Parking.exists_lam1` is that
choice.  What the nonpositive-mean hypothesis of `thm:subcritical` asks for
alongside the inequality is the integrability of the identity against the tilt,
which the exponential moment supplies for every parameter below `θ`.  With both,
the last assertion of `thm:subcritical` reads `S_t ≤ C E₀ e^{-a|R_t|}` with `a`
and `C` produced from the standing hypotheses alone.
-/
import Parking.Support.SubcriticalJointBound
import Parking.Support.TiltInterval

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- **The identity is integrable against the tilt** on `[0, θ)`. -/
theorem integrable_id_tiltLaw {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ : ℝ}
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) {s : ℝ} (hs0 : 0 ≤ s) (hsθ : s < θ) :
    Integrable (fun k : ℤ => (k : ℝ)) (tiltLaw ν s) := by
  have hts : (0 : ℝ) < θ - s := by linarith
  refine integrable_tiltLaw s (fun k : ℤ => (k : ℝ)) (integrable_exp_tilt hexp hs0 hsθ.le) ?_
  have hmeas : Measurable fun k : ℤ => Real.exp (s * k) * (k : ℝ) :=
    (Real.measurable_exp.comp (measurable_const.mul
      (measurable_int_fun (fun k : ℤ => (k : ℝ))))).mul
      (measurable_int_fun (fun k : ℤ => (k : ℝ)))
  refine ((hexp.div_const (θ - s)).add hint).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  have hk := abs_mul_exp_le (lam := s) (s₁ := θ) (x := (k : ℝ)) hs0 hsθ
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos (s * (k : ℝ)))]
  simp only [Pi.add_apply]
  have hc : Real.exp (s * (k : ℝ)) * |(k : ℝ)| = |(k : ℝ)| * Real.exp (s * (k : ℝ)) :=
    mul_comm _ _
  linarith [hk, hc]

/-- **The subcritical bound in the form `thm:subcritical-tail` consumes**: the
tilting interval is chosen inside, so only the standing hypotheses of the
section are needed. -/
theorem exists_subcritical_rangeExp (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (hmean : ∫ k, (k : ℝ) ∂ν < 0)
    {θ : ℝ} (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν) :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ t : ℕ,
      Integrable (fun ω => (LatticeProb.survivorsFrom (toDriver ω) t 0 : ℝ)) (law d ν) ∧
        S (law d ν) t ≤ C * rangeExp d a t := by
  obtain ⟨lam₁, hlam₁, hlam₁θ, hdrift⟩ := exists_lam1 hθ hexp hint hmean
  have hnonpos : ∀ s ∈ Set.Icc (0 : ℝ) lam₁,
      Integrable (fun k : ℤ => (k : ℝ)) (tiltLaw ν s) ∧
      ∫ k, (k : ℝ) ∂(tiltLaw ν s) ≤ 0 := by
    intro s hs
    refine ⟨integrable_id_tiltLaw hexp hint hs.1 (lt_of_le_of_lt hs.2 hlam₁θ), ?_⟩
    have h := hdrift s hs
    unfold drift at h
    linarith
  refine ⟨(1 / 3) * ∫ s in (0 : ℝ)..lam₁, drift ν s, max 1 (subcriticalConst ν lam₁),
    subcritical_a_pos hint hexp hmean hlam₁ hlam₁θ hnonpos,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun t => ?_⟩
  refine ⟨integrable_survivorsFrom_law hd hint t, ?_⟩
  have hI0 : (0 : ℝ) ≤ rangeExp d ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, drift ν s) t := by
    rw [rangeExp]
    exact integral_nonneg fun p => (Real.exp_pos _).le
  exact le_trans (S_le_subcriticalConst hd hint hexp hlam₁ hlam₁θ hnonpos t)
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hI0)

end Parking

end
