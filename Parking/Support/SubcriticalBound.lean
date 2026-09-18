/-
The first two assertions of `thm:subcritical` (`parking.tex:2419-2432`).

`a > 0` is the continuity of the drift on `[0, λ₁]` together with its positivity
at `0` (`Support/TiltContinuity.lean`), and `eq:range-upper` is the bound of
`Support/SubcriticalGraftStep3.lean` carried to the conditional survival
probability by `Support/SubcriticalConditional.lean`: the bound is uniform in the
prescribed particles at the origin, and the prescription a realization carries
there is independent of everything else.
-/
import Parking.Support.SubcriticalConditional

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- **`a > 0`.** -/
theorem subcritical_a_pos {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) {θ : ℝ}
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν < 0) {lam₁ : ℝ} (hlam₁ : 0 < lam₁) (hlam₁θ : lam₁ < θ)
    (hnonpos : ∀ s ∈ Set.Icc (0 : ℝ) lam₁,
      Integrable (fun k : ℤ => (k : ℝ)) (tiltLaw ν s) ∧
      ∫ k, (k : ℝ) ∂(tiltLaw ν s) ≤ 0) :
    0 < (1 / 3) * ∫ s in (0 : ℝ)..lam₁, drift ν s := by
  have hpos := intervalIntegral_drift_pos hexp hint hmean hlam₁ hlam₁θ
    (fun s hs => by
      have := (hnonpos s hs).2
      unfold drift
      linarith)
  linarith

/-- **`eq:range-upper`**: the conditional survival probability of the first
particle at the origin. -/
theorem survivalGivenWalk_le (hd : 1 ≤ d) {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) {θ : ℝ}
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * k)) ν)
    {lam₁ : ℝ} (hlam₁ : 0 < lam₁) (hlam₁θ : lam₁ < θ)
    (hnonpos : ∀ s ∈ Set.Icc (0 : ℝ) lam₁,
      Integrable (fun k : ℤ => (k : ℝ)) (tiltLaw ν s) ∧
      ∫ k, (k : ℝ) ∂(tiltLaw ν s) ≤ 0)
    (k : ℕ) (hk : 1 ≤ k) (hνk : ν {(k : ℤ)} ≠ 0) (t : ℕ) (w : ℕ → Fin d × Bool) :
    survivalGivenWalk d ν k t w
      ≤ Real.exp ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, ∫ j, |(j : ℝ)| ∂(tiltLaw ν s))
        * Real.exp (lam₁ * ((k : ℝ) - 1) / 3
          - ((1 / 3) * ∫ s in (0 : ℝ)..lam₁, drift ν s)
            * (rangeCard (0 : Site d) w t : ℝ)) := by
  refine survivalGivenWalk_le_of_graft hd w k hνk t ?_
  intro r ω₁ hP hcount
  have hc : 0 ≤ ω₁.1 (0 : Site d) := by
    rw [hcount]
    have : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    omega
  have hbound := integral_graftSurvivalObs_le_exp hd hint hexp hlam₁ hlam₁θ hnonpos w hP hc t
  have hcast : ((ω₁.1 (0 : Site d)).toNat : ℝ) = (k : ℝ) - 1 := by
    rw [hcount]
    have h1 : ((k : ℤ) - 1).toNat = k - 1 := by omega
    rw [h1]
    have h2 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      have : (1 : ℕ) ≤ k := hk
      push_cast [Nat.cast_sub this]
      ring
    exact h2
  rwa [hcast] at hbound

end Parking

end
