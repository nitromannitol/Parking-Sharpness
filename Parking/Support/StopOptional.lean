/-
Optional stopping for the simple random walk: the expected reward of a
bounded stopping rule is the linear potential at the start minus the
expected stopped potential.

This is the identity that turns the ADDITIVE problem of `eq:stopping`,
`sup_{σ ≤ n} E_x ∑_{j<σ} η(X_j)`, into one with the TERMINAL reward `-V`,
where `V` is `Parking.linPotential`:

    E_x ∑_{j<σ} η(X_j) = V_n(x) - E_x V_{n-σ}(X_σ),

so that `u_n(x) = V_n(x) + sup_{σ ≤ n} E_x[-V_{n-σ}(X_σ)]`, BP's Lemma 2.5
(page 16) for the simple random walk. Transposed from
`Parking/Support/OrientedStopOptional.lean`, with `walkOp`/`walkPath`/
`linPotential` in place of `orientedOp`/`orientedPath`/`orientedPotential`.
-/
import Parking.Support.StoppingValue
import Parking.Support.LinPotential

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- The stopped potential, the terminal reward of the stopping problem. -/
def stopTerminal (η : Site d → ℝ) (n : ℕ) (x : Site d)
    (σ : (ℕ → Fin d × Bool) → ℕ) (p : ℕ → Fin d × Bool) : ℝ :=
  linPotential η (n - σ p) (walkPath x p (σ p))

theorem stopTerminal_congr {n : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE n σ) (η : Site d → ℝ) (x : Site d)
    {p q : ℕ → Fin d × Bool} (h : ∀ i, i < n → p i = q i) :
    stopTerminal η n x σ p = stopTerminal η n x σ q := by
  have hle : σ p ≤ n := hσ.1 p
  have hsame : σ q = σ p := hσ.2 p q (fun j hj => h j (lt_of_lt_of_le hj hle))
  unfold stopTerminal
  rw [hsame, walkPath_congr x (fun i hi => h i (lt_of_lt_of_le hi hle))]

theorem integrable_stopTerminal (hd : 1 ≤ d) {n : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE n σ) (η : Site d → ℝ) (x : Site d) :
    Integrable (stopTerminal η n x σ) (walkLaw d) :=
  integrable_of_finite_dependence hd n _ (fun _ _ h => stopTerminal_congr hσ η x h)

/-- **Optional stopping for the simple random walk.**  The expected reward of a
bounded stopping rule is the linear potential at the start minus the expected
stopped potential, BP's Lemma 2.5 for the additive form. -/
theorem stopValue_eq_potential (hd : 1 ≤ d) (η : Site d → ℝ) :
    ∀ (n : ℕ) (x : Site d) (σ : (ℕ → Fin d × Bool) → ℕ), IsStoppingTimeLE n σ →
      stopValue η x σ
        = linPotential η n x - ∫ p, stopTerminal η n x σ p ∂(walkLaw d) := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  intro n
  induction n with
  | zero =>
      intro x σ hσ
      have h0 : ∀ p, σ p = 0 := fun p => Nat.le_zero.mp (hσ.1 p)
      rw [stopValue_of_zero h0, linPotential_zero]
      have hz : ∀ p : ℕ → Fin d × Bool, stopTerminal η 0 x σ p = 0 := by
        intro p
        unfold stopTerminal
        rw [h0 p, Nat.zero_sub, linPotential_zero]
      simp [hz]
  | succ n ih =>
      intro x σ hσ
      have hfin : ∀ f : Fin d × Bool → ℝ, Integrable f (stepLaw d) := fun f =>
        integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
      by_cases hex : ∃ p₀, σ p₀ = 0
      · obtain ⟨p₀, hp₀⟩ := hex
        have h0 : ∀ p, σ p = 0 := by
          intro q
          have hj : ∀ j, j < σ p₀ → p₀ j = q j := by
            intro j hj
            rw [hp₀] at hj
            exact absurd hj (Nat.not_lt_zero j)
          rw [hσ.2 p₀ q hj, hp₀]
        have hz : ∀ p : ℕ → Fin d × Bool,
            stopTerminal η (n + 1) x σ p = linPotential η (n + 1) x := by
          intro p
          unfold stopTerminal
          rw [h0 p]
          rfl
        rw [stopValue_of_zero h0]
        simp [hz]
      · rw [not_exists] at hex
        have hpos : ∀ p, 1 ≤ σ p := fun p => Nat.one_le_iff_ne_zero.mpr (hex p)
        have hcons : ∀ (u : Fin d × Bool) (r : ℕ → Fin d × Bool),
            stopTerminal η (n + 1) x σ (consNat u r)
              = stopTerminal η n (x + stepVec u) (fun r' => σ (consNat u r') - 1) r := by
          intro u r
          have h1 : n + 1 - σ (consNat u r) = n - (σ (consNat u r) - 1) := by
            have := hpos (consNat u r)
            omega
          have h2 : walkPath x (consNat u r) (σ (consNat u r))
              = walkPath (x + stepVec u) r (σ (consNat u r) - 1) := by
            have hm : σ (consNat u r) = (σ (consNat u r) - 1) + 1 := by
              have := hpos (consNat u r)
              omega
            rw [hm, walkPath_consNat]
            simp
          unfold stopTerminal
          rw [h1, h2]
        have hsplit : (∫ p, stopTerminal η (n + 1) x σ p ∂(walkLaw d))
            = ∫ u : Fin d × Bool, (∫ r, stopTerminal η n (x + stepVec u)
                (fun r' => σ (consNat u r') - 1) r ∂(walkLaw d)) ∂(stepLaw d) := by
          rw [show walkLaw d = Measure.infinitePi fun _ : ℕ => stepLaw d from rfl,
            integral_infinitePi_nat_head_tail (stepLaw d)
              (stopTerminal η (n + 1) x σ)
              (integrable_stopTerminal hd hσ η x)]
          exact integral_congr_ae (Filter.Eventually.of_forall (fun u => by
            simp only [hcons u]))
        rw [stopValue_consNat hd hσ hpos, hsplit]
        have hih : ∀ u : Fin d × Bool,
            stopValue η (x + stepVec u) (fun r => σ (consNat u r) - 1)
              = linPotential η n (x + stepVec u)
                - ∫ r, stopTerminal η n (x + stepVec u)
                    (fun r' => σ (consNat u r') - 1) r ∂(walkLaw d) :=
          fun u => ih (x + stepVec u) _ (isStoppingTimeLE_shift' hσ u)
        simp only [hih]
        rw [integral_sub (hfin _) (hfin _), integral_stepLaw_walk hd _ x,
          linPotential_succ]
        ring

end Parking

end
