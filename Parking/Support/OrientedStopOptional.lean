/-
Optional stopping for the oriented walk: the expected reward of a bounded
stopping rule is the potential at the start minus the expected stopped
potential.

This is the identity that turns the ADDITIVE problem of `eq:stopping`,
`sup_{σ ≤ n} E_x ∑_{j<σ} η(X_j)`, into one with the TERMINAL reward `-Φ`, where
`Φ_m(x) = ∑_{ℓ<m} (P⃗^ℓ η)(x)` is the truncated potential
(`Parking.orientedPotential`):

    E_x ∑_{j<σ} η(X_j) = Φ_n(x) - E_x Φ_{n-σ}(X_σ),

so that `u⃗_n(x) = Φ_n(x) + sup_{σ ≤ n} E_x[-Φ_{n-σ}(X_σ)]`, which is the
discrete counterpart, term by term, of
`U(T) = Z_T(0,0) + sup_{τ ≤ T} E_0[-Z_T(τ, B_τ)]` at `parking.tex:3186-3190`.
The proof is the same head-tail induction as `Parking.orientedStopValue_consNat`,
with `Parking.orientedPotential_succ`, `Φ_{m+1}(x) = η(x) + (P⃗Φ_m)(x)`, in place
of the odometer recursion.
-/
import Parking.Support.OrientedStoppingValue

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- The stopped potential, the terminal reward of the stopping problem. -/
def orientedStopTerminal (η : Site d → ℝ) (n : ℕ) (x : Site d)
    (σ : (ℕ → Fin d × Bool) → ℕ) (p : ℕ → Fin d × Bool) : ℝ :=
  orientedPotential η (n - σ p) (orientedPath x p (σ p))

theorem orientedStopTerminal_congr {n : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE n σ) (η : Site d → ℝ) (x : Site d)
    {p q : ℕ → Fin d × Bool} (h : ∀ i, i < n → p i = q i) :
    orientedStopTerminal η n x σ p = orientedStopTerminal η n x σ q := by
  have hle : σ p ≤ n := hσ.1 p
  have hsame : σ q = σ p := hσ.2 p q (fun j hj => h j (lt_of_lt_of_le hj hle))
  unfold orientedStopTerminal
  rw [hsame, orientedPath_congr x (σ p) (fun i hi => h i (lt_of_lt_of_le hi hle))]

theorem integrable_orientedStopTerminal (hd : 1 ≤ d) {n : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE n σ) (η : Site d → ℝ) (x : Site d) :
    Integrable (orientedStopTerminal η n x σ) (walkLaw d) :=
  integrable_of_finite_dependence hd n _
    (fun _ _ h => orientedStopTerminal_congr hσ η x h)

/-- **Optional stopping for the oriented walk.**  The expected reward of a
bounded stopping rule is the potential at the start minus the expected stopped
potential, which is what turns the additive problem into one with the terminal
reward `-Φ`. -/
theorem orientedStopValue_eq_potential (hd : 1 ≤ d) (η : Site d → ℝ) :
    ∀ (n : ℕ) (x : Site d) (σ : (ℕ → Fin d × Bool) → ℕ), IsStoppingTimeLE n σ →
      orientedStopValue η x σ
        = orientedPotential η n x - ∫ p, orientedStopTerminal η n x σ p ∂(walkLaw d) := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  intro n
  induction n with
  | zero =>
      intro x σ hσ
      have h0 : ∀ p, σ p = 0 := fun p => Nat.le_zero.mp (hσ.1 p)
      rw [orientedStopValue_of_zero h0, orientedPotential_zero]
      have hz : ∀ p : ℕ → Fin d × Bool, orientedStopTerminal η 0 x σ p = 0 := by
        intro p
        unfold orientedStopTerminal
        rw [h0 p]
        exact orientedPotential_zero η _
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
            orientedStopTerminal η (n + 1) x σ p = orientedPotential η (n + 1) x := by
          intro p
          unfold orientedStopTerminal
          rw [h0 p]
          rfl
        rw [orientedStopValue_of_zero h0]
        simp [hz]
      · rw [not_exists] at hex
        have hpos : ∀ p, 1 ≤ σ p := fun p => Nat.one_le_iff_ne_zero.mpr (hex p)
        have hcons : ∀ (u : Fin d × Bool) (r : ℕ → Fin d × Bool),
            orientedStopTerminal η (n + 1) x σ (consNat u r)
              = orientedStopTerminal η n (x - unit u.1) (fun r' => σ (consNat u r') - 1) r := by
          intro u r
          have h1 : n + 1 - σ (consNat u r) = n - (σ (consNat u r) - 1) := by
            have := hpos (consNat u r)
            omega
          have h2 : orientedPath x (consNat u r) (σ (consNat u r))
              = orientedPath (x - unit u.1) r (σ (consNat u r) - 1) := by
            have hm : σ (consNat u r) = (σ (consNat u r) - 1) + 1 := by
              have := hpos (consNat u r)
              omega
            rw [hm, orientedPath_tail]
            rfl
          unfold orientedStopTerminal
          rw [h1, h2]
        have hsplit : (∫ p, orientedStopTerminal η (n + 1) x σ p ∂(walkLaw d))
            = ∫ u : Fin d × Bool, (∫ r, orientedStopTerminal η n (x - unit u.1)
                (fun r' => σ (consNat u r') - 1) r ∂(walkLaw d)) ∂(stepLaw d) := by
          rw [show walkLaw d = Measure.infinitePi fun _ : ℕ => stepLaw d from rfl,
            integral_infinitePi_nat_head_tail (stepLaw d)
              (orientedStopTerminal η (n + 1) x σ)
              (integrable_orientedStopTerminal hd hσ η x)]
          exact integral_congr_ae (Filter.Eventually.of_forall (fun u => by
            simp only [hcons u]))
        rw [orientedStopValue_consNat hd hσ hpos, hsplit]
        have hih : ∀ u : Fin d × Bool,
            orientedStopValue η (x - unit u.1) (fun r => σ (consNat u r) - 1)
              = orientedPotential η n (x - unit u.1)
                - ∫ r, orientedStopTerminal η n (x - unit u.1)
                    (fun r' => σ (consNat u r') - 1) r ∂(walkLaw d) :=
          fun u => ih (x - unit u.1) _ (isStoppingTimeLE_shift hσ u)
        simp only [hih]
        rw [integral_sub (hfin _) (hfin _), integral_stepLaw_oriented hd _ x,
          orientedPotential_succ]
        ring

end Parking

end
