/-
The terminal-reward form of the stopping problem for the simple random walk.

`Parking.stopValue_eq_potential` turns the ADDITIVE reward `∑_{j<σ} η(X_j)`
into the terminal reward `-V_{n-σ}(X_σ)`, where `V = Parking.linPotential`.
The objects below are the terminal-reward problem itself: the expected
terminal reward of one bounded stopping rule, the set of those values, and
their supremum.  With them BP's Lemma 2.5 (page 16) reads

    u_n(x) = V_n(x) + sup_{σ ≤ n} E_x[ -V_{n-σ}(X_σ) ],

the discrete analogue of `𝒰(T,x) = Z(T,x) + sup_{τ≤T} E_x^BM[-Z(T-τ,B_τ)]`
(BouRabeePanagiotis2026, Section 2.1, eq. (21)).  The development parallels
`Parking/Support/OrientedTerminal.lean`.
-/
import Parking.Support.StopOptional

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- `E_x F(σ, X_σ)`, the expected terminal reward of the stopping rule `σ`.
The first argument of `F` is the elapsed time. -/
def terminalValue (F : ℕ → Site d → ℝ) (x : Site d)
    (σ : (ℕ → Fin d × Bool) → ℕ) : ℝ :=
  ∫ p, F (σ p) (walkPath x p (σ p)) ∂(walkLaw d)

/-- The set of expected terminal rewards of the stopping rules bounded by
`n`. -/
def terminalValues (d : ℕ) (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d) : Set ℝ :=
  {a | ∃ σ, IsStoppingTimeLE n σ ∧ a = terminalValue F x σ}

/-- `sup_{σ ≤ n} E_x F(σ, X_σ)`, the value of the stopping problem with
terminal reward `F`. -/
def stoppingSup (d : ℕ) (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d) : ℝ :=
  sSup (terminalValues d F n x)

/-- The rule that stops at once is admissible, so the set of terminal values is
never empty and the supremum is not the junk value of `sSup ∅`. -/
theorem terminalValues_nonempty (d : ℕ) (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d) :
    (terminalValues d F n x).Nonempty :=
  ⟨terminalValue F x (fun _ => 0),
    ⟨fun _ => 0, ⟨fun _ => Nat.zero_le _, fun _ _ _ => rfl⟩, rfl⟩⟩

/-- A bound on the reward bounds the value, so the supremum is not the junk
value of an unbounded `sSup` either. -/
theorem stoppingSup_le (hd : 1 ≤ d) (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ (k : ℕ) (y : Site d), F k y ≤ M) :
    stoppingSup d F n x ≤ M := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  refine Real.sSup_le (fun a ha => ?_) hM
  obtain ⟨σ, hσ, rfl⟩ := ha
  by_cases hint : Integrable (fun p => F (σ p) (walkPath x p (σ p))) (walkLaw d)
  · have hmono : (∫ p, F (σ p) (walkPath x p (σ p)) ∂(walkLaw d))
        ≤ ∫ _p : ℕ → Fin d × Bool, M ∂(walkLaw d) :=
      integral_mono hint (integrable_const M) (fun p => hbound _ _)
    simpa [terminalValue] using hmono
  · rw [terminalValue, integral_undef hint]
    exact hM

/-- **The Dynkin rewriting, rule by rule.**  The expected terminal reward at
`-V` of a bounded stopping rule is its additive value less the potential at
the start. -/
theorem terminalValue_potential (hd : 1 ≤ d) (η : Site d → ℝ) {n : ℕ}
    {σ : (ℕ → Fin d × Bool) → ℕ} (hσ : IsStoppingTimeLE n σ) (x : Site d) :
    terminalValue (fun k y => -linPotential η (n - k) y) x σ
      = stopValue η x σ - linPotential η n x := by
  have hpt : ∀ p : ℕ → Fin d × Bool,
      (fun k y => -linPotential η (n - k) y) (σ p) (walkPath x p (σ p))
        = -stopTerminal η n x σ p := fun p => rfl
  unfold terminalValue
  simp only [hpt]
  rw [MeasureTheory.integral_neg, stopValue_eq_potential hd η n x σ hσ]
  ring

/-- The terminal-reward problem at `-V` has the same least upper bound as the
additive problem, translated by the potential at the start. -/
theorem isLUB_terminalValues (hd : 1 ≤ d) (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    IsLUB (terminalValues d (fun k y => -linPotential η (n - k) y) n x)
      (u η n x - linPotential η n x) := by
  constructor
  · rintro a ⟨σ, hσ, rfl⟩
    rw [terminalValue_potential hd η hσ]
    have h := stopValue_le hd η n x σ hσ
    linarith
  · intro b hb
    obtain ⟨σ, hσ, hval⟩ := u_mem_stopValues hd η n x
    refine hb ⟨σ, hσ, ?_⟩
    rw [terminalValue_potential hd η hσ, ← hval]

theorem stoppingSup_potential (hd : 1 ≤ d) (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    stoppingSup d (fun k y => -linPotential η (n - k) y) n x
      = u η n x - linPotential η n x :=
  (isLUB_terminalValues hd η n x).csSup_eq (terminalValues_nonempty d _ n x)

/-- **BP's Lemma 2.5 for the simple random walk (page 16).**  The divisible
odometer is the linear potential at the start plus the value of the
terminal-reward problem with reward `-V` at the time to go:

    `u_n(x) = V_n(x) + sup_{σ ≤ n} E_x[-V_{n-σ}(X_σ)]`. -/
theorem u_eq_potential_add_stoppingSup (hd : 1 ≤ d) (η : Site d → ℝ) (n : ℕ)
    (x : Site d) :
    u η n x = linPotential η n x
      + stoppingSup d (fun k y => -linPotential η (n - k) y) n x := by
  rw [stoppingSup_potential hd η n x]
  ring

end Parking

end
