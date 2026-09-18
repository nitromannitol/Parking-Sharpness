/-
The terminal-reward form of the oriented stopping problem.

`Parking.orientedStopValue_eq_potential` turns the ADDITIVE reward
`∑_{j<σ} η(X_j)` into the terminal reward `-Φ_{n-σ}(X_σ)`, where
`Φ_m(x) = ∑_{ℓ<m}(P⃗^ℓ η)(x)` is `Parking.orientedPotential`.  The objects below
are the terminal-reward problem itself: the expected terminal reward of one
bounded stopping rule, the set of those values, and their supremum.  With them
the oriented form of `eq:stopping` reads

    u⃗_n(x) = Φ_n(x) + sup_{σ ≤ n} E_x[ -Φ_{n-σ}(X_σ) ],

which is the discrete mirror, term by term, of
`U(T) = Z_T(0,0) + sup_{τ ≤ T} E_0[-Z_T(τ, B_τ)]` at `parking.tex:3186-3190`.

The first argument of the reward is the ELAPSED time `σ`, so that a reward
written with the remaining time carries it as `n - σ`; that is how the
rescaled reward of the scaling limit is read.
-/
import Parking.Support.OrientedStopOptional

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- `E_x F(σ, X_σ)`, the expected terminal reward of the oriented stopping rule
`σ`.  The first argument of `F` is the elapsed time. -/
def orientedTerminalValue (F : ℕ → Site d → ℝ) (x : Site d)
    (σ : (ℕ → Fin d × Bool) → ℕ) : ℝ :=
  ∫ p, F (σ p) (orientedPath x p (σ p)) ∂(walkLaw d)

/-- The set of expected terminal rewards of the oriented stopping rules bounded
by `n`. -/
def orientedTerminalValues (d : ℕ) (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d) : Set ℝ :=
  {a | ∃ σ, IsStoppingTimeLE n σ ∧ a = orientedTerminalValue F x σ}

/-- `sup_{σ ≤ n} E_x F(σ, X_σ)`, the value of the oriented stopping problem with
terminal reward `F`. -/
def orientedStoppingSup (d : ℕ) (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d) : ℝ :=
  sSup (orientedTerminalValues d F n x)

/-- The rule that stops at once is admissible, so the set of terminal values is
never empty and the supremum is not the junk value of `sSup ∅`. -/
theorem orientedTerminalValues_nonempty (d : ℕ) (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d) :
    (orientedTerminalValues d F n x).Nonempty :=
  ⟨orientedTerminalValue F x (fun _ => 0),
    ⟨fun _ => 0, ⟨fun _ => Nat.zero_le _, fun _ _ _ => rfl⟩, rfl⟩⟩

/-- A bound on the reward bounds the value, so the supremum is not the junk
value of an unbounded `sSup` either.  A rule whose reward fails to be integrable
contributes the value zero, which the bound `0 ≤ M` covers. -/
theorem orientedStoppingSup_le (hd : 1 ≤ d) (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ (k : ℕ) (y : Site d), F k y ≤ M) :
    orientedStoppingSup d F n x ≤ M := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  refine Real.sSup_le (fun a ha => ?_) hM
  obtain ⟨σ, hσ, rfl⟩ := ha
  by_cases hint : Integrable (fun p => F (σ p) (orientedPath x p (σ p))) (walkLaw d)
  · have hmono : (∫ p, F (σ p) (orientedPath x p (σ p)) ∂(walkLaw d))
        ≤ ∫ _p : ℕ → Fin d × Bool, M ∂(walkLaw d) :=
      integral_mono hint (integrable_const M) (fun p => hbound _ _)
    simpa [orientedTerminalValue] using hmono
  · rw [orientedTerminalValue, integral_undef hint]
    exact hM

/-- **The Dynkin rewriting, rule by rule.**  The expected terminal reward at
`-Φ` of a bounded stopping rule is its additive value less the potential at the
start. -/
theorem orientedTerminalValue_potential (hd : 1 ≤ d) (η : Site d → ℝ) {n : ℕ}
    {σ : (ℕ → Fin d × Bool) → ℕ} (hσ : IsStoppingTimeLE n σ) (x : Site d) :
    orientedTerminalValue (fun k y => -orientedPotential η (n - k) y) x σ
      = orientedStopValue η x σ - orientedPotential η n x := by
  have hpt : ∀ p : ℕ → Fin d × Bool,
      (fun k y => -orientedPotential η (n - k) y) (σ p) (orientedPath x p (σ p))
        = -orientedStopTerminal η n x σ p := fun p => rfl
  unfold orientedTerminalValue
  simp only [hpt]
  rw [MeasureTheory.integral_neg, orientedStopValue_eq_potential hd η n x σ hσ]
  ring

/-- The terminal-reward problem at `-Φ` has the same least upper bound as the
additive problem, translated by the potential at the start. -/
theorem isLUB_orientedTerminalValues (hd : 1 ≤ d) (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    IsLUB (orientedTerminalValues d (fun k y => -orientedPotential η (n - k) y) n x)
      (uOriented η n x - orientedPotential η n x) := by
  constructor
  · rintro a ⟨σ, hσ, rfl⟩
    rw [orientedTerminalValue_potential hd η hσ]
    have h := orientedStopValue_le hd η n x σ hσ
    linarith
  · intro b hb
    obtain ⟨σ, hσ, hval⟩ := uOriented_mem_orientedStopValues hd η n x
    refine hb ⟨σ, hσ, ?_⟩
    rw [orientedTerminalValue_potential hd η hσ, ← hval]

theorem orientedStoppingSup_potential (hd : 1 ≤ d) (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    orientedStoppingSup d (fun k y => -orientedPotential η (n - k) y) n x
      = uOriented η n x - orientedPotential η n x :=
  (isLUB_orientedTerminalValues hd η n x).csSup_eq (orientedTerminalValues_nonempty d _ n x)

/-- **The Dynkin rewriting of `eq:stopping` for the oriented walk.**  The
oriented odometer is the potential at the start plus the value of the
terminal-reward problem with reward `-Φ` at the time to go:

    `u⃗_n(x) = Φ_n(x) + sup_{σ ≤ n} E_x[-Φ_{n-σ}(X_σ)]`,

the discrete mirror, term by term, of
`U(T) = Z_T(0,0) + sup_{τ ≤ T} E_0[-Z_T(τ,B_τ)]` at `parking.tex:3186-3190`. -/
theorem uOriented_eq_potential_add_stoppingSup (hd : 1 ≤ d) (η : Site d → ℝ) (n : ℕ)
    (x : Site d) :
    uOriented η n x = orientedPotential η n x
      + orientedStoppingSup d (fun k y => -orientedPotential η (n - k) y) n x := by
  rw [orientedStoppingSup_potential hd η n x]
  ring

/-- The terminal reward of a bounded stopping rule reads only the directions the
rule may read. -/
theorem orientedTerminalReward_congr {n : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE n σ) (F : ℕ → Site d → ℝ) (x : Site d)
    {p q : ℕ → Fin d × Bool} (h : ∀ i, i < n → p i = q i) :
    F (σ p) (orientedPath x p (σ p)) = F (σ q) (orientedPath x q (σ q)) := by
  have hle : σ p ≤ n := hσ.1 p
  have hsame : σ q = σ p := hσ.2 p q (fun j hj => h j (lt_of_lt_of_le hj hle))
  rw [hsame, orientedPath_congr x (σ p) (fun i hi => h i (lt_of_lt_of_le hi hle))]

/-- **The terminal reward of a bounded rule is always integrable**, whatever the
reward field: it reads finitely many directions.  So the discrete problem, unlike
the continuum one, carries no junk value at all. -/
theorem integrable_orientedTerminalReward (hd : 1 ≤ d) {n : ℕ}
    {σ : (ℕ → Fin d × Bool) → ℕ} (hσ : IsStoppingTimeLE n σ) (F : ℕ → Site d → ℝ)
    (x : Site d) :
    Integrable (fun p => F (σ p) (orientedPath x p (σ p))) (walkLaw d) :=
  integrable_of_finite_dependence hd n _ (fun _ _ h => orientedTerminalReward_congr hσ F x h)

/-- The expected terminal reward is homogeneous in the reward. -/
theorem orientedTerminalValue_const_mul (c : ℝ) (F : ℕ → Site d → ℝ) (x : Site d)
    (σ : (ℕ → Fin d × Bool) → ℕ) :
    orientedTerminalValue (fun k y => c * F k y) x σ
      = c * orientedTerminalValue F x σ := by
  unfold orientedTerminalValue
  exact MeasureTheory.integral_const_mul c _

theorem orientedTerminalValues_const_mul (c : ℝ) (F : ℕ → Site d → ℝ) (n : ℕ) (x : Site d) :
    orientedTerminalValues d (fun k y => c * F k y) n x
      = (fun a => c * a) '' orientedTerminalValues d F n x := by
  ext a
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨orientedTerminalValue F x σ, ⟨σ, hσ, rfl⟩,
      (orientedTerminalValue_const_mul c F x σ).symm⟩
  · rintro ⟨b, ⟨σ, hσ, rfl⟩, rfl⟩
    exact ⟨σ, hσ, (orientedTerminalValue_const_mul c F x σ).symm⟩

end Parking

end
