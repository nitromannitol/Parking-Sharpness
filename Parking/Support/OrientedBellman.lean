import Parking.Support.OrientedTerminal

/-!
# Finite-horizon oriented stopping and backward induction

Backward induction computes the stopping value for a time-dependent terminal
reward. The optimal decision depends only on the oriented position and time.
-/

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- The backward value of an oriented stopping problem with a terminal reward. -/
def orientedBellman : ℕ → (ℕ → Site d → ℝ) → Site d → ℝ
  | 0, F, x => F 0 x
  | n + 1, F, x => max (F 0 x) (orientedOp (orientedBellman n (fun k => F (k + 1))) x)

/-- Conditioning a positive stopping time on the first direction shifts its
    terminal reward and initial position by one step. -/
theorem orientedTerminalValue_consNat (hd : 1 ≤ d) {n : ℕ}
    {σ : (ℕ → Fin d × Bool) → ℕ} (hσ : IsStoppingTimeLE (n + 1) σ)
    (hpos : ∀ p, 1 ≤ σ p) (F : ℕ → Site d → ℝ) (x : Site d) :
    orientedTerminalValue F x σ =
      ∫ u : Fin d × Bool, orientedTerminalValue (fun k => F (k + 1)) (x - unit u.1)
        (fun r => σ (consNat u r) - 1) ∂(stepLaw d) := by
  have := stepLaw_isProbability hd
  have hi := integrable_orientedTerminalReward hd hσ F x
  unfold orientedTerminalValue at hi ⊢
  rw [show walkLaw d = Measure.infinitePi fun _ : ℕ => stepLaw d from rfl,
    integral_infinitePi_nat_head_tail (stepLaw d) _ (by
      rwa [show (Measure.infinitePi fun _ : ℕ => stepLaw d) = walkLaw d from rfl])]
  congr 1
  funext u
  apply integral_congr_ae
  filter_upwards with r
  have htime : σ (consNat u r) - 1 + 1 = σ (consNat u r) := by
    have := hpos (consNat u r)
    omega
  rw [htime, ← htime, orientedPath_tail]
  rfl

/-- Every bounded oriented rule has expected reward at most the backward value. -/
theorem orientedTerminalValue_le_orientedBellman (hd : 1 ≤ d) :
    ∀ n (F : ℕ → Site d → ℝ) x σ, IsStoppingTimeLE n σ →
      orientedTerminalValue F x σ ≤ orientedBellman n F x := by
  have := stepLaw_isProbability hd
  have : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  intro n
  induction n with
  | zero =>
    intro F x σ hσ
    have h0 : ∀ p, σ p = 0 := fun p => Nat.le_zero.mp (hσ.1 p)
    simp [orientedTerminalValue, orientedBellman, h0, orientedPath]
  | succ n ih =>
    intro F x σ hσ
    by_cases hex : ∃ p, σ p = 0
    · obtain ⟨p₀, hp₀⟩ := hex
      have h0 : ∀ p, σ p = 0 := by
        intro q
        have hpq : ∀ j, j < σ p₀ → p₀ j = q j := by
          intro j hj
          rw [hp₀] at hj
          omega
        rw [hσ.2 p₀ q hpq, hp₀]
      simp only [orientedBellman]
      have heq : orientedTerminalValue F x σ = F 0 x := by
        simp [orientedTerminalValue, h0, orientedPath]
      rw [heq]
      exact le_max_left _ _
    · have hpos : ∀ p, 1 ≤ σ p := fun p => Nat.one_le_iff_ne_zero.mpr (by
        intro h; exact hex ⟨p, h⟩)
      rw [orientedTerminalValue_consNat hd hσ hpos]
      have hfin : ∀ f : Fin d × Bool → ℝ, Integrable f (stepLaw d) := fun f =>
        integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
      have hmono : (∫ u : Fin d × Bool,
          orientedTerminalValue (fun k => F (k + 1)) (x - unit u.1)
            (fun r => σ (consNat u r) - 1) ∂(stepLaw d)) ≤
          ∫ u : Fin d × Bool, orientedBellman n (fun k => F (k + 1))
            (x - unit u.1) ∂(stepLaw d) :=
        integral_mono (hfin _) (hfin _) (fun u =>
          ih _ _ _ (isStoppingTimeLE_shift hσ u))
      rw [integral_stepLaw_oriented hd] at hmono
      exact hmono.trans (le_max_right _ _)

/-- A backward-induction stopping rule using the current oriented position. -/
def orientedOptimalRule : (n : ℕ) → (ℕ → Site d → ℝ) → Site d →
    (ℕ → Fin d × Bool) → ℕ
  | 0, _, _, _ => 0
  | n + 1, F, x, p =>
    if F 0 x ≥ orientedOp (orientedBellman n (fun k => F (k + 1))) x then 0
    else orientedOptimalRule n (fun k => F (k + 1)) (x - unit (p 0).1) (tailNat p) + 1

/-- The backward rule is bounded and only reads the coordinate choices before
    it stops. -/
theorem orientedOptimalRule_bounded_and_congr :
    ∀ n (F : ℕ → Site d → ℝ) x,
      (∀ p, orientedOptimalRule n F x p ≤ n) ∧
      (∀ p q, (∀ j < orientedOptimalRule n F x p, (p j).1 = (q j).1) →
        orientedOptimalRule n F x q = orientedOptimalRule n F x p) := by
  intro n
  induction n with
  | zero => simp [orientedOptimalRule]
  | succ n ih =>
    intro F x
    by_cases h : F 0 x ≥ orientedOp (orientedBellman n (fun k => F (k + 1))) x
    · simp [orientedOptimalRule, h]
    · constructor
      · intro p
        have hb := (ih (fun k => F (k + 1)) (x - unit (p 0).1)).1 (tailNat p)
        simp only [orientedOptimalRule, ite_eq_right h]
        omega
      · intro p q hpq
        simp only [orientedOptimalRule, ite_eq_right h] at hpq ⊢
        have h0 : (p 0).1 = (q 0).1 := hpq 0 (by omega)
        rw [← h0]
        congr 1
        apply (ih (fun k => F (k + 1)) (x - unit (p 0).1)).2
        intro j hj
        exact hpq (j + 1) (by omega)

/-- The backward-induction rule is an admissible stopping time. -/
theorem isStoppingTimeLE_orientedOptimalRule (n : ℕ) (F : ℕ → Site d → ℝ) (x : Site d) :
    IsStoppingTimeLE n (orientedOptimalRule n F x) := by
  refine ⟨(orientedOptimalRule_bounded_and_congr n F x).1, ?_⟩
  intro p q hpq
  exact (orientedOptimalRule_bounded_and_congr n F x).2 p q (fun j hj =>
    congrArg Prod.fst (hpq j hj))

/-- The backward-induction rule attains the backward value. -/
theorem orientedTerminalValue_orientedOptimalRule (hd : 1 ≤ d) :
    ∀ n (F : ℕ → Site d → ℝ) x,
      orientedTerminalValue F x (orientedOptimalRule n F x) = orientedBellman n F x := by
  have := stepLaw_isProbability hd
  have : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  intro n
  induction n with
  | zero =>
    intro F x
    simp [orientedTerminalValue, orientedOptimalRule, orientedBellman, orientedPath]
  | succ n ih =>
    intro F x
    by_cases h : F 0 x ≥ orientedOp (orientedBellman n (fun k => F (k + 1))) x
    · have hzero : orientedOptimalRule (n + 1) F x = fun _ => 0 := by
        funext p
        simp [orientedOptimalRule, h]
      rw [hzero]
      simp [orientedTerminalValue, orientedBellman, orientedPath, max_eq_left h]
    · have hpos : ∀ p, 1 ≤ orientedOptimalRule (n + 1) F x p := by
        intro p
        simp only [orientedOptimalRule, ite_eq_right h]
        omega
      rw [orientedTerminalValue_consNat hd (isStoppingTimeLE_orientedOptimalRule _ _ _) hpos]
      have hinner : ∀ u : Fin d × Bool,
          orientedTerminalValue (fun k => F (k + 1)) (x - unit u.1)
            (fun r => orientedOptimalRule (n + 1) F x (consNat u r) - 1) =
          orientedBellman n (fun k => F (k + 1)) (x - unit u.1) := by
        intro u
        have heq : (fun r => orientedOptimalRule (n + 1) F x (consNat u r) - 1) =
            orientedOptimalRule n (fun k => F (k + 1)) (x - unit u.1) := by
          funext r
          simp [orientedOptimalRule, h]
          rfl
        rw [heq, ih]
      simp only [hinner]
      rw [integral_stepLaw_oriented hd]
      simp only [orientedBellman, max_eq_right (le_of_not_ge h)]

/-- The oriented stopping value equals its backward-induction value. -/
theorem orientedStoppingSup_eq_orientedBellman (hd : 1 ≤ d)
    (n : ℕ) (F : ℕ → Site d → ℝ) (x : Site d) :
    orientedStoppingSup d F n x = orientedBellman n F x := by
  have hb : BddAbove (orientedTerminalValues d F n x) := by
    refine ⟨orientedBellman n F x, ?_⟩
    rintro a ⟨σ, hσ, rfl⟩
    exact orientedTerminalValue_le_orientedBellman hd n F x σ hσ
  apply le_antisymm
  · apply csSup_le (orientedTerminalValues_nonempty d F n x)
    rintro a ⟨σ, hσ, rfl⟩
    exact orientedTerminalValue_le_orientedBellman hd n F x σ hσ
  · rw [← orientedTerminalValue_orientedOptimalRule hd n F x]
    exact le_csSup hb ⟨orientedOptimalRule n F x, isStoppingTimeLE_orientedOptimalRule n F x, rfl⟩

end Parking
