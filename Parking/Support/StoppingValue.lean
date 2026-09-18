/-
`eq:stopping` (`parking.tex:866-874`) for the simple random walk: the divisible
odometer `u_n` is the value of the bounded optimal stopping problem with
reward `∑_{j<σ} η(X_j)` along the simple random walk.

This is BP's Theorem 2.2 (`Parking.External.Stopping` records the sentence
that cites it as already known from Bou-Rabee, Peres and Sava-Huss 2026,
Theorem 3.2), proved here directly from the recursion `u_0 = 0`,
`u_{n+1} = (η + Pu_n)^+`, transposing `Parking/Support/OrientedStoppingValue.lean`'s
argument verbatim, coordinate for coordinate, with `walkOp`/`walkPath`/`stepVec`
in place of `orientedOp`/`orientedPath`/`(x ↦ x - unit ·)`: `u_0 = 0` and
`u_{n+1} = (η + Pu_n)^+` is the dynamic programming equation of the problem,
so every bounded stopping rule collects at most `u_n(x)` in expectation, and
the rule that stops at once exactly when the continuation value
`η(x) + (Pu_n)(x)` is not positive, and otherwise takes one step and follows
the attaining rule of the site it reaches, collects exactly that.
-/
import Parking.Support.Pathwise
import Parking.Support.OrientedMaximum

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- **The Markov step for the plain walk**: averaging `f` over one uniform
signed step from `x` is `walkOp f x`. -/
theorem integral_stepLaw_walk (hd : 1 ≤ d) (f : Site d → ℝ) (x : Site d) :
    (∫ b : Fin d × Bool, f (x + stepVec b) ∂(stepLaw d)) = walkOp f x := by
  rw [integral_stepLaw hd, sum_stepVec, walkOp]

theorem stopReward_congr {n : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE n σ) (η : Site d → ℝ) (x : Site d)
    {p q : ℕ → Fin d × Bool} (h : ∀ i, i < n → p i = q i) :
    stopReward η x σ p = stopReward η x σ q := by
  have hle : σ p ≤ n := hσ.1 p
  have hpq : ∀ j, j < σ p → p j = q j := fun j hj => h j (lt_of_lt_of_le hj hle)
  have hsame : σ q = σ p := hσ.2 p q hpq
  unfold stopReward
  rw [hsame]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjlt : j < σ p := Finset.mem_range.mp hj
  rw [walkPath_congr x (fun i hi => hpq i (lt_trans hi hjlt))]

theorem integrable_stopReward (hd : 1 ≤ d) {n : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE n σ) (η : Site d → ℝ) (x : Site d) :
    Integrable (stopReward η x σ) (walkLaw d) :=
  integrable_of_finite_dependence hd n _ (fun _ _ h => stopReward_congr hσ η x h)

theorem zero_mem_stopValues (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    (0 : ℝ) ∈ stopValues d η n x := by
  refine ⟨fun _ => 0, ⟨fun _ => Nat.zero_le _, fun _ _ _ => rfl⟩, ?_⟩
  unfold stopValue stopReward
  simp

theorem isStoppingTimeLE_shift' {n : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE (n + 1) σ) (u : Fin d × Bool) :
    IsStoppingTimeLE n (fun r => σ (consNat u r) - 1) := by
  refine ⟨fun r => ?_, fun r r' hrr => ?_⟩
  · show σ (consNat u r) - 1 ≤ n
    have := hσ.1 (consNat u r)
    omega
  · show σ (consNat u r') - 1 = σ (consNat u r) - 1
    have hrr' : ∀ j, j < σ (consNat u r) - 1 → r j = r' j := hrr
    have hcons : ∀ j, j < σ (consNat u r) → consNat u r j = consNat u r' j := by
      intro j hj
      match j with
      | 0 => rfl
      | k + 1 =>
          have hk : k < σ (consNat u r) - 1 := by omega
          show r k = r' k
          exact hrr' k hk
    rw [hσ.2 (consNat u r) (consNat u r') hcons]

theorem stopReward_consNat {σ : (ℕ → Fin d × Bool) → ℕ}
    (hpos : ∀ p, 1 ≤ σ p) (η : Site d → ℝ) (x : Site d)
    (u : Fin d × Bool) (r : ℕ → Fin d × Bool) :
    stopReward η x σ (consNat u r)
      = η x + stopReward η (x + stepVec u) (fun r' => σ (consNat u r') - 1) r := by
  have hm : σ (consNat u r) = (σ (consNat u r) - 1) + 1 := by
    have := hpos (consNat u r)
    omega
  unfold stopReward
  rw [hm, Finset.sum_range_succ']
  have hstep : ∀ j : ℕ, walkPath x (consNat u r) (j + 1)
      = walkPath (x + stepVec u) r j := fun j => walkPath_consNat x u r j
  simp only [hstep]
  show _ = η x + _
  rw [add_comm]
  rfl

theorem stopValue_consNat (hd : 1 ≤ d) {n : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE (n + 1) σ) (hpos : ∀ p, 1 ≤ σ p) (η : Site d → ℝ) (x : Site d) :
    stopValue η x σ
      = η x + ∫ u : Fin d × Bool, stopValue η (x + stepVec u)
          (fun r => σ (consNat u r) - 1) ∂(stepLaw d) := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have hi : Integrable (stopReward η x σ) (walkLaw d) :=
    integrable_stopReward hd hσ η x
  have hfin : ∀ f : Fin d × Bool → ℝ, Integrable f (stepLaw d) := fun f =>
    integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
  rw [stopValue, show walkLaw d = Measure.infinitePi fun _ : ℕ => stepLaw d from rfl,
    integral_infinitePi_nat_head_tail (stepLaw d) (stopReward η x σ)
      (by rwa [show (Measure.infinitePi fun _ : ℕ => stepLaw d) = walkLaw d from rfl])]
  have hinner : ∀ u : Fin d × Bool,
      (∫ r, stopReward η x σ (consNat u r)
          ∂(Measure.infinitePi fun _ : ℕ => stepLaw d))
        = η x + stopValue η (x + stepVec u) (fun r' => σ (consNat u r') - 1) := by
    intro u
    have hcongr : ∀ r, stopReward η x σ (consNat u r)
        = η x + stopReward η (x + stepVec u) (fun r' => σ (consNat u r') - 1) r :=
      fun r => stopReward_consNat hpos η x u r
    simp only [hcongr]
    rw [show (Measure.infinitePi fun _ : ℕ => stepLaw d) = walkLaw d from rfl,
      integral_add (integrable_const _)
        (integrable_stopReward hd (isStoppingTimeLE_shift' hσ u) η _),
      integral_const]
    simp [stopValue]
  simp only [hinner]
  rw [integral_add (hfin _) (hfin _), integral_const]
  simp

theorem stopValue_of_zero {σ : (ℕ → Fin d × Bool) → ℕ}
    (h0 : ∀ p, σ p = 0) (η : Site d → ℝ) (x : Site d) :
    stopValue η x σ = 0 := by
  unfold stopValue stopReward
  simp [h0]

/-- **The odometer bounds every bounded stopping rule.** -/
theorem stopValue_le (hd : 1 ≤ d) (η : Site d → ℝ) :
    ∀ (n : ℕ) (x : Site d) (σ : (ℕ → Fin d × Bool) → ℕ), IsStoppingTimeLE n σ →
      stopValue η x σ ≤ u η n x := by
  haveI := stepLaw_isProbability hd
  intro n
  induction n with
  | zero =>
      intro x σ hσ
      have h0 : ∀ p, σ p = 0 := fun p => Nat.le_zero.mp (hσ.1 p)
      rw [stopValue_of_zero h0]
      exact le_of_eq rfl
  | succ n ih =>
      intro x σ hσ
      by_cases hex : ∃ p₀, σ p₀ = 0
      · obtain ⟨p₀, hp₀⟩ := hex
        have h0 : ∀ p, σ p = 0 := by
          intro q
          have : ∀ j, j < σ p₀ → p₀ j = q j := by
            intro j hj
            rw [hp₀] at hj
            exact absurd hj (Nat.not_lt_zero j)
          rw [hσ.2 p₀ q this, hp₀]
        rw [stopValue_of_zero h0]
        exact le_max_left _ _
      · rw [not_exists] at hex
        have hpos : ∀ p, 1 ≤ σ p := fun p => Nat.one_le_iff_ne_zero.mpr (hex p)
        rw [stopValue_consNat hd hσ hpos]
        have hfin : ∀ f : Fin d × Bool → ℝ, Integrable f (stepLaw d) := fun f =>
          integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
        have hmono : (∫ v : Fin d × Bool, stopValue η (x + stepVec v)
              (fun r => σ (consNat v r) - 1) ∂(stepLaw d))
            ≤ ∫ v : Fin d × Bool, u η n (x + stepVec v) ∂(stepLaw d) :=
          integral_mono (hfin _) (hfin _) fun v =>
            ih (x + stepVec v) _ (isStoppingTimeLE_shift' hσ v)
        have hop : (∫ v : Fin d × Bool, u η n (x + stepVec v) ∂(stepLaw d))
            = walkOp (u η n) x := integral_stepLaw_walk hd _ x
        calc η x + ∫ v : Fin d × Bool, stopValue η (x + stepVec v)
                (fun r => σ (consNat v r) - 1) ∂(stepLaw d)
            ≤ η x + walkOp (u η n) x := by
              rw [← hop]
              linarith [hmono]
          _ ≤ u η (n + 1) x := le_max_right _ _

/-- **The odometer is the value of one bounded stopping rule.** -/
theorem u_mem_stopValues (hd : 1 ≤ d) (η : Site d → ℝ) :
    ∀ (n : ℕ) (x : Site d), u η n x ∈ stopValues d η n x := by
  haveI := stepLaw_isProbability hd
  intro n
  induction n with
  | zero =>
      intro x
      show u η 0 x ∈ stopValues d η 0 x
      rw [show u η 0 x = 0 from rfl]
      exact zero_mem_stopValues η 0 x
  | succ n ih =>
      intro x
      have hrec : u η (n + 1) x = max 0 (η x + walkOp (u η n) x) := rfl
      by_cases hle : η x + walkOp (u η n) x ≤ 0
      · rw [hrec, max_eq_left hle]
        exact zero_mem_stopValues η (n + 1) x
      · have hge : (0 : ℝ) ≤ η x + walkOp (u η n) x := le_of_not_ge hle
        rw [hrec, max_eq_right hge]
        choose τ hτ hτval using ih
        have hσ0 : IsStoppingTimeLE (n + 1)
            (fun p => τ (x + stepVec (p 0)) (tailNat p) + 1) := by
          refine ⟨fun p => ?_, fun p q h => ?_⟩
          · show τ (x + stepVec (p 0)) (tailNat p) + 1 ≤ n + 1
            have := (hτ (x + stepVec (p 0))).1 (tailNat p)
            omega
          · have h' : ∀ j, j < τ (x + stepVec (p 0)) (tailNat p) + 1 → p j = q j := h
            have h0 : p 0 = q 0 := h' 0 (by omega)
            have htail : ∀ k, k < τ (x + stepVec (p 0)) (tailNat p) →
                tailNat p k = tailNat q k := fun k hk => h' (k + 1) (by omega)
            show τ (x + stepVec (q 0)) (tailNat q) + 1 = τ (x + stepVec (p 0)) (tailNat p) + 1
            rw [← h0, (hτ (x + stepVec (p 0))).2 (tailNat p) (tailNat q) htail]
        refine ⟨fun p => τ (x + stepVec (p 0)) (tailNat p) + 1, hσ0, ?_⟩
        · have hσ : IsStoppingTimeLE (n + 1)
              (fun p => τ (x + stepVec (p 0)) (tailNat p) + 1) := hσ0
          have hpos : ∀ p, 1 ≤ τ (x + stepVec (p 0)) (tailNat p) + 1 := fun p => Nat.le_add_left 1 _
          rw [stopValue_consNat hd hσ hpos]
          have hshift : ∀ v : Fin d × Bool,
              (fun r => (fun p => τ (x + stepVec (p 0)) (tailNat p) + 1) (consNat v r) - 1)
                = τ (x + stepVec v) := by
            intro v
            funext r
            show τ (x + stepVec ((consNat v r) 0)) (tailNat (consNat v r)) + 1 - 1
              = τ (x + stepVec v) r
            rfl
          have hinner : ∀ v : Fin d × Bool,
              stopValue η (x + stepVec v)
                  (fun r => (fun p => τ (x + stepVec (p 0)) (tailNat p) + 1) (consNat v r) - 1)
                = u η n (x + stepVec v) := by
            intro v
            rw [hshift v, ← hτval (x + stepVec v)]
          simp only [hinner]
          rw [integral_stepLaw_walk hd _ x]

/-- **`eq:stopping` for the simple random walk.**  The divisible odometer is the
least upper bound of the expected rewards of the stopping rules of the walk
bounded by `n`. -/
theorem isLUB_stopValues (hd : 1 ≤ d) (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    IsLUB (stopValues d η n x) (u η n x) := by
  constructor
  · rintro a ⟨σ, hσ, rfl⟩
    exact stopValue_le hd η n x σ hσ
  · intro b hb
    exact hb (u_mem_stopValues hd η n x)

theorem csSup_stopValues (hd : 1 ≤ d) (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    sSup (stopValues d η n x) = u η n x :=
  (isLUB_stopValues hd η n x).csSup_eq ⟨0, zero_mem_stopValues η n x⟩

end Parking

end
