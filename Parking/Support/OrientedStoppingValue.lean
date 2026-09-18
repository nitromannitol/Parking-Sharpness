/-
The oriented form of `eq:stopping` (`parking.tex:866-874`): the oriented
divisible odometer `u⃗_n` of `eq:oriented-divisible` (`parking.tex:3003`) is the
value of the bounded optimal stopping problem of the oriented walk.

`u⃗_0 = 0` and `u⃗_{n+1} = (η + P⃗u⃗_n)^+` is the dynamic programming equation of
the problem with reward `∑_{j<σ} η(X_j)`, so the two halves below are the two
halves of a least upper bound: every bounded stopping rule collects at most
`u⃗_n(x)` in expectation, and one of them collects exactly that.  The rule that
attains it stops at once when the continuation value `η(x) + (P⃗u⃗_n)(x)` is
not positive, and otherwise takes one step and follows the attaining rule of
the site it reaches.

The supremum is asserted as a least upper bound, so that no junk value of an
unattained or unbounded supremum can satisfy it, exactly as
`Parking.External.Stopping` does for the simple random walk.
-/
import Parking.Support.OrientedStopping

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

theorem orientedStopReward_congr {n : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE n σ) (η : Site d → ℝ) (x : Site d)
    {p q : ℕ → Fin d × Bool} (h : ∀ i, i < n → p i = q i) :
    orientedStopReward η x σ p = orientedStopReward η x σ q := by
  have hle : σ p ≤ n := hσ.1 p
  have hpq : ∀ j, j < σ p → p j = q j := fun j hj => h j (lt_of_lt_of_le hj hle)
  have hsame : σ q = σ p := hσ.2 p q hpq
  unfold orientedStopReward
  rw [hsame]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjlt : j < σ p := Finset.mem_range.mp hj
  rw [orientedPath_congr x j (fun i hi => h i (lt_of_lt_of_le (hi.trans hjlt) hle))]

theorem integrable_orientedStopReward (hd : 1 ≤ d) {n : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE n σ) (η : Site d → ℝ) (x : Site d) :
    Integrable (orientedStopReward η x σ) (walkLaw d) :=
  integrable_of_finite_dependence hd n _ (fun _ _ h => orientedStopReward_congr hσ η x h)

theorem zero_mem_orientedStopValues (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    (0 : ℝ) ∈ orientedStopValues d η n x := by
  refine ⟨fun _ => 0, ⟨fun _ => Nat.zero_le _, fun _ _ _ => rfl⟩, ?_⟩
  unfold orientedStopValue orientedStopReward
  simp

/-- The shifted rule: what is left of `σ` after the first direction `u` has been
read, when `σ` never stops at once. -/
theorem isStoppingTimeLE_shift {n : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
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

theorem orientedStopReward_consNat {σ : (ℕ → Fin d × Bool) → ℕ}
    (hpos : ∀ p, 1 ≤ σ p) (η : Site d → ℝ) (x : Site d)
    (u : Fin d × Bool) (r : ℕ → Fin d × Bool) :
    orientedStopReward η x σ (consNat u r)
      = η x + orientedStopReward η (x - unit u.1) (fun r' => σ (consNat u r') - 1) r := by
  have hm : σ (consNat u r) = (σ (consNat u r) - 1) + 1 := by
    have := hpos (consNat u r)
    omega
  unfold orientedStopReward
  rw [hm, Finset.sum_range_succ']
  have hstep : ∀ j : ℕ, orientedPath x (consNat u r) (j + 1)
      = orientedPath (x - unit u.1) r j := by
    intro j
    rw [orientedPath_tail]
    rfl
  simp only [hstep]
  show _ = η x + _
  rw [add_comm]
  rfl

theorem orientedStopValue_consNat (hd : 1 ≤ d) {n : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE (n + 1) σ) (hpos : ∀ p, 1 ≤ σ p) (η : Site d → ℝ) (x : Site d) :
    orientedStopValue η x σ
      = η x + ∫ u : Fin d × Bool, orientedStopValue η (x - unit u.1)
          (fun r => σ (consNat u r) - 1) ∂(stepLaw d) := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have hi : Integrable (orientedStopReward η x σ) (walkLaw d) :=
    integrable_orientedStopReward hd hσ η x
  have hfin : ∀ f : Fin d × Bool → ℝ, Integrable f (stepLaw d) := fun f =>
    integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
  rw [orientedStopValue, show walkLaw d = Measure.infinitePi fun _ : ℕ => stepLaw d from rfl,
    integral_infinitePi_nat_head_tail (stepLaw d) (orientedStopReward η x σ)
      (by rwa [show (Measure.infinitePi fun _ : ℕ => stepLaw d) = walkLaw d from rfl])]
  have hinner : ∀ u : Fin d × Bool,
      (∫ r, orientedStopReward η x σ (consNat u r)
          ∂(Measure.infinitePi fun _ : ℕ => stepLaw d))
        = η x + orientedStopValue η (x - unit u.1) (fun r' => σ (consNat u r') - 1) := by
    intro u
    have hcongr : ∀ r, orientedStopReward η x σ (consNat u r)
        = η x + orientedStopReward η (x - unit u.1) (fun r' => σ (consNat u r') - 1) r :=
      fun r => orientedStopReward_consNat hpos η x u r
    simp only [hcongr]
    rw [show (Measure.infinitePi fun _ : ℕ => stepLaw d) = walkLaw d from rfl,
      integral_add (integrable_const _)
        (integrable_orientedStopReward hd (isStoppingTimeLE_shift hσ u) η _),
      integral_const]
    simp [orientedStopValue]
  simp only [hinner]
  rw [integral_add (hfin _) (hfin _), integral_const]
  simp

theorem orientedStopValue_of_zero {σ : (ℕ → Fin d × Bool) → ℕ}
    (h0 : ∀ p, σ p = 0) (η : Site d → ℝ) (x : Site d) :
    orientedStopValue η x σ = 0 := by
  unfold orientedStopValue orientedStopReward
  simp [h0]

/-- **The oriented odometer bounds every bounded stopping rule.** -/
theorem orientedStopValue_le (hd : 1 ≤ d) (η : Site d → ℝ) :
    ∀ (n : ℕ) (x : Site d) (σ : (ℕ → Fin d × Bool) → ℕ), IsStoppingTimeLE n σ →
      orientedStopValue η x σ ≤ uOriented η n x := by
  haveI := stepLaw_isProbability hd
  intro n
  induction n with
  | zero =>
      intro x σ hσ
      have h0 : ∀ p, σ p = 0 := fun p => Nat.le_zero.mp (hσ.1 p)
      rw [orientedStopValue_of_zero h0]
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
        rw [orientedStopValue_of_zero h0]
        exact le_max_left _ _
      · rw [not_exists] at hex
        have hpos : ∀ p, 1 ≤ σ p := fun p => Nat.one_le_iff_ne_zero.mpr (hex p)
        rw [orientedStopValue_consNat hd hσ hpos]
        have hfin : ∀ f : Fin d × Bool → ℝ, Integrable f (stepLaw d) := fun f =>
          integrableOn_univ.mp (IntegrableOn.of_finite Set.finite_univ)
        have hmono : (∫ u : Fin d × Bool, orientedStopValue η (x - unit u.1)
              (fun r => σ (consNat u r) - 1) ∂(stepLaw d))
            ≤ ∫ u : Fin d × Bool, uOriented η n (x - unit u.1) ∂(stepLaw d) :=
          integral_mono (hfin _) (hfin _) fun u =>
            ih (x - unit u.1) _ (isStoppingTimeLE_shift hσ u)
        have hop : (∫ u : Fin d × Bool, uOriented η n (x - unit u.1) ∂(stepLaw d))
            = orientedOp (uOriented η n) x := integral_stepLaw_oriented hd _ x
        calc η x + ∫ u : Fin d × Bool, orientedStopValue η (x - unit u.1)
                (fun r => σ (consNat u r) - 1) ∂(stepLaw d)
            ≤ η x + orientedOp (uOriented η n) x := by
              rw [← hop]
              linarith [hmono]
          _ ≤ uOriented η (n + 1) x := le_max_right _ _

/-- **The oriented odometer is the value of one bounded stopping rule.** -/
theorem uOriented_mem_orientedStopValues (hd : 1 ≤ d) (η : Site d → ℝ) :
    ∀ (n : ℕ) (x : Site d), uOriented η n x ∈ orientedStopValues d η n x := by
  haveI := stepLaw_isProbability hd
  intro n
  induction n with
  | zero =>
      intro x
      show uOriented η 0 x ∈ orientedStopValues d η 0 x
      rw [show uOriented η 0 x = 0 from rfl]
      exact zero_mem_orientedStopValues η 0 x
  | succ n ih =>
      intro x
      have hrec : uOriented η (n + 1) x = max 0 (η x + orientedOp (uOriented η n) x) := rfl
      by_cases hle : η x + orientedOp (uOriented η n) x ≤ 0
      · rw [hrec, max_eq_left hle]
        exact zero_mem_orientedStopValues η (n + 1) x
      · have hge : (0 : ℝ) ≤ η x + orientedOp (uOriented η n) x := le_of_not_ge hle
        rw [hrec, max_eq_right hge]
        choose τ hτ hτval using ih
        have hσ0 : IsStoppingTimeLE (n + 1)
            (fun p => τ (x - unit (p 0).1) (tailNat p) + 1) := by
          refine ⟨fun p => ?_, fun p q h => ?_⟩
          · show τ (x - unit (p 0).1) (tailNat p) + 1 ≤ n + 1
            have := (hτ (x - unit (p 0).1)).1 (tailNat p)
            omega
          · have h' : ∀ j, j < τ (x - unit (p 0).1) (tailNat p) + 1 → p j = q j := h
            have h0 : p 0 = q 0 := h' 0 (by omega)
            have htail : ∀ k, k < τ (x - unit (p 0).1) (tailNat p) →
                tailNat p k = tailNat q k := fun k hk => h' (k + 1) (by omega)
            show τ (x - unit (q 0).1) (tailNat q) + 1 = τ (x - unit (p 0).1) (tailNat p) + 1
            rw [← h0, (hτ (x - unit (p 0).1)).2 (tailNat p) (tailNat q) htail]
        refine ⟨fun p => τ (x - unit (p 0).1) (tailNat p) + 1, hσ0, ?_⟩
        · have hσ : IsStoppingTimeLE (n + 1)
              (fun p => τ (x - unit (p 0).1) (tailNat p) + 1) := hσ0
          have hpos : ∀ p, 1 ≤ τ (x - unit (p 0).1) (tailNat p) + 1 := fun p => Nat.le_add_left 1 _
          rw [orientedStopValue_consNat hd hσ hpos]
          have hshift : ∀ u : Fin d × Bool,
              (fun r => (fun p => τ (x - unit (p 0).1) (tailNat p) + 1) (consNat u r) - 1)
                = τ (x - unit u.1) := by
            intro u
            funext r
            show τ (x - unit ((consNat u r) 0).1) (tailNat (consNat u r)) + 1 - 1
              = τ (x - unit u.1) r
            rfl
          have hinner : ∀ u : Fin d × Bool,
              orientedStopValue η (x - unit u.1)
                  (fun r => (fun p => τ (x - unit (p 0).1) (tailNat p) + 1) (consNat u r) - 1)
                = uOriented η n (x - unit u.1) := by
            intro u
            rw [hshift u, ← hτval (x - unit u.1)]
          simp only [hinner]
          rw [integral_stepLaw_oriented hd _ x]

/-- **The oriented form of `eq:stopping`.**  The oriented divisible odometer is
the least upper bound of the expected rewards of the stopping rules of the
oriented walk bounded by `n`. -/
theorem isLUB_orientedStopValues (hd : 1 ≤ d) (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    IsLUB (orientedStopValues d η n x) (uOriented η n x) := by
  constructor
  · rintro a ⟨σ, hσ, rfl⟩
    exact orientedStopValue_le hd η n x σ hσ
  · intro b hb
    exact hb (uOriented_mem_orientedStopValues hd η n x)

/-- The oriented form of `eq:stopping` read as a supremum. -/
theorem csSup_orientedStopValues (hd : 1 ≤ d) (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    sSup (orientedStopValues d η n x) = uOriented η n x :=
  (isLUB_orientedStopValues hd η n x).csSup_eq ⟨0, zero_mem_orientedStopValues η n x⟩

/-- The expected reward is additive in the scenery. -/
theorem orientedStopValue_add (hd : 1 ≤ d) {n : ℕ} {σ : (ℕ → Fin d × Bool) → ℕ}
    (hσ : IsStoppingTimeLE n σ) (η η' : Site d → ℝ) (x : Site d) :
    orientedStopValue (fun y => η y + η' y) x σ
      = orientedStopValue η x σ + orientedStopValue η' x σ := by
  have hpt : ∀ p : ℕ → Fin d × Bool,
      orientedStopReward (fun y => η y + η' y) x σ p
        = orientedStopReward η x σ p + orientedStopReward η' x σ p := by
    intro p
    unfold orientedStopReward
    rw [← Finset.sum_add_distrib]
  unfold orientedStopValue
  simp only [hpt]
  exact integral_add (integrable_orientedStopReward hd hσ η x)
    (integrable_orientedStopReward hd hσ η' x)

/-- The expected reward is homogeneous in the scenery. -/
theorem orientedStopValue_const_mul (c : ℝ) (η : Site d → ℝ) (x : Site d)
    (σ : (ℕ → Fin d × Bool) → ℕ) :
    orientedStopValue (fun y => c * η y) x σ = c * orientedStopValue η x σ := by
  have hpt : ∀ p : ℕ → Fin d × Bool,
      orientedStopReward (fun y => c * η y) x σ p = c * orientedStopReward η x σ p := by
    intro p
    unfold orientedStopReward
    rw [Finset.mul_sum]
  unfold orientedStopValue
  simp only [hpt]
  exact MeasureTheory.integral_const_mul c _

end Parking

end
