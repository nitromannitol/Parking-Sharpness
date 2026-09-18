/-
Freshness and the pair cancellation estimate. The state, motion decisions and
selected entries are unchanged by replacing the current fresh table. Distinct
labels select distinct entries. The two-position difference therefore satisfies
the walk hitting comparison, uniformly for fixed configurations and priorities.
Every disappearing label is cancelled against a unique opposite partner.
-/
import Parking.Support.DiscrepancyMeas
import Parking.Support.RoundHitting

noncomputable section

open MeasureTheory LatticeProb

variable {d : ℕ}

theorem Parking.matchedCount_update (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (n t : ℕ) (τ : Parking.RoundSlot d → Fin d × Bool)
    (ht : t ≤ n) : Parking.matchedCount η ρ (Function.update σ n τ) t =
      Parking.matchedCount η ρ σ t := by
  funext x
  unfold Parking.matchedCount
  rw [Parking.matchedState_update η ρ σ n t τ ht]

/-- Replacing a current or future table leaves the earlier label state unchanged. -/
theorem Parking.discrepancyState_update (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (n t : ℕ) (τ : Parking.RoundSlot d → Fin d × Bool)
    (ht : t ≤ n) : Parking.discrepancyState c ρ (Function.update σ n τ) t =
      Parking.discrepancyState c ρ σ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Parking.discrepancyState, Parking.discrepancyState, ih (by omega),
        Parking.matchedCount_update _ ρ σ n t τ (by omega),
        Parking.matchedCount_update _ ρ σ n t τ (by omega), Function.update_of_ne (by omega)]

/-- The current table entry assigned to a label, including its auxiliary entry
when it does not move. -/
def Parking.discrepancyIndex (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) (p : Label d) : Parking.RoundSlot d :=
  Parking.discrepancySlot c ρ (Parking.matchedCount (Parking.coupledConf false c) ρ σ t)
    (Parking.matchedCount (Parking.coupledConf true c) ρ σ t) (Parking.discrepancyState c ρ σ t) t p

def Parking.discrepancyDoesMove (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) (p : Label d) : Bool := by
  classical
  exact decide (Parking.discrepancyMoving c ρ
    (Parking.matchedCount (Parking.coupledConf false c) ρ σ t)
    (Parking.matchedCount (Parking.coupledConf true c) ρ σ t) (Parking.discrepancyState c ρ σ t) t p)

theorem Parking.discrepancyIndex_update (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (n t : ℕ) (τ : Parking.RoundSlot d → Fin d × Bool)
    (ht : t ≤ n) : Parking.discrepancyIndex c ρ (Function.update σ n τ) t =
      Parking.discrepancyIndex c ρ σ t := by
  funext p
  unfold Parking.discrepancyIndex
  rw [Parking.matchedCount_update _ ρ σ n t τ ht,
    Parking.matchedCount_update _ ρ σ n t τ ht, Parking.discrepancyState_update c ρ σ n t τ ht]

theorem Parking.discrepancyDoesMove_update (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (n t : ℕ) (τ : Parking.RoundSlot d → Fin d × Bool)
    (ht : t ≤ n) : Parking.discrepancyDoesMove c ρ (Function.update σ n τ) t =
      Parking.discrepancyDoesMove c ρ σ t := by
  funext p
  unfold Parking.discrepancyDoesMove
  rw [Parking.matchedCount_update _ ρ σ n t τ ht,
    Parking.matchedCount_update _ ρ σ n t τ ht, Parking.discrepancyState_update c ρ σ n t τ ht]

/-- The difference of two label positions appends the first step and the
negative of the second step. -/
theorem Parking.discrepancyPair_next (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) (p q : Label d) :
    (Parking.discrepancyState c ρ σ (t + 1)).pos p -
        (Parking.discrepancyState c ρ σ (t + 1)).pos q =
      Parking.roundDifference
        ((Parking.discrepancyState c ρ σ t).pos p - (Parking.discrepancyState c ρ σ t).pos q)
        (Parking.discrepancyDoesMove c ρ σ t p) (Parking.discrepancyDoesMove c ρ σ t q)
        (σ t (Parking.discrepancyIndex c ρ σ t p))
        (Parking.reverseDirection (σ t (Parking.discrepancyIndex c ρ σ t q))) := by
  classical
  let a := Parking.matchedCount (Parking.coupledConf false c) ρ σ t
  let b := Parking.matchedCount (Parking.coupledConf true c) ρ σ t
  let S := Parking.discrepancyState c ρ σ t
  change Parking.discrepancyNextPos c ρ a b (σ t) S t p -
      Parking.discrepancyNextPos c ρ a b (σ t) S t q =
    Parking.roundDifference (S.pos p - S.pos q)
      (decide (Parking.discrepancyMoving c ρ a b S t p))
      (decide (Parking.discrepancyMoving c ρ a b S t q))
      (σ t (Parking.discrepancySlot c ρ a b S t p))
      (Parking.reverseDirection (σ t (Parking.discrepancySlot c ρ a b S t q)))
  by_cases hp : Parking.discrepancyMoving c ρ a b S t p <;>
    by_cases hq : Parking.discrepancyMoving c ρ a b S t q <;>
    simp [Parking.discrepancyNextPos, Parking.roundDifference, hp, hq,
      Parking.stepVec_reverseDirection] <;> abel

/-- With both initial configurations and all priorities fixed, two distinct
labels have no greater meeting probability than a walk with twice as many steps. -/
theorem Parking.discrepancyPair_hit_le (hd : 1 ≤ d) (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (p q : Label d) (hpq : p ≠ q) (T : ℕ) :
    (Parking.roundNoiseLaw d) {σ | ∃ s ≤ T,
      (Parking.discrepancyState c ρ σ s).pos p = (Parking.discrepancyState c ρ σ s).pos q} ≤
      (Parking.walkLaw d) {r | ∃ s ≤ 2 * T, Parking.walkPath (p.1 - q.1) r s = 0} := by
  let X : Parking.RoundNoise d → ℕ → Site d := fun σ s =>
    (Parking.discrepancyState c ρ σ s).pos p - (Parking.discrepancyState c ρ σ s).pos q
  have hS := Parking.measurableState_discrepancyState ⟨0, hd⟩ (fun _ => c) (fun _ => ρ) id
    measurable_const measurable_const measurable_id
  have hX : Measurable X := measurable_pi_lambda _ fun s => ((hS s).2.1 p).sub ((hS s).2.1 q)
  have hset : {σ | ∃ s ≤ T,
      (Parking.discrepancyState c ρ σ s).pos p = (Parking.discrepancyState c ρ σ s).pos q} =
      {σ | ∃ s ≤ T, X σ s = 0} := by
    ext σ
    simp only [Set.mem_setOf_eq, X, sub_eq_zero]
  rw [hset]
  apply Parking.roundPath_hit_le hd X hX (p.1 - q.1)
    (fun σ n => Parking.discrepancyIndex c ρ σ n p)
    (fun σ n => Parking.discrepancyIndex c ρ σ n q)
    (fun σ n => Parking.discrepancyDoesMove c ρ σ n p)
    (fun σ n => Parking.discrepancyDoesMove c ρ σ n q)
  · exact fun _ => rfl
  · intro σ n k τ hk
    dsimp [X]
    rw [Parking.discrepancyState_update c ρ σ n k τ hk]
  · intro σ n τ
    exact congrFun (Parking.discrepancyIndex_update c ρ σ n n τ le_rfl) p
  · intro σ n τ
    exact congrFun (Parking.discrepancyIndex_update c ρ σ n n τ le_rfl) q
  · intro σ n τ
    exact congrFun (Parking.discrepancyDoesMove_update c ρ σ n n τ le_rfl) p
  · intro σ n τ
    exact congrFun (Parking.discrepancyDoesMove_update c ρ σ n n τ le_rfl) q
  · intro σ n h
    exact hpq (Parking.discrepancySlot_injective c ρ _ _ _ n h)
  · exact fun σ n => Parking.discrepancyPair_next c ρ σ n p q

/-- The particular pair cancelled in a round. The two labels have equal
priority ranks in the opposite arrival lists at their common destination. -/
def Parking.discrepancyCancelledAt (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) (p q : Label d) : Prop :=
  Parking.RankPair
    (Parking.discrepancyArrivalsSign c ρ
      (Parking.matchedCount (Parking.coupledConf false c) ρ σ t)
      (Parking.matchedCount (Parking.coupledConf true c) ρ σ t) (σ t)
      (Parking.discrepancyState c ρ σ t) t
      ((Parking.discrepancyState c ρ σ (t + 1)).pos p) (Parking.discrepancySign c p))
    (Parking.discrepancyArrivalsSign c ρ
      (Parking.matchedCount (Parking.coupledConf false c) ρ σ t)
      (Parking.matchedCount (Parking.coupledConf true c) ρ σ t) (σ t)
      (Parking.discrepancyState c ρ σ t) t
      ((Parking.discrepancyState c ρ σ (t + 1)).pos p) (!Parking.discrepancySign c p))
    (Parking.matchKey ρ 0) p q

def Parking.discrepancyCancelledBy (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (T : ℕ) (p q : Label d) : Prop :=
  ∃ t < T, Parking.discrepancyCancelledAt c ρ σ t p q

theorem Parking.discrepancyCancelledAt_positions (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ) (p q : Label d)
    (hpq : Parking.discrepancyCancelledAt c ρ σ t p q) :
    (Parking.discrepancyState c ρ σ (t + 1)).pos p =
      (Parking.discrepancyState c ρ σ (t + 1)).pos q := by
  have hArr := (Finset.mem_filter.mp hpq.2.1).1
  exact (Finset.mem_filter.mp hArr).2.2.symm

theorem Parking.discrepancyCancelledAt_sign (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ) (p q : Label d)
    (hpq : Parking.discrepancyCancelledAt c ρ σ t p q) :
    Parking.discrepancySign c q = !Parking.discrepancySign c p :=
  (Finset.mem_filter.mp hpq.2.1).2

theorem Parking.discrepancyCancelledAt_symm (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ) (p q : Label d)
    (hpq : Parking.discrepancyCancelledAt c ρ σ t p q) :
    Parking.discrepancyCancelledAt c ρ σ t q p := by
  have hpos := Parking.discrepancyCancelledAt_positions c ρ σ t p q hpq
  have hsign := Parking.discrepancyCancelledAt_sign c ρ σ t p q hpq
  unfold Parking.discrepancyCancelledAt
  rw [← hpos, hsign, Bool.not_not]
  exact Parking.rankPair_symm hpq

theorem Parking.discrepancyCancelledAt_dead (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ) (p q : Label d)
    (hpq : Parking.discrepancyCancelledAt c ρ σ t p q) :
    (Parking.discrepancyState c ρ σ (t + 1)).active p = false := by
  exact decide_eq_false (Parking.not_mem_rankSurvivors_of_pair hpq)

/-- Every disappearing label is paired with exactly one opposite label. -/
theorem Parking.existsUnique_discrepancyCancelledAt (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ) (p : Label d)
    (ha : (Parking.discrepancyState c ρ σ t).active p = true)
    (hdead : (Parking.discrepancyState c ρ σ (t + 1)).active p = false) :
    ∃! q, Parking.discrepancyCancelledAt c ρ σ t p q := by
  classical
  apply Parking.existsUnique_rankPair _ _ _ (Parking.matchKey_injective ρ 0).injOn
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, ha, rfl⟩, rfl⟩
    have hidx : p.2 < (Parking.discrepancyConf c p.1).toNat := by
      simpa [Parking.discrepancyState, initial] using Parking.discrepancyState_active_le c ρ σ p t ha
    exact mem_candidates (fun i => by
      have h := Parking.abs_discrepancyPos_sub_start_le c ρ σ (t + 1) p i
      rwa [abs_sub_comm] at h) hidx
  · exact of_decide_eq_false hdead

/-- **The conditional pair cancellation bound.** Fixing the two initial
configurations and every priority, cancellation by round `T` has probability
at most that of a simple walk from the initial difference hitting zero within
`2T` steps. This is a section-wise bound, before averaging any initial data. -/
theorem Parking.discrepancy_cancel_prob_le (hd : 1 ≤ d) (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (p q : Label d) (hpq : p ≠ q) (T : ℕ) :
    (Parking.roundNoiseLaw d) {σ | Parking.discrepancyCancelledBy c ρ σ T p q} ≤
      (Parking.walkLaw d) {r | ∃ s ≤ 2 * T, Parking.walkPath (p.1 - q.1) r s = 0} := by
  calc
    (Parking.roundNoiseLaw d) {σ | Parking.discrepancyCancelledBy c ρ σ T p q} ≤
        (Parking.roundNoiseLaw d) {σ | ∃ s ≤ T,
          (Parking.discrepancyState c ρ σ s).pos p = (Parking.discrepancyState c ρ σ s).pos q} := by
      apply measure_mono
      intro σ h
      obtain ⟨t, ht, hpq⟩ := h
      exact ⟨t + 1, by omega, Parking.discrepancyCancelledAt_positions c ρ σ t p q hpq⟩
    _ ≤ _ := Parking.discrepancyPair_hit_le hd c ρ p q hpq T

end
