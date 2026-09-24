/-
Persistent discrepancy labels. Fixed priorities assign labels to surplus
instruction entries and pair opposite arrivals for cancellation. Labels keep
their sign and priority when their carriers change, move at speed at most one,
and never return after removal. The finite candidate sets retain every live
label.
-/
import Parking.Support.CancelByRank
import Parking.Support.CoupledLaw
import Parking.Support.MatchedCounts

noncomputable section

open LatticeProb

variable {d : ℕ}

/-- The initial number of discrepancy labels at each site. -/
def Parking.discrepancyConf (c : Site d → ℤ × ℤ) : Site d → ℤ :=
  fun x => |(c x).2 - (c x).1|

/-- A label retains its initial sign throughout its life. -/
def Parking.discrepancySign (c : Site d → ℤ × ℤ) (p : Label d) : Bool :=
  decide (0 < (c p.1).2 - (c p.1).1)

/-- Labels present at a site. Activity and position are stored in the first two
fields of a state; the other two fields are zero for this label process. -/
def Parking.discrepancyAt (c : Site d → ℤ × ℤ) (S : State d) (t : ℕ) (x : Site d) :
    Finset (Label d) := Parking.matchActive (Parking.discrepancyConf c) S t x

/-- The number of excess active particles at a site. -/
def Parking.discrepancyMoveCount (a b : Site d → ℕ) (x : Site d) : ℕ :=
  (a x - b x) + (b x - a x)

def Parking.discrepancyMoving (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (a b : Site d → ℕ) (S : State d) (t : ℕ) (p : Label d) : Prop :=
  p ∈ Parking.discrepancyAt c S t (S.pos p) ∧
    rankIn (Parking.discrepancyAt c S t (S.pos p)) (Parking.matchKey ρ 0) p <
      Parking.discrepancyMoveCount a b (S.pos p)

/-- Moving labels use the surplus entries after the shared initial segment.
Labels that wait have separate auxiliary entries. -/
def Parking.discrepancySlot (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (a b : Site d → ℕ) (S : State d) (t : ℕ) (p : Label d) : Parking.RoundSlot d := by
  classical
  exact if Parking.discrepancyMoving c ρ a b S t p then
    Sum.inl (S.pos p, min (a (S.pos p)) (b (S.pos p)) +
      rankIn (Parking.discrepancyAt c S t (S.pos p)) (Parking.matchKey ρ 0) p)
  else Sum.inr p

theorem Parking.discrepancySlot_injective (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (a b : Site d → ℕ) (S : State d) (t : ℕ) :
    Function.Injective (Parking.discrepancySlot c ρ a b S t) := by
  classical
  intro p q hpq
  unfold Parking.discrepancySlot at hpq
  split_ifs at hpq with hp hq hq
  · have heq := Sum.inl_injective hpq
    have hpos : S.pos p = S.pos q := congrArg Prod.fst heq
    have hrank := congrArg Prod.snd heq
    have hp' := hp.1
    have hq' := hq.1
    rw [← hpos] at hq' hrank
    exact rankIn_injOn (Parking.matchKey_injective ρ 0).injOn hp' hq'
      (Nat.add_left_cancel hrank)
  · exact Sum.inr_injective hpq

def Parking.discrepancyNextPos (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (a b : Site d → ℕ) (τ : Parking.RoundSlot d → Fin d × Bool)
    (S : State d) (t : ℕ) (p : Label d) : Site d := by
  classical
  exact if Parking.discrepancyMoving c ρ a b S t p then
    S.pos p + Parking.stepVec (τ (Parking.discrepancySlot c ρ a b S t p))
  else S.pos p

/-- Arriving labels include the labels that wait at holes. -/
def Parking.discrepancyArrivals (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (a b : Site d → ℕ) (τ : Parking.RoundSlot d → Fin d × Bool)
    (S : State d) (t : ℕ) (x : Site d) : Finset (Label d) :=
  (candidates (Parking.discrepancyConf c) x (t + 1)).filter fun p =>
    S.active p ∧ Parking.discrepancyNextPos c ρ a b τ S t p = x

def Parking.discrepancyArrivalsSign (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (a b : Site d → ℕ) (τ : Parking.RoundSlot d → Fin d × Bool)
    (S : State d) (t : ℕ) (x : Site d) (sgn : Bool) : Finset (Label d) :=
  (Parking.discrepancyArrivals c ρ a b τ S t x).filter fun p =>
    Parking.discrepancySign c p = sgn

/-- A round transfers the labels to the surplus departures, moves those
labels, then cancels opposite labels in increasing order of their fixed priorities. -/
def Parking.discrepancyStep (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (a b : Site d → ℕ) (τ : Parking.RoundSlot d → Fin d × Bool)
    (S : State d) (t : ℕ) : State d where
  active := fun p => decide (p ∈ Parking.rankSurvivors
    (Parking.discrepancyArrivalsSign c ρ a b τ S t
      (Parking.discrepancyNextPos c ρ a b τ S t p) (Parking.discrepancySign c p))
    (Parking.discrepancyArrivalsSign c ρ a b τ S t
      (Parking.discrepancyNextPos c ρ a b τ S t p) (!Parking.discrepancySign c p))
    (Parking.matchKey ρ 0))
  pos := Parking.discrepancyNextPos c ρ a b τ S t
  holes := fun _ => 0
  departures := fun _ => 0

/-- The label priorities are fixed at creation and stay with the label when
its physical carrier changes. -/
def Parking.discrepancyState (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) : ℕ → State d
  | 0 => initial (Parking.discrepancyConf c)
  | t + 1 => Parking.discrepancyStep c ρ
      (Parking.matchedCount (Parking.coupledConf false c) ρ σ t)
      (Parking.matchedCount (Parking.coupledConf true c) ρ σ t)
      (σ t) (Parking.discrepancyState c ρ σ t) t

def Parking.discrepancyAtSign (c : Site d → ℤ × ℤ) (S : State d)
    (t : ℕ) (x : Site d) (sgn : Bool) : Finset (Label d) :=
  (Parking.discrepancyAt c S t x).filter fun p => Parking.discrepancySign c p = sgn

/-- The labels of one sign surviving a round are precisely the unmatched
tail of that sign's arrivals, with its original priorities. -/
theorem Parking.discrepancyAtSign_step (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (a b : Site d → ℕ)
    (τ : Parking.RoundSlot d → Fin d × Bool) (S : State d) (t : ℕ) (x : Site d)
    (sgn : Bool) :
    Parking.discrepancyAtSign c (Parking.discrepancyStep c ρ a b τ S t) (t + 1) x sgn =
      Parking.rankSurvivors (Parking.discrepancyArrivalsSign c ρ a b τ S t x sgn)
        (Parking.discrepancyArrivalsSign c ρ a b τ S t x (!sgn)) (Parking.matchKey ρ 0) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hp, hsign⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hact, hpos⟩ := Finset.mem_filter.mp hp
    change decide (p ∈ Parking.rankSurvivors
      (Parking.discrepancyArrivalsSign c ρ a b τ S t
        (Parking.discrepancyNextPos c ρ a b τ S t p) (Parking.discrepancySign c p))
      (Parking.discrepancyArrivalsSign c ρ a b τ S t
        (Parking.discrepancyNextPos c ρ a b τ S t p) (!Parking.discrepancySign c p))
      (Parking.matchKey ρ 0)) = true at hact
    have hm := of_decide_eq_true hact
    change Parking.discrepancyNextPos c ρ a b τ S t p = x at hpos
    rw [hpos, hsign] at hm
    exact hm
  · intro hp
    have hArr := (Finset.mem_filter.mp hp).1
    obtain ⟨hArr, hsign⟩ := Finset.mem_filter.mp hArr
    obtain ⟨hcan, hactive, hpos⟩ := Finset.mem_filter.mp hArr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hcan, ?_, hpos⟩, hsign⟩
    change decide (p ∈ Parking.rankSurvivors
      (Parking.discrepancyArrivalsSign c ρ a b τ S t
        (Parking.discrepancyNextPos c ρ a b τ S t p) (Parking.discrepancySign c p))
      (Parking.discrepancyArrivalsSign c ρ a b τ S t
        (Parking.discrepancyNextPos c ρ a b τ S t p) (!Parking.discrepancySign c p))
      (Parking.matchKey ρ 0)) = true
    apply decide_eq_true
    rw [hpos, hsign]
    exact hp

theorem Parking.card_discrepancyAtSign_step (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (a b : Site d → ℕ)
    (τ : Parking.RoundSlot d → Fin d × Bool) (S : State d) (t : ℕ) (x : Site d)
    (sgn : Bool) :
    (Parking.discrepancyAtSign c (Parking.discrepancyStep c ρ a b τ S t)
      (t + 1) x sgn).card =
      (Parking.discrepancyArrivalsSign c ρ a b τ S t x sgn).card -
        (Parking.discrepancyArrivalsSign c ρ a b τ S t x (!sgn)).card := by
  rw [Parking.discrepancyAtSign_step]
  exact Parking.card_rankSurvivors _ _ _ (Parking.matchKey_injective ρ 0).injOn

/-- Cancellation leaves only one sign at each site. -/
theorem Parking.discrepancyAtSign_step_empty_or_empty (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (a b : Site d → ℕ)
    (τ : Parking.RoundSlot d → Fin d × Bool) (S : State d) (t : ℕ) (x : Site d) :
    Parking.discrepancyAtSign c (Parking.discrepancyStep c ρ a b τ S t) (t + 1) x true = ∅ ∨
      Parking.discrepancyAtSign c (Parking.discrepancyStep c ρ a b τ S t) (t + 1) x false = ∅ := by
  simp only [Parking.discrepancyAtSign_step, Bool.not_true, Bool.not_false]
  exact Parking.rankSurvivors_empty_or_empty _ _ _
    (Parking.matchKey_injective ρ 0).injOn (Parking.matchKey_injective ρ 0).injOn

theorem Parking.discrepancyStep_active_imp (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (a b : Site d → ℕ)
    (τ : Parking.RoundSlot d → Fin d × Bool) (S : State d) (t : ℕ) (p : Label d)
    (hp : (Parking.discrepancyStep c ρ a b τ S t).active p = true) : S.active p = true := by
  have hs := of_decide_eq_true hp
  have hs' := (Finset.mem_filter.mp hs).1
  have hs'' := (Finset.mem_filter.mp hs').1
  exact (Finset.mem_filter.mp hs'').2.1

/-- Once a label disappears it never returns. -/
theorem Parking.discrepancyState_active_le (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (p : Label d) (t : ℕ)
    (hp : (Parking.discrepancyState c ρ σ t).active p = true) :
    (Parking.discrepancyState c ρ σ 0).active p = true := by
  induction t with
  | zero => exact hp
  | succ t ih =>
      exact ih (Parking.discrepancyStep_active_imp c ρ _ _ _ _ t p hp)

/-- A label moves by at most one unit in every coordinate in a round. -/
theorem Parking.abs_discrepancyPos_sub_start_le (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ) (p : Label d) (i : Fin d) :
    |(Parking.discrepancyState c ρ σ t).pos p i - p.1 i| ≤ (t : ℤ) := by
  induction t with
  | zero => simp [Parking.discrepancyState, initial]
  | succ t ih =>
      have hstep : |(Parking.discrepancyState c ρ σ (t + 1)).pos p i -
          (Parking.discrepancyState c ρ σ t).pos p i| ≤ 1 := by
        change |(Parking.discrepancyNextPos c ρ _ _ _ _ t p) i -
          (Parking.discrepancyState c ρ σ t).pos p i| ≤ 1
        unfold Parking.discrepancyNextPos
        split
        · simpa only [Pi.add_apply, add_sub_cancel_left] using Parking.abs_stepVec_le_one _ i
        · simp
      calc |(Parking.discrepancyState c ρ σ (t + 1)).pos p i - p.1 i|
          ≤ |(Parking.discrepancyState c ρ σ (t + 1)).pos p i -
              (Parking.discrepancyState c ρ σ t).pos p i| +
            |(Parking.discrepancyState c ρ σ t).pos p i - p.1 i| := abs_sub_le _ _ _
        _ ≤ 1 + (t : ℤ) := add_le_add hstep ih
        _ = ((t + 1 : ℕ) : ℤ) := by omega

theorem Parking.mem_discrepancyAt_iff (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ) (x : Site d) (p : Label d) :
    p ∈ Parking.discrepancyAt c (Parking.discrepancyState c ρ σ t) t x ↔
      (Parking.discrepancyState c ρ σ t).active p = true ∧
        (Parking.discrepancyState c ρ σ t).pos p = x := by
  unfold Parking.discrepancyAt Parking.matchActive
  rw [Finset.mem_filter]
  refine ⟨fun hp => hp.2, fun hp => ⟨?_, hp⟩⟩
  have hidx : p.2 < ((Parking.discrepancyConf c) p.1).toNat := by
    simpa [Parking.discrepancyState, initial] using
      Parking.discrepancyState_active_le c ρ σ p t hp.1
  apply mem_candidates _ hidx
  intro i
  have hb := Parking.abs_discrepancyPos_sub_start_le c ρ σ t p i
  rw [hp.2] at hb
  rwa [abs_sub_comm]

end
