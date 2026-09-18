/-
Translation covariance of persistent discrepancy labels. Their creation,
priority ranks, motion, waiting and ranked cancellation all commute
with translation, jointly with the two physical processes.
-/
import Parking.Support.MatchedShift
import Parking.Support.DiscrepancyLabels

noncomputable section

open LatticeProb

variable {d : ℕ} {v : Site d} {S' S : State d}

/-- Translation of the finite labels present at a site. -/
theorem Parking.discrepancyAt_shift (c : Site d → ℤ × ℤ)
    (hS : Parking.ShiftState v S' S) (t : ℕ) (x : Site d) :
    (Parking.discrepancyAt (fun y => c (y + v)) S' t x).map (Parking.shiftLabelEmb v) =
      Parking.discrepancyAt c S t (x + v) :=
  Parking.matchActive_shift (Parking.discrepancyConf c) hS t x

section
variable (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
  (a' a b' b : Site d → ℕ) (ha : ∀ x, a' x = a (x + v)) (hb : ∀ x, b' x = b (x + v))
  (hS : Parking.ShiftState v S' S) (t : ℕ)
include ha hb hS
local notation "c'" => (fun y => c (y + v))
local notation "ρ'" => Parking.shiftRank v ρ

/-- The selection of the moving labels commutes with translations. -/
theorem Parking.discrepancyMoving_shift (p : Label d) :
    Parking.discrepancyMoving c' ρ' a' b' S' t p ↔
      Parking.discrepancyMoving c ρ a b S t (Parking.shiftLabel v p) := by
  have hA : (Parking.discrepancyAt c' S' t (S'.pos p)).map (Parking.shiftLabelEmb v) =
      Parking.discrepancyAt c S t (S.pos (Parking.shiftLabel v p)) := by
    simpa only [hS.pos, sub_add_cancel] using Parking.discrepancyAt_shift c hS t (S'.pos p)
  unfold Parking.discrepancyMoving
  rw [Parking.mem_finset_shift v _ _ hA p, Parking.rankIn_shift v ρ 0 _ _ hA p]
  simp only [Parking.discrepancyMoveCount, ha, hb, hS.pos, sub_add_cancel]

/-- The transferred label reads the translated surplus entry. -/
theorem Parking.discrepancySlot_shift (p : Label d) :
    Parking.shiftRoundSlot v (Parking.discrepancySlot c' ρ' a' b' S' t p) =
      Parking.discrepancySlot c ρ a b S t (Parking.shiftLabel v p) := by
  classical
  have hA : (Parking.discrepancyAt c' S' t (S'.pos p)).map (Parking.shiftLabelEmb v) =
      Parking.discrepancyAt c S t (S.pos (Parking.shiftLabel v p)) := by
    simpa only [hS.pos, sub_add_cancel] using Parking.discrepancyAt_shift c hS t (S'.pos p)
  have hm := Parking.discrepancyMoving_shift c ρ a' a b' b ha hb hS t p
  unfold Parking.discrepancySlot
  by_cases hp : Parking.discrepancyMoving c' ρ' a' b' S' t p
  · rw [if_pos hp, if_pos (hm.mp hp)]
    change Sum.inl (S'.pos p + v, _) = Sum.inl _
    rw [Parking.rankIn_shift v ρ 0 _ _ hA p, ha, hb, hS.pos, sub_add_cancel]
  · rw [if_neg hp, if_neg (fun h => hp (hm.mpr h))]
    rfl

variable (τ : Parking.RoundSlot d → Fin d × Bool)
local notation "τ'" => (fun q => τ (Parking.shiftRoundSlot v q))

/-- The moving and waiting label positions commute with translations. -/
theorem Parking.discrepancyNextPos_shift (p : Label d) :
    Parking.discrepancyNextPos c' ρ' a' b' τ' S' t p =
      Parking.discrepancyNextPos c ρ a b τ S t (Parking.shiftLabel v p) - v := by
  classical
  have hm := Parking.discrepancyMoving_shift c ρ a' a b' b ha hb hS t p
  unfold Parking.discrepancyNextPos
  by_cases hp : Parking.discrepancyMoving c' ρ' a' b' S' t p
  · rw [if_pos hp, if_pos (hm.mp hp)]
    dsimp only
    rw [Parking.discrepancySlot_shift c ρ a' a b' b ha hb hS, hS.pos]
    abel
  · rw [if_neg hp, if_neg (fun h => hp (hm.mpr h))]
    exact hS.pos p

/-- Arrival sets of each sign are translation covariant. -/
theorem Parking.discrepancyArrivalsSign_shift (x : Site d) (sgn : Bool) :
    (Parking.discrepancyArrivalsSign c' ρ' a' b' τ' S' t x sgn).map (Parking.shiftLabelEmb v) =
      Parking.discrepancyArrivalsSign c ρ a b τ S t (x + v) sgn := by
  classical
  unfold Parking.discrepancyArrivalsSign Parking.discrepancyArrivals
  rw [show Parking.discrepancyConf c' = (fun y => Parking.discrepancyConf c (y + v)) from rfl,
    ← Parking.candidates_shift (Parking.discrepancyConf c) x v (t + 1),
    Finset.filter_map, Finset.filter_map]
  congr 1
  ext p
  simp only [Finset.mem_filter, Function.comp_def, Parking.shiftLabelEmb_apply,
    hS.active, Parking.discrepancyNextPos_shift c ρ a' a b' b ha hb hS,
    sub_eq_iff_eq_add, Parking.discrepancySign, Parking.shiftLabel]
  rfl

end

/-- Ranked cancellation commutes with translation. -/
theorem Parking.rankSurvivors_shift (v : Site d) (ρ : Label d × ℕ → ℝ) (t : ℕ)
    (A' A B' B : Finset (Label d)) (hA : A'.map (Parking.shiftLabelEmb v) = A)
    (hB : B'.map (Parking.shiftLabelEmb v) = B) :
    (Parking.rankSurvivors A' B' (Parking.matchKey (Parking.shiftRank v ρ) t)).map
        (Parking.shiftLabelEmb v) = Parking.rankSurvivors A B (Parking.matchKey ρ t) := by
  classical
  have hm : ∀ p, p ∈ Parking.rankSurvivors A' B' (Parking.matchKey (Parking.shiftRank v ρ) t) ↔
      Parking.shiftLabel v p ∈ Parking.rankSurvivors A B (Parking.matchKey ρ t) := by
    intro p
    simp only [Parking.rankSurvivors, Finset.mem_filter]
    rw [Parking.mem_finset_shift v _ _ hA p, Parking.rankIn_shift v ρ t _ _ hA p,
      ← hB, Finset.card_map]
  ext p
  rw [Parking.mem_map_shiftLabel]
  simpa only [Parking.shiftLabel, sub_add_cancel, Prod.mk.eta] using hm (p.1 - v, p.2)

/-- A whole label round, including cancellation and transfer, is translation covariant. -/
theorem Parking.discrepancyStep_shift (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (a' a b' b : Site d → ℕ) (ha : ∀ x, a' x = a (x + v)) (hb : ∀ x, b' x = b (x + v))
    (hS : Parking.ShiftState v S' S) (t : ℕ) (τ : Parking.RoundSlot d → Fin d × Bool) :
    Parking.ShiftState v
      (Parking.discrepancyStep (fun y => c (y + v)) (Parking.shiftRank v ρ) a' b'
        (fun q => τ (Parking.shiftRoundSlot v q)) S' t)
      (Parking.discrepancyStep c ρ a b τ S t) where
  active p := by
    classical
    let c' := fun y => c (y + v)
    let ρ' := Parking.shiftRank v ρ
    let τ' := fun q => τ (Parking.shiftRoundSlot v q)
    let x' := Parking.discrepancyNextPos c' ρ' a' b' τ' S' t p
    let x := Parking.discrepancyNextPos c ρ a b τ S t (Parking.shiftLabel v p)
    let sgn := Parking.discrepancySign c (Parking.shiftLabel v p)
    have hx : x' + v = x := by
      dsimp [x', x, c', ρ', τ']
      rw [Parking.discrepancyNextPos_shift c ρ a' a b' b ha hb hS, sub_add_cancel]
    have hA := Parking.discrepancyArrivalsSign_shift c ρ a' a b' b ha hb hS t τ x' sgn
    have hB := Parking.discrepancyArrivalsSign_shift c ρ a' a b' b ha hb hS t τ x' (!sgn)
    rw [hx] at hA hB
    have hR := Parking.rankSurvivors_shift v ρ 0 _ _ _ _ hA hB
    simp only [Parking.discrepancyStep]
    apply decide_eq_decide.mpr
    exact Parking.mem_finset_shift v _ _ hR p
  pos p := Parking.discrepancyNextPos_shift c ρ a' a b' b ha hb hS t τ p
  holes _ := rfl
  departures _ := rfl

/-- The physical active counts commute with translation. -/
theorem Parking.matchedCount_shift (v : Site d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ) (x : Site d) :
    Parking.matchedCount (fun y => η (y + v)) (Parking.shiftRank v ρ)
      (Parking.shiftRoundNoise v σ) t x = Parking.matchedCount η ρ σ t (x + v) := by
  unfold Parking.matchedCount
  rw [← Parking.matchActive_shift η (Parking.matchedState_shift v η ρ σ t) t x, Finset.card_map]

/-- Persistent labels, including their survival and positions, commute with translations. -/
theorem Parking.discrepancyState_shift (v : Site d) (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ) :
    Parking.ShiftState v
      (Parking.discrepancyState (fun y => c (y + v)) (Parking.shiftRank v ρ)
        (Parking.shiftRoundNoise v σ) t)
      (Parking.discrepancyState c ρ σ t) := by
  induction t with
  | zero =>
      refine ⟨fun _ => rfl, fun p => ?_, fun _ => rfl, fun _ => rfl⟩
      simp only [Parking.discrepancyState, initial, Parking.shiftLabel]
      abel
  | succ t ih =>
      apply Parking.discrepancyStep_shift c ρ _ _ _ _ _ _ ih t (σ t)
      · intro x
        exact Parking.matchedCount_shift v (Parking.coupledConf false c) ρ σ t x
      · intro x
        exact Parking.matchedCount_shift v (Parking.coupledConf true c) ρ σ t x

end
