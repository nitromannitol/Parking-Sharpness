/-
The discrepancy labels equal the signed difference of the coupled physical
processes. Rank assignment covers exactly the surplus departure slots; the
incoming labels are surplus arrivals together with waiting labels. Opposite
cancellation preserves the signed count, and only one sign remains at a site.
-/
import Parking.Support.DiscrepancyLabels

noncomputable section

open LatticeProb

variable {d : ℕ}

/-- Positive and negative labels partition the live labels at a site. -/
theorem Parking.card_discrepancyAtSign_add (c : Site d → ℤ × ℤ) (S : State d) (t : ℕ) (x : Site d) :
    (Parking.discrepancyAtSign c S t x true).card + (Parking.discrepancyAtSign c S t x false).card =
      (Parking.discrepancyAt c S t x).card := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Parking.discrepancyAt c S t x) (p := fun p => Parking.discrepancySign c p = true)
  simpa only [Bool.not_eq_true, Parking.discrepancyAtSign] using h

/-- The signed count of labels is preserved by cancellation. -/
theorem Parking.discrepancySigned_step (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (a b : Site d → ℕ) (τ : Parking.RoundSlot d → Fin d × Bool) (S : State d) (t : ℕ) (x : Site d) :
    ((Parking.discrepancyAtSign c (Parking.discrepancyStep c ρ a b τ S t) (t + 1) x true).card : ℤ) -
      (Parking.discrepancyAtSign c (Parking.discrepancyStep c ρ a b τ S t) (t + 1) x false).card =
    ((Parking.discrepancyArrivalsSign c ρ a b τ S t x true).card : ℤ) -
      (Parking.discrepancyArrivalsSign c ρ a b τ S t x false).card := by
  rw [Parking.card_discrepancyAtSign_step, Parking.card_discrepancyAtSign_step]
  simp only [Bool.not_true, Bool.not_false]
  omega

theorem Parking.discrepancyAt_zero (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (x : Site d) :
    Parking.discrepancyAt c (Parking.discrepancyState c ρ σ 0) 0 x =
      (Finset.range (Parking.discrepancyConf c x).toNat).map
        ⟨(fun i => (x, i)), by intro i j h; exact congrArg Prod.snd h⟩ := by
  classical
  unfold Parking.discrepancyAt Parking.matchActive
  rw [Parking.discrepancyState, Parking.candidates_zero, Finset.filter_map]
  congr 1
  exact Finset.filter_true_of_mem fun i hi =>
    ⟨by simpa [initial] using Finset.mem_range.mp hi, rfl⟩

theorem Parking.card_discrepancyAtSign_zero (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (x : Site d) (sgn : Bool) :
    (Parking.discrepancyAtSign c (Parking.discrepancyState c ρ σ 0) 0 x sgn).card =
      if Parking.discrepancySign c (x, 0) = sgn then (Parking.discrepancyConf c x).toNat else 0 := by
  classical
  unfold Parking.discrepancyAtSign
  rw [Parking.discrepancyAt_zero, Finset.filter_map, Finset.card_map]
  change ((Finset.range (Parking.discrepancyConf c x).toNat).filter
    (fun _ => decide (0 < (c x).2 - (c x).1) = sgn)).card =
    if decide (0 < (c x).2 - (c x).1) = sgn then (Parking.discrepancyConf c x).toNat else 0
  by_cases h : decide (0 < (c x).2 - (c x).1) = sgn
  · simp only [h, Finset.filter_true, Finset.card_range, if_true]
  · simp only [h, Finset.filter_false, Finset.card_empty, if_false]

theorem Parking.card_discrepancyPositive_zero (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (x : Site d) :
    (Parking.discrepancyAtSign c (Parking.discrepancyState c ρ σ 0) 0 x true).card =
      ((c x).2 - (c x).1).toNat := by
  rw [Parking.card_discrepancyAtSign_zero]
  unfold Parking.discrepancySign Parking.discrepancyConf
  by_cases h : 0 < (c x).2 - (c x).1
  · simp only [h, decide_true, if_true, abs_of_pos h]
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    exact (Int.toNat_eq_zero.mpr (by omega : (c x).2 - (c x).1 ≤ 0)).symm

theorem Parking.card_discrepancyNegative_zero (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (x : Site d) :
    (Parking.discrepancyAtSign c (Parking.discrepancyState c ρ σ 0) 0 x false).card =
      ((c x).1 - (c x).2).toNat := by
  rw [Parking.card_discrepancyAtSign_zero]
  unfold Parking.discrepancySign Parking.discrepancyConf
  by_cases h : 0 < (c x).2 - (c x).1
  · simp only [h, decide_true, Bool.true_eq_false, if_false]
    exact (Int.toNat_eq_zero.mpr (by omega : (c x).1 - (c x).2 ≤ 0)).symm
  · simp only [h, decide_false, if_true]
    rw [abs_of_nonpos (by omega : (c x).2 - (c x).1 ≤ 0), neg_sub]

/-- At every time, the label process has at most one sign at each site. -/
theorem Parking.discrepancyAtSign_empty_or_empty (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ) (x : Site d) :
    Parking.discrepancyAtSign c (Parking.discrepancyState c ρ σ t) t x true = ∅ ∨
      Parking.discrepancyAtSign c (Parking.discrepancyState c ρ σ t) t x false = ∅ := by
  cases t with
  | zero =>
      rw [← Finset.card_eq_zero, ← Finset.card_eq_zero,
        Parking.card_discrepancyPositive_zero, Parking.card_discrepancyNegative_zero]
      omega
  | succ t => exact Parking.discrepancyAtSign_step_empty_or_empty c ρ _ _ _ _ t x

/-- The invariant identifying the labels with the signed difference of the
physical processes. -/
def Parking.DiscrepancyBalance (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) : Prop :=
  ∀ x : Site d,
    ((Parking.discrepancyAtSign c (Parking.discrepancyState c ρ σ t) t x true).card : ℤ) -
        (Parking.discrepancyAtSign c (Parking.discrepancyState c ρ σ t) t x false).card =
      ((Parking.matchedCount (Parking.coupledConf true c) ρ σ t x : ℤ) -
        ((Parking.matchedState (Parking.coupledConf true c) ρ σ t).holes x : ℤ)) -
      ((Parking.matchedCount (Parking.coupledConf false c) ρ σ t x : ℤ) -
        ((Parking.matchedState (Parking.coupledConf false c) ρ σ t).holes x : ℤ))

theorem Parking.discrepancyBalance_zero (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) : Parking.DiscrepancyBalance c ρ σ 0 := by
  intro x
  rw [Parking.card_discrepancyPositive_zero, Parking.card_discrepancyNegative_zero,
    Parking.matchedCount_zero, Parking.matchedCount_zero]
  change (((c x).2 - (c x).1).toNat : ℤ) - ((c x).1 - (c x).2).toNat =
    ((c x).2.toNat : ℤ) - (-(c x).2).toNat - (((c x).1.toNat : ℤ) - (-(c x).1).toNat)
  omega

/-- The live labels are bounded by the four physical populations as soon as
signed-count balance is known. -/
theorem Parking.card_discrepancyAt_le_four (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) (hbal : Parking.DiscrepancyBalance c ρ σ t) (x : Site d) :
    (Parking.discrepancyAt c (Parking.discrepancyState c ρ σ t) t x).card ≤
      Parking.matchedCount (Parking.coupledConf true c) ρ σ t x +
      (Parking.matchedState (Parking.coupledConf true c) ρ σ t).holes x +
      Parking.matchedCount (Parking.coupledConf false c) ρ σ t x +
      (Parking.matchedState (Parking.coupledConf false c) ρ σ t).holes x := by
  have hb := hbal x
  have hcard := Parking.card_discrepancyAtSign_add c (Parking.discrepancyState c ρ σ t) t x
  rcases Parking.discrepancyAtSign_empty_or_empty c ρ σ t x with hp | hn
  · rw [hp, Finset.card_empty] at hb hcard
    omega
  · rw [hn, Finset.card_empty] at hb hcard
    omega

/-- Balance and exclusion ensure enough labels to cover every surplus departure. -/
theorem Parking.discrepancyMoveCount_le_card (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ)
    (hbal : Parking.DiscrepancyBalance c ρ σ t) (x : Site d) :
    Parking.discrepancyMoveCount
      (Parking.matchedCount (Parking.coupledConf false c) ρ σ t)
      (Parking.matchedCount (Parking.coupledConf true c) ρ σ t) x ≤
      (Parking.discrepancyAt c (Parking.discrepancyState c ρ σ t) t x).card := by
  have hb := hbal x
  have hcard := Parking.card_discrepancyAtSign_add c (Parking.discrepancyState c ρ σ t) t x
  have h0 := Parking.matchedCount_eq_zero_or_holes_eq_zero (Parking.coupledConf false c) ρ σ t x
  have h1 := Parking.matchedCount_eq_zero_or_holes_eq_zero (Parking.coupledConf true c) ρ σ t x
  unfold Parking.discrepancyMoveCount
  omega

/-- The labels at a site have the sign of every nonzero surplus of active
particles there. -/
theorem Parking.discrepancySign_of_surplus (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ)
    (hbal : Parking.DiscrepancyBalance c ρ σ t) (x : Site d) (sgn : Bool)
    (hsur : Parking.matchedCount (Parking.coupledConf (!sgn) c) ρ σ t x <
      Parking.matchedCount (Parking.coupledConf sgn c) ρ σ t x)
    {p : Label d} (hp : p ∈ Parking.discrepancyAt c (Parking.discrepancyState c ρ σ t) t x) :
    Parking.discrepancySign c p = sgn := by
  have hb := hbal x
  have h0 := Parking.matchedCount_eq_zero_or_holes_eq_zero (Parking.coupledConf false c) ρ σ t x
  have h1 := Parking.matchedCount_eq_zero_or_holes_eq_zero (Parking.coupledConf true c) ρ σ t x
  have hnone := Parking.discrepancyAtSign_empty_or_empty c ρ σ t x
  rw [← Finset.card_eq_zero, ← Finset.card_eq_zero] at hnone
  by_contra hsign
  have hopp : Parking.discrepancySign c p = !sgn := by
    cases sgn <;> cases hh : Parking.discrepancySign c p <;> simp_all
  have hpos : 0 < (Parking.discrepancyAtSign c (Parking.discrepancyState c ρ σ t) t x (!sgn)).card :=
    Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hopp⟩⟩
  cases sgn <;> simp only [Bool.not_false, Bool.not_true] at hsur hpos <;> omega

/-- A moving label has the sign of the marginal whose surplus table entries
it uses. -/
theorem Parking.surplus_of_discrepancyMoving (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ)
    (hbal : Parking.DiscrepancyBalance c ρ σ t) (x : Site d) (sgn : Bool)
    {p : Label d} (hp : p ∈ Parking.discrepancyAt c (Parking.discrepancyState c ρ σ t) t x)
    (hsgn : Parking.discrepancySign c p = sgn)
    (hmov : Parking.discrepancyMoving c ρ
      (Parking.matchedCount (Parking.coupledConf false c) ρ σ t)
      (Parking.matchedCount (Parking.coupledConf true c) ρ σ t)
      (Parking.discrepancyState c ρ σ t) t p) :
    Parking.matchedCount (Parking.coupledConf (!sgn) c) ρ σ t x <
      Parking.matchedCount (Parking.coupledConf sgn c) ρ σ t x := by
  have hpos : (Parking.discrepancyState c ρ σ t).pos p = x := (Finset.mem_filter.mp hp).2.2
  have hK := hmov.2
  rw [hpos] at hK
  unfold Parking.discrepancyMoveCount at hK
  have hne : Parking.matchedCount (Parking.coupledConf false c) ρ σ t x ≠
      Parking.matchedCount (Parking.coupledConf true c) ρ σ t x := by omega
  by_contra hsur
  have hrev : Parking.matchedCount (Parking.coupledConf sgn c) ρ σ t x <
      Parking.matchedCount (Parking.coupledConf (!sgn) c) ρ σ t x := by
    cases sgn <;> simp only [Bool.not_true, Bool.not_false] at hsur ⊢ <;> omega
  have hop := Parking.discrepancySign_of_surplus c ρ σ t hbal x (!sgn)
    (by simpa using hrev) hp
  rw [hsgn] at hop
  cases sgn <;> simp at hop

/-- The rank prefix is exactly the corresponding initial segment of integers. -/
theorem Parking.image_rankPrefix {α β : Type*} [DecidableEq α] [LinearOrder β]
    (A : Finset α) (f : α → β) (hf : Set.InjOn f A) (k : ℕ) (hk : k ≤ A.card) :
    (A.filter fun p => rankIn A f p < k).image (rankIn A f) = Finset.range k := by
  have he := Finset.filter_image (s := A) (f := rankIn A f) (p := fun j => j < k)
  rw [← he, image_rankIn hf]
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

section
attribute [local instance] Classical.propDecidable
variable (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ)
local notation "S" => Parking.discrepancyState c ρ σ t
local notation "a₀" => Parking.matchedCount (Parking.coupledConf false c) ρ σ t
local notation "a₁" => Parking.matchedCount (Parking.coupledConf true c) ρ σ t
local notation "Moves" => Parking.discrepancyMoving c ρ a₀ a₁ S t
local notation "Slot" => Parking.discrepancySlot c ρ a₀ a₁ S t
local notation "Next" => Parking.discrepancyNextPos c ρ a₀ a₁ (σ t) S t

/-- The label departures of a given sign. -/
def Parking.discrepancyLeaving (x : Site d) (sgn : Bool) : Finset (Label d) := by
  classical
  exact (Parking.discrepancyAtSign c S t x sgn).filter Moves

/-- The label arrivals of a given sign, before cancellation. -/
def Parking.discrepancyIncoming (x : Site d) (sgn : Bool) : Finset (Label d) :=
  Parking.discrepancyArrivalsSign c ρ a₀ a₁ (σ t) S t x sgn

/-- Candidate truncation loses no incoming label. -/
theorem Parking.mem_discrepancyIncoming_iff (x : Site d) (sgn : Bool) (p : Label d) :
    p ∈ Parking.discrepancyIncoming c ρ σ t x sgn ↔
      (S).active p = true ∧ Next p = x ∧ Parking.discrepancySign c p = sgn := by
  classical
  unfold Parking.discrepancyIncoming Parking.discrepancyArrivalsSign Parking.discrepancyArrivals
  simp only [Finset.mem_filter]
  refine ⟨fun hp => ⟨hp.1.2.1, hp.1.2.2, hp.2⟩, fun hp => ⟨⟨?_, hp.1, hp.2.1⟩, hp.2.2⟩⟩
  have hidx : p.2 < (Parking.discrepancyConf c p.1).toNat := by
    simpa [Parking.discrepancyState, initial] using
      Parking.discrepancyState_active_le c ρ σ p t hp.1
  apply mem_candidates _ hidx
  intro i
  have hb := Parking.abs_discrepancyPos_sub_start_le c ρ σ (t + 1) p i
  change |Next p i - p.1 i| ≤ _ at hb
  rw [hp.2.1] at hb
  rwa [abs_sub_comm]

/-- Precisely the surplus active particles depart with labels of their sign. -/
theorem Parking.card_discrepancyLeaving (hbal : Parking.DiscrepancyBalance c ρ σ t)
    (x : Site d) (sgn : Bool) :
    (Parking.discrepancyLeaving c ρ σ t x sgn).card =
      Parking.matchedCount (Parking.coupledConf sgn c) ρ σ t x -
        Parking.matchedCount (Parking.coupledConf (!sgn) c) ρ σ t x := by
  classical
  by_cases hsur : Parking.matchedCount (Parking.coupledConf (!sgn) c) ρ σ t x <
      Parking.matchedCount (Parking.coupledConf sgn c) ρ σ t x
  · have heq : Parking.discrepancyLeaving c ρ σ t x sgn =
        (Parking.discrepancyAt c S t x).filter fun p =>
          rankIn (Parking.discrepancyAt c S t x) (Parking.matchKey ρ 0) p <
            Parking.discrepancyMoveCount a₀ a₁ x := by
      ext p
      simp only [Parking.discrepancyLeaving, Parking.discrepancyAtSign, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hp, _⟩, hm⟩
        have hpos := (Parking.mem_discrepancyAt_iff c ρ σ t x p).mp hp
        exact ⟨hp, by simpa only [hpos.2] using hm.2⟩
      · rintro ⟨hp, hr⟩
        have hpos := (Parking.mem_discrepancyAt_iff c ρ σ t x p).mp hp
        refine ⟨⟨hp, Parking.discrepancySign_of_surplus c ρ σ t hbal x sgn hsur hp⟩, ?_⟩
        unfold Parking.discrepancyMoving
        simpa only [hpos.2] using And.intro hp hr
    have hc := card_filter_rank_lt (Parking.discrepancyAt c S t x) (Parking.matchKey ρ 0)
      (Parking.matchKey_injective ρ 0).injOn (Parking.discrepancyMoveCount a₀ a₁ x)
    change ((Parking.discrepancyAt c S t x).filter (fun p =>
      rankIn (Parking.discrepancyAt c S t x) (Parking.matchKey ρ 0) p <
        Parking.discrepancyMoveCount a₀ a₁ x)).card = _ at hc
    rw [heq, hc, min_eq_right (Parking.discrepancyMoveCount_le_card c ρ σ t hbal x)]
    unfold Parking.discrepancyMoveCount
    cases sgn <;> simp only [Bool.not_false, Bool.not_true] at hsur ⊢ <;> omega
  · have he : Parking.discrepancyLeaving c ρ σ t x sgn = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hp, hm⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp, hs⟩ := Finset.mem_filter.mp hp
      exact hsur (Parking.surplus_of_discrepancyMoving c ρ σ t hbal x sgn hp hs hm)
    rw [he, Finset.card_empty, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hsur)]

/-- Entries of the physical arrival table, with the irrelevant neighbor
condition eliminated. -/
theorem Parking.mem_arrivalSlots_iff (η : Site d → ℤ) (x y : Site d) (j : ℕ) :
    (Sum.inl (y, j) : Parking.RoundSlot d) ∈ Parking.arrivalSlots η ρ σ t x ↔
      j < Parking.matchedCount η ρ σ t y ∧
        y + Parking.stepVec (σ t (Sum.inl (y, j))) = x := by
  classical
  constructor
  · intro hp
    obtain ⟨z, _, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hp
    have he' : (z, k) = (y, j) := Sum.inl_injective he
    cases he'
    simpa only [Finset.mem_filter, Finset.mem_range] using hk
  · rintro ⟨hj, hd⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨y, ?_, Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hj, hd⟩, rfl⟩⟩
    rw [← hd]
    exact Parking.nbrFinset_symm (Parking.mem_nbrFinset_add_stepVec y _)

/-- Each moving label uses an entry in the surplus interval of its sign. -/
theorem Parking.discrepancySlot_surplus (hbal : Parking.DiscrepancyBalance c ρ σ t)
    (x : Site d) (sgn : Bool) {p : Label d}
    (hp : p ∈ Parking.discrepancyAt c S t x) (hs : Parking.discrepancySign c p = sgn)
    (hm : Moves p) :
    ∃ j, Slot p = Sum.inl (x, j) ∧
      j < Parking.matchedCount (Parking.coupledConf sgn c) ρ σ t x ∧
      Parking.matchedCount (Parking.coupledConf (!sgn) c) ρ σ t x ≤ j := by
  classical
  have hpos := ((Parking.mem_discrepancyAt_iff c ρ σ t x p).mp hp).2
  have hsur := Parking.surplus_of_discrepancyMoving c ρ σ t hbal x sgn hp hs hm
  have hr := hm.2
  rw [hpos] at hr
  refine ⟨min (a₀ x) (a₁ x) + rankIn (Parking.discrepancyAt c S t x)
    (Parking.matchKey ρ 0) p, ?_, ?_⟩
  · simp only [Parking.discrepancySlot, if_pos hm, hpos]
  · unfold Parking.discrepancyMoveCount at hr
    cases sgn <;> simp only [Bool.not_false, Bool.not_true] at hsur ⊢ <;> omega

/-- Every surplus entry carries exactly one moving label. -/
theorem Parking.exists_discrepancyLabel_at_slot (hbal : Parking.DiscrepancyBalance c ρ σ t)
    (x : Site d) (sgn : Bool) (j : ℕ)
    (hj : j < Parking.matchedCount (Parking.coupledConf sgn c) ρ σ t x)
    (ho : Parking.matchedCount (Parking.coupledConf (!sgn) c) ρ σ t x ≤ j) :
    ∃ p ∈ Parking.discrepancyAt c S t x,
      Parking.discrepancySign c p = sgn ∧ Moves p ∧ Slot p = Sum.inl (x, j) := by
  classical
  let n := Parking.matchedCount (Parking.coupledConf (!sgn) c) ρ σ t x
  have hsur : n < Parking.matchedCount (Parking.coupledConf sgn c) ρ σ t x := lt_of_le_of_lt ho hj
  have hmin : min (a₀ x) (a₁ x) = n := by
    dsimp [n]
    cases sgn <;> simp only [Bool.not_false, Bool.not_true] at hj ho ⊢ <;> omega
  have hk : j - n < Parking.discrepancyMoveCount a₀ a₁ x := by
    dsimp [n, Parking.discrepancyMoveCount]
    cases sgn <;> simp only [Bool.not_false, Bool.not_true] at hj ho ⊢ <;> omega
  have hcard : j - n < (Parking.discrepancyAt c S t x).card :=
    lt_of_lt_of_le hk (Parking.discrepancyMoveCount_le_card c ρ σ t hbal x)
  have him : j - n ∈ (Parking.discrepancyAt c S t x).image
      (rankIn (Parking.discrepancyAt c S t x) (Parking.matchKey ρ 0)) := by
    rw [image_rankIn (Parking.matchKey_injective ρ 0).injOn]
    exact Finset.mem_range.mpr hcard
  obtain ⟨p, hp, hr⟩ := Finset.mem_image.mp him
  have hpos := ((Parking.mem_discrepancyAt_iff c ρ σ t x p).mp hp).2
  have hm : Moves p := by
    unfold Parking.discrepancyMoving
    rw [hpos, hr]
    exact ⟨hp, hk⟩
  refine ⟨p, hp, Parking.discrepancySign_of_surplus c ρ σ t hbal x sgn hsur hp, hm, ?_⟩
  simp only [Parking.discrepancySlot, if_pos hm, hpos, hmin, hr]
  congr 2
  omega

/-- Moving label arrivals are in bijection with the surplus physical arrivals. -/
theorem Parking.image_discrepancyIncoming_moving
    (hbal : Parking.DiscrepancyBalance c ρ σ t) (x : Site d) (sgn : Bool) :
    ((Parking.discrepancyIncoming c ρ σ t x sgn).filter Moves).image Slot =
      Parking.arrivalSlots (Parking.coupledConf sgn c) ρ σ t x \
        Parking.arrivalSlots (Parking.coupledConf (!sgn) c) ρ σ t x := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hp, hm⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hn, hs⟩ := (Parking.mem_discrepancyIncoming_iff c ρ σ t x sgn p).mp hp
    have hpAt := (Parking.mem_discrepancyAt_iff c ρ σ t ((S).pos p) p).mpr ⟨ha, rfl⟩
    obtain ⟨j, he, hj, ho⟩ := Parking.discrepancySlot_surplus c ρ σ t hbal ((S).pos p) sgn hpAt hs hm
    have hd : (S).pos p + Parking.stepVec (σ t (Sum.inl ((S).pos p, j))) = x := by
      simpa only [Parking.discrepancyNextPos, if_pos hm, he] using hn
    rw [he, Finset.mem_sdiff, Parking.mem_arrivalSlots_iff, Parking.mem_arrivalSlots_iff]
    exact ⟨⟨hj, hd⟩, fun hh => (Nat.not_lt_of_ge ho) hh.1⟩
  · intro hq
    obtain ⟨hq, hno⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨y, _, hq⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hj, hd⟩ := Finset.mem_filter.mp hj
    have ho : Parking.matchedCount (Parking.coupledConf (!sgn) c) ρ σ t y ≤ j := by
      by_contra hn
      exact hno ((Parking.mem_arrivalSlots_iff ρ σ t _ x y j).mpr
        ⟨Nat.lt_of_not_ge hn, hd⟩)
    obtain ⟨p, hp, hs, hm, he⟩ := Parking.exists_discrepancyLabel_at_slot c ρ σ t hbal y sgn j
      (Finset.mem_range.mp hj) ho
    have hp' := (Parking.mem_discrepancyAt_iff c ρ σ t y p).mp hp
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_filter.mpr ⟨?_, hm⟩, he⟩
    apply (Parking.mem_discrepancyIncoming_iff c ρ σ t x sgn p).mpr
    refine ⟨hp'.1, ?_, hs⟩
    simpa only [Parking.discrepancyNextPos, if_pos hm, he, hp'.2] using hd

/-- Waiting labels remain at their current site. -/
theorem Parking.discrepancyIncoming_waiting (x : Site d) (sgn : Bool) :
    (Parking.discrepancyIncoming c ρ σ t x sgn).filter (fun p => ¬ Moves p) =
      Parking.discrepancyAtSign c S t x sgn \ Parking.discrepancyLeaving c ρ σ t x sgn := by
  classical
  ext p
  simp only [Finset.mem_filter, Parking.mem_discrepancyIncoming_iff, Finset.mem_sdiff,
    Parking.discrepancyLeaving, Parking.discrepancyAtSign, Finset.mem_filter,
    Parking.mem_discrepancyAt_iff]
  by_cases hm : Moves p
  · simp only [hm]
    tauto
  · simp only [hm, Parking.discrepancyNextPos]
    tauto

/-- Label arrivals consist of surplus physical arrivals and labels that wait. -/
theorem Parking.card_discrepancyIncoming (hbal : Parking.DiscrepancyBalance c ρ σ t)
    (x : Site d) (sgn : Bool) :
    ((Parking.discrepancyIncoming c ρ σ t x sgn).card : ℤ) =
      ((Parking.arrivalSlots (Parking.coupledConf sgn c) ρ σ t x \
        Parking.arrivalSlots (Parking.coupledConf (!sgn) c) ρ σ t x).card : ℤ) +
      (Parking.discrepancyAtSign c S t x sgn).card -
      (Parking.discrepancyLeaving c ρ σ t x sgn).card := by
  classical
  have hpart := Finset.card_filter_add_card_filter_not
    (s := Parking.discrepancyIncoming c ρ σ t x sgn) (p := Moves)
  have hm : ((Parking.discrepancyIncoming c ρ σ t x sgn).filter Moves).card =
      (Parking.arrivalSlots (Parking.coupledConf sgn c) ρ σ t x \
        Parking.arrivalSlots (Parking.coupledConf (!sgn) c) ρ σ t x).card := by
    rw [← Parking.image_discrepancyIncoming_moving c ρ σ t hbal x sgn]
    exact (Finset.card_image_of_injective _
      (Parking.discrepancySlot_injective c ρ a₀ a₁ S t)).symm
  have hw : ((Parking.discrepancyIncoming c ρ σ t x sgn).filter (fun p => ¬ Moves p)).card +
      (Parking.discrepancyLeaving c ρ σ t x sgn).card =
      (Parking.discrepancyAtSign c S t x sgn).card := by
    rw [Parking.discrepancyIncoming_waiting]
    exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  omega

/-- The signed count invariant is preserved by a round of coupled motion and
cancellation. -/
theorem Parking.discrepancyBalance_succ (hbal : Parking.DiscrepancyBalance c ρ σ t) :
    Parking.DiscrepancyBalance c ρ σ (t + 1) := by
  intro x
  have hb := hbal x
  have hp := Parking.card_discrepancyIncoming c ρ σ t hbal x true
  have hn := Parking.card_discrepancyIncoming c ρ σ t hbal x false
  rw [Parking.card_discrepancyLeaving c ρ σ t hbal] at hp hn
  simp only [Bool.not_true, Bool.not_false] at hp hn
  have hi₁ := Finset.card_sdiff_add_card_inter
    (Parking.arrivalSlots (Parking.coupledConf true c) ρ σ t x)
    (Parking.arrivalSlots (Parking.coupledConf false c) ρ σ t x)
  have hi₀ := Finset.card_sdiff_add_card_inter
    (Parking.arrivalSlots (Parking.coupledConf false c) ρ σ t x)
    (Parking.arrivalSlots (Parking.coupledConf true c) ρ σ t x)
  rw [Finset.inter_comm] at hi₀
  rw [Parking.discrepancyState, Parking.discrepancySigned_step,
    Parking.matchedSigned_succ, Parking.matchedSigned_succ,
    Parking.card_matchedArrivals, Parking.card_matchedArrivals]
  change ((Parking.discrepancyIncoming c ρ σ t x true).card : ℤ) -
    (Parking.discrepancyIncoming c ρ σ t x false).card = _
  omega

end

/-- The live signed labels equal the signed physical discrepancy at every site
and every time. -/
theorem Parking.discrepancyBalance (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) : Parking.DiscrepancyBalance c ρ σ t := by
  induction t with
  | zero => exact Parking.discrepancyBalance_zero c ρ σ
  | succ t ih => exact Parking.discrepancyBalance_succ c ρ σ t ih

/-- Live discrepancy labels at a site are bounded by the four physical
particle and hole populations. -/
theorem Parking.discrepancyCount_le_four (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) (x : Site d) :
    (Parking.discrepancyAt c (Parking.discrepancyState c ρ σ t) t x).card ≤
      Parking.matchedCount (Parking.coupledConf true c) ρ σ t x +
      (Parking.matchedState (Parking.coupledConf true c) ρ σ t).holes x +
      Parking.matchedCount (Parking.coupledConf false c) ρ σ t x +
      (Parking.matchedState (Parking.coupledConf false c) ρ σ t).holes x :=
  Parking.card_discrepancyAt_le_four c ρ σ t (Parking.discrepancyBalance c ρ σ t) x

end
