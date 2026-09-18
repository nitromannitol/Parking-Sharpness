/-
The common instruction tables in counts: the minimum number of departures is
shared, the maximum number of entries is read, and physical arrivals correspond
bijectively to arriving table entries. Settling preserves the signed count.
-/
import Parking.Support.Matched

noncomputable section

open MeasureTheory LatticeProb

variable {d : ℕ}

/-- Exactly the minimum count of instructions at a site is shared. -/
theorem Parking.card_common_matchSlots (η η' : Site d → ℤ)
    (ρ ρ' : Label d × ℕ → ℝ) (S S' : State d) (t : ℕ) (x : Site d) :
    (((Parking.matchActive η S t x).image (Parking.matchSlot η ρ S t)) ∩
      ((Parking.matchActive η' S' t x).image (Parking.matchSlot η' ρ' S' t))).card =
      min (Parking.matchActive η S t x).card (Parking.matchActive η' S' t x).card := by
  classical
  have hf : Function.Injective (fun j : ℕ => (Sum.inl (x, j) : Parking.RoundSlot d)) :=
    fun _ _ h => congrArg Prod.snd (Sum.inl_injective h)
  rw [Parking.image_matchSlot, Parking.image_matchSlot, ← Finset.image_inter _ _ hf,
    Finset.range_inter_range, Finset.card_image_of_injective _ hf, Finset.card_range]

/-- Together the two processes read the maximum count of distinct instructions. -/
theorem Parking.card_union_matchSlots (η η' : Site d → ℤ)
    (ρ ρ' : Label d × ℕ → ℝ) (S S' : State d) (t : ℕ) (x : Site d) :
    (((Parking.matchActive η S t x).image (Parking.matchSlot η ρ S t)) ∪
      ((Parking.matchActive η' S' t x).image (Parking.matchSlot η' ρ' S' t))).card =
      max (Parking.matchActive η S t x).card (Parking.matchActive η' S' t x).card := by
  classical
  have hf : Function.Injective (fun j : ℕ => (Sum.inl (x, j) : Parking.RoundSlot d)) :=
    fun _ _ h => congrArg Prod.snd (Sum.inl_injective h)
  rw [Parking.image_matchSlot, Parking.image_matchSlot, ← Finset.image_union,
    Finset.range_union_range, Finset.card_image_of_injective _ hf, Finset.card_range]

/-- The active count in the common-table construction. -/
def Parking.matchedCount (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) (x : Site d) : ℕ :=
  (Parking.matchActive η (Parking.matchedState η ρ σ t) t x).card

/-- The arrivals at a site in one round of the common-table construction. -/
def Parking.matchedArrivals (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) (x : Site d) : Finset (Label d) :=
  Parking.pArrivalsAt ⟨η, Parking.matchedMoves η ρ σ, ρ⟩
    (Parking.matchedState η ρ σ t) t x

theorem Parking.matchedCount_zero (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (x : Site d) :
    Parking.matchedCount η ρ σ 0 x = (η x).toNat := by
  classical
  unfold Parking.matchedCount Parking.matchActive
  rw [Parking.matchedState, Parking.candidates_zero]
  rw [Finset.filter_map, Finset.card_map,
    Finset.filter_true_of_mem (fun i hi =>
      ⟨by simpa [initial] using Finset.mem_range.mp hi, rfl⟩), Finset.card_range]

theorem Parking.mem_matchActive_iff (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) (x : Site d) (p : Label d) :
    p ∈ Parking.matchActive η (Parking.matchedState η ρ σ t) t x ↔
      (Parking.matchedState η ρ σ t).active p = true ∧
      (Parking.matchedState η ρ σ t).pos p = x := by
  simpa only [Parking.pState_matchedMoves, Parking.pActiveAt, Parking.matchActive] using
    Parking.mem_pActiveAt_iff ⟨η, Parking.matchedMoves η ρ σ, ρ⟩ t x p

theorem Parking.matchedCount_succ (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) (x : Site d) :
    Parking.matchedCount η ρ σ (t + 1) x =
      (Parking.matchedArrivals η ρ σ t x).card - (Parking.matchedState η ρ σ t).holes x := by
  simpa only [Parking.pActiveCount, Parking.pHoleCount, Parking.pState_matchedMoves,
    Parking.matchedCount, Parking.matchedArrivals, Parking.pActiveAt, Parking.matchActive] using
    Parking.pActiveCount_succ (Parking.labelOrder d) ⟨η, Parking.matchedMoves η ρ σ, ρ⟩ t x

theorem Parking.matchedHoles_succ (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) (x : Site d) :
    (Parking.matchedState η ρ σ (t + 1)).holes x =
      (Parking.matchedState η ρ σ t).holes x - (Parking.matchedArrivals η ρ σ t x).card := by
  simpa only [Parking.pHoleCount, Parking.pState_matchedMoves, Parking.matchedArrivals] using
    Parking.pHoleCount_succ ⟨η, Parking.matchedMoves η ρ σ, ρ⟩ t x

/-- Settling cancels one particle against one hole and preserves the signed count. -/
theorem Parking.matchedSigned_succ (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) (x : Site d) :
    (Parking.matchedCount η ρ σ (t + 1) x : ℤ) -
        ((Parking.matchedState η ρ σ (t + 1)).holes x : ℤ) =
      ((Parking.matchedArrivals η ρ σ t x).card : ℤ) -
        ((Parking.matchedState η ρ σ t).holes x : ℤ) := by
  rw [Parking.matchedCount_succ, Parking.matchedHoles_succ]
  omega

/-- A marginal cannot have both a moving particle and an unfilled hole at one site. -/
theorem Parking.matchedCount_eq_zero_or_holes_eq_zero (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ) (x : Site d) :
    Parking.matchedCount η ρ σ t x = 0 ∨ (Parking.matchedState η ρ σ t).holes x = 0 := by
  cases t with
  | zero =>
      rw [Parking.matchedCount_zero]
      change (η x).toNat = 0 ∨ (-η x).toNat = 0
      omega
  | succ t =>
      rw [Parking.matchedCount_succ, Parking.matchedHoles_succ]
      omega

/-- All unmatched particles and holes at one site have the same sign. -/
theorem Parking.abs_signed_difference_eq (a h b k : ℕ)
    (hah : a = 0 ∨ h = 0) (hbk : b = 0 ∨ k = 0) :
    |((a : ℤ) - h) - ((b : ℤ) - k)| = |(a : ℤ) - b| + |(h : ℤ) - k| := by
  rcases hah with rfl | rfl <;> rcases hbk with rfl | rfl
  · calc
      |((0 : ℤ) - h) - ((0 : ℤ) - k)| = |(k : ℤ) - h| :=
        congrArg abs (by ring)
      _ = |(0 : ℤ) - 0| + |(h : ℤ) - k| := by simpa using (abs_sub_comm (k : ℤ) h)
  · simp only [Nat.cast_zero, zero_sub, sub_zero, abs_neg, Int.abs_natCast]
    rw [show -(h : ℤ) - b = -((b : ℤ) + h) by ring, abs_neg,
      abs_of_nonneg (by positivity)]
  · simp only [Nat.cast_zero, zero_sub, sub_zero, sub_neg_eq_add, abs_neg, Int.abs_natCast]
    exact abs_of_nonneg (by positivity)
  · simp

/-- Matched physical particles receive exactly the same direction. -/
theorem Parking.matchedMoves_eq_of_rank_eq (η η' : Site d → ℤ)
    (ρ ρ' : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ) (x : Site d)
    {p q : Label d}
    (hp : p ∈ Parking.matchActive η (Parking.matchedState η ρ σ t) t x)
    (hq : q ∈ Parking.matchActive η' (Parking.matchedState η' ρ' σ t) t x)
    (hr : rankIn (Parking.matchActive η (Parking.matchedState η ρ σ t) t x)
        (Parking.matchKey ρ t) p =
      rankIn (Parking.matchActive η' (Parking.matchedState η' ρ' σ t) t x)
        (Parking.matchKey ρ' t) q) :
    Parking.matchedMoves η ρ σ (p, t) = Parking.matchedMoves η' ρ' σ (q, t) := by
  unfold Parking.matchedMoves
  rw [Parking.matchSlot_of_mem η ρ _ t x hp, Parking.matchSlot_of_mem η' ρ' _ t x hq, hr]


/-- The entries whose particles arrive at `x` in this round. -/
def Parking.arrivalSlots (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) (x : Site d) : Finset (Parking.RoundSlot d) :=
  (nbrFinset x).biUnion fun y =>
    ((Finset.range (Parking.matchedCount η ρ σ t y)).filter fun j =>
      y + Parking.stepVec (σ t (Sum.inl (y, j))) = x).image fun j => Sum.inl (y, j)

theorem Parking.mem_matchedArrivals_iff (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) (x : Site d) (p : Label d) :
    p ∈ Parking.matchedArrivals η ρ σ t x ↔
      (Parking.matchedState η ρ σ t).active p = true ∧
      (Parking.matchedState η ρ σ t).pos p +
        Parking.stepVec (Parking.matchedMoves η ρ σ (p, t)) = x := by
  have h := Parking.mem_pArrivalsAt_iff ⟨η, Parking.matchedMoves η ρ σ, ρ⟩ t x p
  simp only [Parking.pState_matchedMoves] at h
  unfold Parking.matchedArrivals
  rw [h]
  constructor
  · rintro ⟨ha, hp⟩
    exact ⟨ha, by simpa [Parking.pNextPos, ha] using hp⟩
  · rintro ⟨ha, hp⟩
    exact ⟨ha, by simpa [Parking.pNextPos, ha] using hp⟩

theorem Parking.mem_nbrFinset_add_stepVec (y : Site d) (b : Fin d × Bool) :
    y + Parking.stepVec b ∈ nbrFinset y := by
  apply Parking.mem_nbrFinset_iff.mpr
  refine ⟨b.1, ?_⟩
  cases hb : b.2
  · exact Or.inr (by simp [Parking.stepVec, hb, sub_eq_add_neg])
  · exact Or.inl (by simp [Parking.stepVec, hb])

/-- The physical arrivals correspond bijectively to the arriving table entries. -/
theorem Parking.image_matchSlot_matchedArrivals (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ) (x : Site d) :
    (Parking.matchedArrivals η ρ σ t x).image
        (Parking.matchSlot η ρ (Parking.matchedState η ρ σ t) t) =
      Parking.arrivalSlots η ρ σ t x := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have hp' := (Parking.mem_matchedArrivals_iff η ρ σ t x p).mp hp
    let S := Parking.matchedState η ρ σ t
    let y := S.pos p
    let j := rankIn (Parking.matchActive η S t y) (Parking.matchKey ρ t) p
    have ha : p ∈ Parking.matchActive η S t y :=
      (Parking.mem_matchActive_iff η ρ σ t y p).mpr ⟨hp'.1, rfl⟩
    have hslot := Parking.matchSlot_of_mem η ρ S t y ha
    have hmove : Parking.matchedMoves η ρ σ (p, t) = σ t (Sum.inl (y, j)) := by
      exact congrArg (σ t) hslot
    have hdir : y + Parking.stepVec (σ t (Sum.inl (y, j))) = x := by
      rw [← hmove]
      exact hp'.2
    apply Finset.mem_biUnion.mpr
    refine ⟨y, ?_, Finset.mem_image.mpr ⟨j, ?_, hslot.symm⟩⟩
    · rw [← hdir]
      exact Parking.nbrFinset_symm (Parking.mem_nbrFinset_add_stepVec y _)
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (rankIn_lt_card ha), hdir⟩
  · intro hq
    obtain ⟨y, hy, hq⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hj, hdir⟩ := Finset.mem_filter.mp hj
    have hslot : (Sum.inl (y, j) : Parking.RoundSlot d) ∈
        (Parking.matchActive η (Parking.matchedState η ρ σ t) t y).image
          (Parking.matchSlot η ρ (Parking.matchedState η ρ σ t) t) := by
      rw [Parking.image_matchSlot]
      exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
    obtain ⟨p, hp, hslot⟩ := Finset.mem_image.mp hslot
    refine Finset.mem_image.mpr ⟨p, ?_, hslot⟩
    apply (Parking.mem_matchedArrivals_iff η ρ σ t x p).mpr
    have hp' := (Parking.mem_matchActive_iff η ρ σ t y p).mp hp
    refine ⟨hp'.1, ?_⟩
    rw [hp'.2, Parking.matchedMoves, hslot]
    exact hdir

theorem Parking.card_matchedArrivals (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) (x : Site d) :
    (Parking.matchedArrivals η ρ σ t x).card = (Parking.arrivalSlots η ρ σ t x).card := by
  rw [← Parking.image_matchSlot_matchedArrivals,
    Finset.card_image_of_injective _ (Parking.matchSlot_injective η ρ _ t)]

end
