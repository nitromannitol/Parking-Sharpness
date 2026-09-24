/-
The exploration of `lem:w-martingale` reads only what it has revealed.

`LatticeProb.ReadsOnlyRevealed` is the hypothesis the library's conditional
exploration lemma needs: two realizations on which the exploration has taken the
same steps and found the same instructions there read the same instruction next.
It implies the `pred` field of `LatticeProb.IsExploration` and, with the values
read through an injective map, it makes the index measurable for the
sigma-algebra of the values already revealed.

The content is the mixed locality of the odometer.  `Parking.state_congr` says
that the state after `t` rounds reads only the instructions the odometer has
reached; `LatticeProb.state_agree_box` says that the state in a box reads only
the instructions near it.  Neither alone suffices here: two realizations with the
same revealed prefix differ at infinitely many coordinates at once, and the ones
they differ at are those the odometer has not reached, wherever they lie.  The
two are joined by the hybrid driver that follows the first realization at every
instruction the odometer has reached and the second at all the rest: it has the
same state as the first because `state_congr` reads only what the odometer has
reached, and it agrees with the second throughout the box.
-/
import Parking.Support.WExploration
import LatticeProb.Prob.ExplorationCond

noncomputable section

open MeasureTheory

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### The mixed locality of the odometer -/

/-- **The odometers of two rounds inside a box read only the instructions that
are both inside the box and below the odometer.**  This is the mixed form of
`Parking.U_agree_of_agree_box`, whose hypothesis is spatial, and
`Parking.state_congr_of_le_odometer`, whose hypothesis is on the index. -/
theorem U_agree_of_revealed {ω ω' : Data d} (hs : StepsToNeighbour (toDriver ω))
    (hs' : StepsToNeighbour (toDriver ω')) (heta : ω.1 = ω'.1) (hrank : ω.2.2 = ω'.2.2)
    (R t : ℕ)
    (hstack : ∀ q : Site d × ℕ, q.1 ∈ boxFinset (0 : Site d) (R + t + 2 * t * t) →
      q.2 < U ω t q.1 → ω.2.1 q = ω'.2.1 q)
    (y : Site d) (hy : y ∈ boxFinset (0 : Site d) R) :
    U ω t y = U ω' t y ∧ U ω (t + 1) y = U ω' (t + 1) y := by
  classical
  set τ : Site d × ℕ → Site d :=
    fun q => if q.2 < U ω t q.1 then ω.2.1 q else ω'.2.1 q with hτ
  set ω'' : Data d := ((ω.1, τ, ω.2.2) : Data d) with hω''
  have hstep : StepsToNeighbour (toDriver ω'') := by
    intro q i
    show |τ q i - q.1 i| ≤ 1
    by_cases h : q.2 < U ω t q.1
    · rw [hτ]; simp only [h, if_true]; exact hs q i
    · rw [hτ]; simp only [h, if_false]; exact hs' q i
  have hstate : LatticeProb.state (toDriver ω) t = LatticeProb.state (toDriver ω'') t := by
    refine state_congr (D := toDriver ω) (D' := toDriver ω'') hs rfl rfl t fun z i hi => ?_
    show ω.2.1 (z, i) = τ (z, i)
    rw [hτ]
    exact (if_pos (show i < U ω t z from hi)).symm
  have hU2 : U ω t y = U ω'' t y := by
    show (LatticeProb.state (toDriver ω) t).departures y
      = (LatticeProb.state (toDriver ω'') t).departures y
    rw [hstate]
  have hU2s : U ω (t + 1) y = U ω'' (t + 1) y :=
    U_succ_of_state_eq (D := toDriver ω) (D' := toDriver ω'') rfl t hstate y
  have hbox : ∀ q : Site d × ℕ, q.1 ∈ boxFinset (0 : Site d) (R + t + 2 * t * t) →
      ω''.2.1 q = ω'.2.1 q := by
    intro q hq
    show τ q = ω'.2.1 q
    rw [hτ]
    by_cases h : q.2 < U ω t q.1
    · simp only [h, if_true]; exact hstack q hq h
    · simp only [h, if_false]
  obtain ⟨h1, h2⟩ :=
    U_agree_of_agree_box (ω := ω'') (ω' := ω') hstep heta hrank R t hbox y hy
  exact ⟨hU2.trans h1, hU2s.trans h2⟩


/-- **The block of a round is decided by the instructions the odometer of the
round before has reached near its box.** -/
theorem blockAt_agree_of_revealed {ω ω' : Data d} (hs : StepsToNeighbour (toDriver ω))
    (hs' : StepsToNeighbour (toDriver ω')) (heta : ω.1 = ω'.1) (hrank : ω.2.2 = ω'.2.2)
    (n s : ℕ) (hs1 : 1 ≤ s)
    (hstack : ∀ q : Site d × ℕ,
      q.1 ∈ boxFinset (0 : Site d) (blockRad n s + 2 * s * s) →
        q.2 < U ω (s - 1) q.1 → ω.2.1 q = ω'.2.1 q) :
    blockAt ω (blockRad n s) s = blockAt ω' (blockRad n s) s := by
  refine blockAt_eq_of_U_eq fun y hy => ?_
  have hrad : blockRad n s + (s - 1) + 2 * (s - 1) * (s - 1)
      ≤ blockRad n s + 2 * s * s := by
    have h1 : (s - 1) + 2 * (s - 1) * (s - 1) ≤ 2 * s * s := by
      obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      nlinarith
    omega
  have hst : ∀ q : Site d × ℕ,
      q.1 ∈ boxFinset (0 : Site d) (blockRad n s + (s - 1) + 2 * (s - 1) * (s - 1)) →
        q.2 < U ω (s - 1) q.1 → ω.2.1 q = ω'.2.1 q :=
    fun q hq => hstack q (boxFinset_mono hrad hq)
  obtain ⟨h1, h2⟩ :=
    U_agree_of_revealed hs hs' heta hrank (blockRad n s) (s - 1) hst y hy
  rw [Nat.sub_add_cancel hs1] at h2
  exact ⟨h1, h2⟩

/-- **The blocks up to round `k` are decided by the instructions of the blocks
before them**, simultaneously: two realizations that agree at every instruction
of every earlier block have the same blocks. -/
theorem blockAt_agree_of_blocks {ω ω' : Data d} (hs : StepsToNeighbour (toDriver ω))
    (hs' : StepsToNeighbour (toDriver ω')) (heta : ω.1 = ω'.1) (hrank : ω.2.2 = ω'.2.2)
    (n k : ℕ) (hkn : k ≤ n)
    (hread : ∀ r, 1 ≤ r → r < k → ∀ q ∈ blockAt ω (blockRad n r) r, ω.2.1 q = ω'.2.1 q) :
    ∀ s, 1 ≤ s → s ≤ k → blockAt ω (blockRad n s) s = blockAt ω' (blockRad n s) s := by
  intro s h1s hsk
  refine blockAt_agree_of_revealed hs hs' heta hrank n s h1s ?_
  intro q hq hlt
  have hex : ∃ r, q.2 < U ω r q.1 := ⟨s - 1, hlt⟩
  set r := Nat.find hex with hr
  have hrspec : q.2 < U ω r q.1 := Nat.find_spec hex
  have hrle : r ≤ s - 1 := Nat.find_min' hex hlt
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exfalso
      have h0 : U ω 0 q.1 = 0 := rfl
      rw [h, h0] at hrspec
      omega
    · exact h
  have hprev : U ω (r - 1) q.1 ≤ q.2 := by
    by_contra hc
    exact Nat.find_min hex (m := r - 1) (by omega) (Nat.lt_of_not_le hc)
  have hbox : q.1 ∈ boxFinset (0 : Site d) (blockRad n r) := by
    refine boxFinset_mono ?_ hq
    calc blockRad n s + 2 * s * s ≤ blockRad n (s - 1) := blockRad_step h1s (by omega)
      _ ≤ blockRad n r := blockRad_antitone hrle
  exact hread r hr1 (by omega) q (mem_blockAt.mpr ⟨hbox, hprev, hrspec⟩)

/-! ### The exploration reads only what it has revealed -/

/-- **The blocks of the rounds the exploration has finished are decided by the
instructions it has read.**  Two stacks that give the exploration the same first
`m` steps and the same instructions there give the same block at every round
whose predecessors are exhausted within those `m` steps. -/
theorem blockAt_agree_of_readsPrefix (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (n m : ℕ) {σ σ' : Site d × ℕ → Site d}
    (hread : ∀ k, k < m → explIdx i₀ η ρ n k σ = explIdx i₀ η ρ n k σ' ∧
      σ (explIdx i₀ η ρ n k σ) = σ' (explIdx i₀ η ρ n k σ)) :
    ∀ k, k ≤ n - 1 →
      (blockPrefix ((η, nbrProj i₀ σ, ρ) : Data d) n (k - 1)).length ≤ m →
      ∀ s, 1 ≤ s → s ≤ k →
        blockAt ((η, nbrProj i₀ σ, ρ) : Data d) (blockRad n s) s
          = blockAt ((η, nbrProj i₀ σ', ρ) : Data d) (blockRad n s) s := by
  classical
  set ω : Data d := ((η, nbrProj i₀ σ, ρ) : Data d) with hω
  set ω' : Data d := ((η, nbrProj i₀ σ', ρ) : Data d) with hω'
  have hs : StepsToNeighbour (toDriver ω) :=
    stepsToNeighbour_of_mem fun q => nbrProj_mem i₀ σ q
  have hs' : StepsToNeighbour (toDriver ω') :=
    stepsToNeighbour_of_mem fun q => nbrProj_mem i₀ σ' q
  have hagree : ∀ k, k < m →
      ω.2.1 (explIdx i₀ η ρ n k σ) = ω'.2.1 (explIdx i₀ η ρ n k σ) := by
    intro k hk
    obtain ⟨-, hval⟩ := hread k hk
    show nbrProj i₀ σ (explIdx i₀ η ρ n k σ) = nbrProj i₀ σ' (explIdx i₀ η ρ n k σ)
    simp only [nbrProj, hval]
  intro k hk hlen
  refine blockAt_agree_of_blocks hs hs' rfl rfl n k (by omega) ?_
  intro r hr1 hrk q hq
  have hqmem : q ∈ blockPrefix ω n (k - 1) :=
    mem_blockPrefix.mpr ⟨r, hr1, by omega, hq⟩
  obtain ⟨j, hj, hval⟩ :=
    exists_explIdx_of_mem_blockPrefix (i₀ := i₀) (η := η) (ρ := ρ) (n := n) (σ := σ)
      (k := k - 1) (i := m) (by omega) hlen hqmem
  rw [← hval]
  exact hagree j hj


/-- **`Parking.explIdx` reads only what it has revealed.** -/
theorem readsOnlyRevealed_explIdx (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (n : ℕ) : LatticeProb.ReadsOnlyRevealed (explIdx i₀ η ρ n) := by
  classical
  intro m σ σ' hread
  set ω : Data d := ((η, nbrProj i₀ σ, ρ) : Data d) with hω
  set ω' : Data d := ((η, nbrProj i₀ σ', ρ) : Data d) with hω'
  have hblocks : ∀ k, k ≤ n - 1 → (blockPrefix ω n (k - 1)).length ≤ m →
      ∀ s, 1 ≤ s → s ≤ k → blockAt ω (blockRad n s) s = blockAt ω' (blockRad n s) s :=
    blockAt_agree_of_readsPrefix i₀ η ρ n m hread
  by_cases hi : m < (blockPrefix ω n (n - 1)).length
  · have hex : ∃ k, m < (blockPrefix ω n k).length := ⟨n - 1, hi⟩
    set K := Nat.find hex with hK
    have hKlt : m < (blockPrefix ω n K).length := Nat.find_spec hex
    have hKle : K ≤ n - 1 := Nat.find_min' hex hi
    have hK1 : 1 ≤ K := by
      rcases Nat.eq_zero_or_pos K with h | h
      · exfalso
        rw [h] at hKlt
        simp [blockPrefix] at hKlt
      · exact h
    have hKmin : (blockPrefix ω n (K - 1)).length ≤ m := by
      by_contra hc
      exact Nat.find_min hex (m := K - 1) (by omega) (Nat.lt_of_not_le hc)
    have heq : blockPrefix ω n K = blockPrefix ω' n K :=
      blockPrefix_congr (hblocks K hKle hKmin)
    have hKlt' : m < (blockPrefix ω' n K).length := by rw [← heq]; exact hKlt
    rw [explIdx, explIdx, blockPrefix_append ω n hKle, blockPrefix_append ω' n hKle,
      List.getD_append _ _ _ _ hKlt, List.getD_append _ _ _ _ hKlt', heq]
  · have hlen : (blockPrefix ω n (n - 1)).length ≤ m := Nat.le_of_not_lt hi
    have hlen' : (blockPrefix ω n ((n - 1) - 1)).length ≤ m :=
      le_trans (length_blockPrefix_mono ω n (by omega)) hlen
    have heq : blockPrefix ω n (n - 1) = blockPrefix ω' n (n - 1) :=
      blockPrefix_congr (hblocks (n - 1) le_rfl hlen')
    rw [explIdx, explIdx, heq]

end Parking

end
