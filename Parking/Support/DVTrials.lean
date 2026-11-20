import Parking.Support.DVHitting
import LatticeProb.Walk.Markov
import LatticeProb.Walk.Range

/-!
# Trials in porous boxes

Cut time into blocks of length `ℓ`.  In the block `[kℓ, (k+1)ℓ)` the trial time `τ_k` is the
first time at which the walk stands in a box of side `m` of which fewer than `(1 - δ) m^d`
sites have been visited (a porous box), or `(k+1)ℓ` if there is none (`trialTime`).  It is a
stopping time.  The trial is present if `τ_k < (k+1)ℓ`, and it succeeds if during the next
`ℓ` steps the walk visits a site of that box not visited before `τ_k`.

Two deterministic facts link the trials to the range and to the time spent in porous boxes:

- trials whose indices differ by at least `2` look at disjoint stretches of time, so the
  successful ones among `k = π, π + 2, …` produce distinct new sites, at most `|R_t|` of them
  (`card_success_le`);
- a time `j < t` at which the walk stands in a box that is porous at the end, at time `t`,
  makes the trial of its block present (`present_of_endPorous`).
-/

noncomputable section

namespace Parking

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- The sites visited at times `0, …, j`. -/
def rangeSet (X : ℕ → Site d) (j : ℕ) : Finset (Site d) :=
  (Finset.range (j + 1)).image X

theorem rangeSet_mono (X : ℕ → Site d) {i j : ℕ} (hij : i ≤ j) :
    rangeSet X i ⊆ rangeSet X j :=
  Finset.image_subset_image (Finset.range_subset_range.mpr (by omega))

theorem mem_rangeSet {X : ℕ → Site d} {j : ℕ} {x : Site d} :
    x ∈ rangeSet X j ↔ ∃ i ≤ j, X i = x := by
  simp only [rangeSet, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩

theorem rangeSet_congr {X Y : ℕ → Site d} {j : ℕ} (h : ∀ i ≤ j, X i = Y i) :
    rangeSet X j = rangeSet Y j := by
  unfold rangeSet
  exact Finset.image_congr fun i hi => h i (by simp at hi; omega)

theorem card_rangeSet (X : ℕ → Site d) (t : ℕ) :
    (rangeSet X t).card = LatticeProb.rangeCard X t := rfl

/-- The box of `x` is porous for the visited set `R`: fewer than `(1 - δ) m^d` of its sites
are in `R`. -/
def PorousFor (m : ℕ) [NeZero m] (δ : ℝ) (R : Finset (Site d)) (x : Site d) : Prop :=
  ((boxCell m (fullSplit m x).1 ∩ R).card : ℝ) < (1 - δ) * (m : ℝ) ^ d

/-- At time `j` the walk stands in a box porous for its range up to `j`. -/
def Porous (m : ℕ) [NeZero m] (δ : ℝ) (X : ℕ → Site d) (j : ℕ) : Prop :=
  PorousFor m δ (rangeSet X j) (X j)

theorem porous_congr {m : ℕ} [NeZero m] {δ : ℝ} {X Y : ℕ → Site d} {j : ℕ}
    (h : ∀ i ≤ j, X i = Y i) : Porous m δ X j ↔ Porous m δ Y j := by
  unfold Porous
  rw [rangeSet_congr h, h j le_rfl]

theorem PorousFor.anti {m : ℕ} [NeZero m] {δ : ℝ} {R R' : Finset (Site d)} (hR : R ⊆ R')
    {x : Site d} (h : PorousFor m δ R' x) : PorousFor m δ R x := by
  unfold PorousFor at h ⊢
  refine lt_of_le_of_lt ?_ h
  exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_left hR)

/-- A porous box has more than `δ m^d` unvisited sites. -/
theorem card_sdiff_gt_of_porousFor {m : ℕ} [NeZero m] {δ : ℝ} {R : Finset (Site d)}
    {x : Site d} (h : PorousFor m δ R x) :
    δ * (m : ℝ) ^ d < ((boxCell m (fullSplit m x).1 \ R).card : ℝ) := by
  classical
  unfold PorousFor at h
  have hc := Finset.card_sdiff_add_card_inter (boxCell m (fullSplit m x).1) R
  rw [card_boxCell] at hc
  have hc' : ((boxCell m (fullSplit m x).1 \ R).card : ℝ)
      + ((boxCell m (fullSplit m x).1 ∩ R).card : ℝ) = (m : ℝ) ^ d := by
    exact_mod_cast hc
  linarith

/-! ### The trial times -/

theorem trialTime_exists (m : ℕ) [NeZero m] (δ : ℝ) (ℓ k : ℕ) (X : ℕ → Site d) :
    ∃ j, k * ℓ ≤ j ∧ (Porous m δ X j ∨ j = (k + 1) * ℓ) :=
  ⟨(k + 1) * ℓ, Nat.mul_le_mul_right ℓ (Nat.le_succ k), Or.inr rfl⟩

/-- The first time in the block `[kℓ, (k+1)ℓ)` at which the walk stands in a porous box, or
`(k+1)ℓ`. -/
def trialTime (m : ℕ) [NeZero m] (δ : ℝ) (ℓ k : ℕ) (X : ℕ → Site d) : ℕ := by
  classical
  exact Nat.find (trialTime_exists m δ ℓ k X)

section TrialTime

variable {m : ℕ} [NeZero m] {δ : ℝ} {ℓ k : ℕ}

theorem trialTime_spec (X : ℕ → Site d) :
    k * ℓ ≤ trialTime m δ ℓ k X ∧
      (Porous m δ X (trialTime m δ ℓ k X) ∨ trialTime m δ ℓ k X = (k + 1) * ℓ) := by
  classical
  unfold trialTime
  convert Nat.find_spec (trialTime_exists m δ ℓ k X)

theorem trialTime_le (X : ℕ → Site d) : trialTime m δ ℓ k X ≤ (k + 1) * ℓ := by
  classical
  unfold trialTime
  convert Nat.find_min' (trialTime_exists m δ ℓ k X)
    ⟨Nat.mul_le_mul_right ℓ (Nat.le_succ k), Or.inr rfl⟩

theorem not_porous_of_lt_trialTime (X : ℕ → Site d) {j : ℕ} (hj1 : k * ℓ ≤ j)
    (hj2 : j < trialTime m δ ℓ k X) : ¬ Porous m δ X j := by
  classical
  intro hp
  have : trialTime m δ ℓ k X ≤ j := by
    unfold trialTime
    convert Nat.find_min' (trialTime_exists m δ ℓ k X) ⟨hj1, Or.inl hp⟩
  omega

theorem porous_trialTime (X : ℕ → Site d) (h : trialTime m δ ℓ k X < (k + 1) * ℓ) :
    Porous m δ X (trialTime m δ ℓ k X) := by
  rcases (trialTime_spec (m := m) (δ := δ) (ℓ := ℓ) (k := k) X).2 with hp | he
  · exact hp
  · omega

/-- The trial times are stopping times. -/
theorem isWalkStopping_trialTime : IsWalkStopping (trialTime (d := d) m δ ℓ k) := by
  classical
  intro j X Y hXY hX
  have hP : ∀ i ≤ j, (k * ℓ ≤ i ∧ (Porous m δ X i ∨ i = (k + 1) * ℓ)) ↔
      (k * ℓ ≤ i ∧ (Porous m δ Y i ∨ i = (k + 1) * ℓ)) := by
    intro i hi
    rw [porous_congr fun a ha => hXY a (le_trans ha hi)]
  unfold trialTime at hX ⊢
  rw [Nat.find_eq_iff] at hX ⊢
  refine ⟨(hP j le_rfl).mp hX.1, fun i hi hPi => hX.2 i hi ((hP i hi.le).mpr hPi)⟩

theorem trialTime_congr {X Y : ℕ → Site d} (h : ∀ i ≤ (k + 1) * ℓ, X i = Y i) :
    trialTime m δ ℓ k X = trialTime m δ ℓ k Y :=
  (isWalkStopping_trialTime _ X Y (fun i hi => h i (le_trans hi (trialTime_le X))) rfl).symm

end TrialTime

/-- The trial of block `k` is present. -/
def Present (m : ℕ) [NeZero m] (δ : ℝ) (ℓ k : ℕ) (X : ℕ → Site d) : Prop :=
  trialTime m δ ℓ k X < (k + 1) * ℓ

/-- The trial of block `k` succeeds: it is present and within `ℓ` steps the walk visits a site
of its box not visited before the trial time. -/
def Success (m : ℕ) [NeZero m] (δ : ℝ) (ℓ k : ℕ) (X : ℕ → Site d) : Prop :=
  Present m δ ℓ k X ∧ ∃ a, 1 ≤ a ∧ a ≤ ℓ ∧
    X (trialTime m δ ℓ k X + a) ∈ boxCell m (fullSplit m (X (trialTime m δ ℓ k X))).1
      \ rangeSet X (trialTime m δ ℓ k X)

/-- The sites first visited during the window of the trial. -/
def newSites (m : ℕ) [NeZero m] (δ : ℝ) (ℓ k : ℕ) (X : ℕ → Site d) : Finset (Site d) :=
  rangeSet X (trialTime m δ ℓ k X + ℓ) \ rangeSet X (trialTime m δ ℓ k X)

theorem newSites_nonempty {m : ℕ} [NeZero m] {δ : ℝ} {ℓ k : ℕ} {X : ℕ → Site d}
    (h : Success m δ ℓ k X) : (newSites m δ ℓ k X).Nonempty := by
  obtain ⟨-, a, ha1, ha2, hmem⟩ := h
  refine ⟨X (trialTime m δ ℓ k X + a), Finset.mem_sdiff.mpr ⟨?_, (Finset.mem_sdiff.mp hmem).2⟩⟩
  exact mem_rangeSet.mpr ⟨_, by omega, rfl⟩

open scoped Classical in
/-- **Successes produce distinct new sites.**  Among the trials `k = π + 2i`, `i < J`, whose
windows end by time `t`, the successful ones are at most `|R_t|`. -/
theorem card_success_le (m : ℕ) [NeZero m] (δ : ℝ) {ℓ : ℕ} (π J t : ℕ)
    (ht : (π + 2 * J) * ℓ ≤ t) (X : ℕ → Site d) :
    ((Finset.range J).filter fun i => Success m δ ℓ (π + 2 * i) X).card
      ≤ (rangeSet X t).card := by
  classical
  set S := (Finset.range J).filter fun i => Success m δ ℓ (π + 2 * i) X
  have hdisj : (S : Set ℕ).PairwiseDisjoint fun i => newSites m δ ℓ (π + 2 * i) X := by
    intro i hi i' hi' hne
    rw [Function.onFun, Finset.disjoint_left]
    -- the later window starts after the earlier one ends
    have key : ∀ a b : ℕ, a < b → a ∈ S → ∀ x, x ∈ newSites m δ ℓ (π + 2 * a) X →
        x ∉ newSites m δ ℓ (π + 2 * b) X := by
      intro a b hab ha x hxa hxb
      have hpres := (Finset.mem_filter.mp ha).2.1
      have hτa : trialTime m δ ℓ (π + 2 * a) X < (π + 2 * a + 1) * ℓ := hpres
      have hτb := (trialTime_spec (m := m) (δ := δ) (ℓ := ℓ) (k := π + 2 * b) X).1
      have hle : trialTime m δ ℓ (π + 2 * a) X + ℓ ≤ trialTime m δ ℓ (π + 2 * b) X := by
        have : (π + 2 * a + 1) * ℓ + ℓ ≤ (π + 2 * b) * ℓ := by nlinarith
        omega
      have h1 := (Finset.mem_sdiff.mp hxa).1
      have h2 := (Finset.mem_sdiff.mp hxb).2
      exact h2 (rangeSet_mono X hle h1)
    intro x hx hx'
    rcases lt_or_gt_of_ne hne with h | h
    · exact key i i' h hi x hx hx'
    · exact key i' i h hi' x hx' hx
  have hsub : S.biUnion (fun i => newSites m δ ℓ (π + 2 * i) X) ⊆ rangeSet X t := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
    have hiJ : i < J := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hτ := trialTime_le (m := m) (δ := δ) (ℓ := ℓ) (k := π + 2 * i) X
    refine rangeSet_mono X ?_ (Finset.mem_sdiff.mp hx).1
    have : (π + 2 * i + 1) * ℓ + ℓ ≤ (π + 2 * J) * ℓ := by nlinarith
    omega
  calc S.card = ∑ _i ∈ S, 1 := by rw [Finset.card_eq_sum_ones]
    _ ≤ ∑ i ∈ S, (newSites m δ ℓ (π + 2 * i) X).card := Finset.sum_le_sum fun i hi =>
        Finset.card_pos.mpr (newSites_nonempty (Finset.mem_filter.mp hi).2)
    _ = (S.biUnion fun i => newSites m δ ℓ (π + 2 * i) X).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (rangeSet X t).card := Finset.card_le_card hsub

/-- The box of `X_j` is porous for the range at the end. -/
def EndPorous (m : ℕ) [NeZero m] (δ : ℝ) (X : ℕ → Site d) (t j : ℕ) : Prop :=
  PorousFor m δ (rangeSet X t) (X j)

/-- **A time in an end-porous box makes its block's trial present.** -/
theorem present_of_endPorous {m : ℕ} [NeZero m] {δ : ℝ} {ℓ k t : ℕ} {X : ℕ → Site d}
    {j : ℕ} (hj1 : k * ℓ ≤ j) (hj2 : j < (k + 1) * ℓ) (hjt : j ≤ t)
    (h : EndPorous m δ X t j) : Present m δ ℓ k X := by
  have hp : Porous m δ X j := h.anti (rangeSet_mono X hjt)
  by_contra hnot
  have hle := trialTime_le (m := m) (δ := δ) (ℓ := ℓ) (k := k) X
  have heq : trialTime m δ ℓ k X = (k + 1) * ℓ := by
    unfold Present at hnot; omega
  exact not_porous_of_lt_trialTime X hj1 (by omega) hp

end Parking

end
