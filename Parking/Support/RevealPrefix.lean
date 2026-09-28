import Parking.Support.ProductDoob

/-!
# Revealed prefixes of a blocked enumeration

For an injective family `e : Fin K ↪ ι`, `revealPrefix e n` is the set of coordinates
of `ι` hit by the first `n` entries of `e`, and `blockReveal e n` extends this to a
doubly-indexed enumeration that runs through complete blocks of size `K` and then a
partial prefix of the current block. This file proves both are monotone in `n`, empty
at `n = 0`, and that the next coordinate enumerated at step `n` is always fresh: it lies
outside everything `blockReveal e n` has already revealed, and adding it recovers
exactly `blockReveal e (n + 1)`.
-/

noncomputable section
namespace Parking
variable {ι : Type*} {K : ℕ}

/-- The coordinates revealed by the first n entries of a finite list without repetition. -/
def revealPrefix (e : Fin K ↪ ι) (n : ℕ) : Set ι := {q | ∃ i : Fin K, i.val < n ∧ e i = q}

/-- Membership in `revealPrefix e n` is decidable, since it unfolds to a decidable
existential over the finite type `Fin K`. -/
instance [DecidableEq ι] (e : Fin K ↪ ι) (n : ℕ) :
    DecidablePred (· ∈ revealPrefix e n) := fun q =>
  inferInstanceAs (Decidable (∃ i : Fin K, i.val < n ∧ e i = q))

/-- `revealPrefix e` is monotone in `n`: a coordinate revealed within the first `m`
entries is still revealed after enlarging the bound to any `n ≥ m`. -/
theorem revealPrefix_mono (e : Fin K ↪ ι) : Monotone (revealPrefix e) := by
  intro m n hmn q hq
  obtain ⟨i, hi, rfl⟩ := hq
  exact ⟨i, hi.trans_le hmn, rfl⟩

/-- No coordinate is revealed by an empty prefix. -/
theorem revealPrefix_zero (e : Fin K ↪ ι) : revealPrefix e 0 = ∅ := by
  ext q
  simp [revealPrefix]

/-- The full prefix of length `K` reveals exactly the range of `e`. -/
theorem revealPrefix_full (e : Fin K ↪ ι) : revealPrefix e K = Set.range e := by
  ext q
  constructor
  · rintro ⟨i, _hi, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩

/-- Extending the prefix by one entry, past index `j`, adds exactly `e j` to what
was already revealed by the prefix up to `j`. -/
theorem revealPrefix_succ (e : Fin K ↪ ι) (j : Fin K) :
    revealPrefix e (j.val + 1) = insert (e j) (revealPrefix e j.val) := by
  ext q
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases hij : i = j
    · subst i; exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨i, by
        have : i.val ≠ j.val := fun h => hij (Fin.ext h)
        omega, rfl⟩
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨j, by omega, rfl⟩
    · exact ⟨i, by omega, rfl⟩

/-- The entry `e j` is not among the coordinates revealed by the prefix strictly
before index `j`, since `e` is injective. -/
theorem notMem_revealPrefix (e : Fin K ↪ ι) (j : Fin K) : e j ∉ revealPrefix e j.val := by
  rintro ⟨i, hi, he⟩
  have h := e.injective he
  subst i
  omega

/-- All earlier blocks and the current finite prefix have been revealed after n steps. -/
def blockReveal (e : Fin K ↪ ι) (n : ℕ) : Set (ℕ × ι) :=
  {q | q.1 < n / K ∨ q.1 = n / K ∧ q.2 ∈ revealPrefix e (n % K)}

/-- Membership in `blockReveal e n` is decidable, since it unfolds to a decidable
disjunction built from the decidability of `revealPrefix`. -/
instance [DecidableEq ι] (e : Fin K ↪ ι) (n : ℕ) :
    DecidablePred (· ∈ blockReveal e n) := fun q =>
  inferInstanceAs (Decidable (q.1 < n / K ∨ q.1 = n / K ∧ q.2 ∈ revealPrefix e (n % K)))

/-- `blockReveal e` is monotone in `n`: comparing the quotients and remainders of `m`
and `n` by `K` and applying `revealPrefix_mono` within the shared block. -/
theorem blockReveal_mono (e : Fin K ↪ ι) : Monotone (blockReveal e) := by
  intro m n hmn q hq
  have hdiv := Nat.div_le_div_right (c := K) hmn
  rcases hq with hq | ⟨ht, hp⟩
  · exact Or.inl (hq.trans_le hdiv)
  · by_cases he : m / K = n / K
    · right
      refine ⟨ht.trans he, ?_⟩
      have hm := Nat.mod_add_div m K
      have hn := Nat.mod_add_div n K
      rw [he] at hm
      apply revealPrefix_mono e (show m % K ≤ n % K by omega) hp
    · exact Or.inl (by omega)

/-- No block is revealed before any enumeration steps. -/
theorem blockReveal_zero (e : Fin K ↪ ι) : blockReveal e 0 = ∅ := by
  ext q
  simp [blockReveal, revealPrefix_zero]

/-- The next enumerated coordinate is fresh. -/
theorem notMem_blockReveal_next (e : Fin K ↪ ι) (hK : 0 < K) (n : ℕ) :
    (n / K, e ⟨n % K, Nat.mod_lt n hK⟩) ∉ blockReveal e n := by
  intro h
  rcases h with h | ⟨_ht, hp⟩
  · omega
  · exact notMem_revealPrefix e ⟨n % K, Nat.mod_lt n hK⟩ hp

/-- The next coordinate and every previously revealed one are measurable after the next step. -/
theorem insert_next_subset_blockReveal (e : Fin K ↪ ι) (hK : 0 < K) (n : ℕ) :
    insert (n / K, e ⟨n % K, Nat.mod_lt n hK⟩) (blockReveal e n) ⊆ blockReveal e (n + 1) := by
  intro q hq
  rcases hq with rfl | hq
  · have hdiv := Nat.div_le_div_right (c := K) (show n ≤ n + 1 by omega)
    by_cases he : n / K = (n + 1) / K
    · right
      refine ⟨he, ⟨⟨n % K, Nat.mod_lt n hK⟩, ?_, rfl⟩⟩
      dsimp
      have hm := Nat.mod_add_div n K
      have hn := Nat.mod_add_div (n + 1) K
      rw [he] at hm
      omega
    · left
      omega
  · exact blockReveal_mono e (by omega) hq
end Parking
