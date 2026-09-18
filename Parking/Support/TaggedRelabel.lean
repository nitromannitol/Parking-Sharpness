/-
The label order under a relabeling that fixes the index zero.

The construction breaks a tie of equal uniform variables by the label order,
which compares the sites first and the indices second.  A relabeling of the
particles at `x₀` never moves the sites, and a permutation fixing the index
`0` decides every comparison the same way except between two labels both at
`x₀` with both indices nonzero (`parking.tex:2272-2320`).

This is the combinatorial input to the argument for `thm:subcritical`: on the
event that the uniform variables are pairwise distinct, every tie of the
tagged driver involves the tagged label, whose index is `0`.
-/

import Parking.Support.RelabelEquiv

open LatticeProb Equiv

namespace Parking

variable {d : ℕ}

/-- A permutation fixing `0` sends exactly `0` to `0`. -/
theorem perm_eq_zero_iff {σ : Equiv.Perm ℕ} (hσ0 : σ 0 = 0) (n : ℕ) :
    σ n = 0 ↔ n = 0 := by
  constructor
  · intro hs
    have heq : σ n = σ 0 := by rw [hs, hσ0]
    exact σ.injective heq
  · intro h
    subst h
    exact hσ0

/-- A permutation fixing `0` is positive exactly at positive indices. -/
theorem perm_pos_iff {σ : Equiv.Perm ℕ} (hσ0 : σ 0 = 0) (n : ℕ) :
    0 < σ n ↔ 0 < n := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with hc | hc
    · rw [hc, hσ0] at h
      exact absurd h (Nat.lt_irrefl 0)
    · exact hc
  · intro h
    rcases Nat.eq_zero_or_pos (σ n) with hc | hc
    · exact absurd (perm_eq_zero_iff hσ0 n |>.mp hc) (fun hh => Nat.lt_irrefl 0 (hh ▸ h))
    · exact hc

/-- The label order is site-major: when the sites differ, the comparison is
decided by the sites, which a relabeling never moves. -/
theorem labelLT_perm_iff_of_sites_ne {x₀ : Site d} {σ : Equiv.Perm ℕ}
    {p q : Label d} (hpq : p.1 ≠ q.1) :
    labelLT (permLabel x₀ σ p) (permLabel x₀ σ q) ↔ labelLT p q := by
  have hp : (permLabel x₀ σ p).1 = p.1 := by
    unfold permLabel
    split <;> rfl
  have hq : (permLabel x₀ σ q).1 = q.1 := by
    unfold permLabel
    split <;> rfl
  rw [labelLT, labelLT, labelKey, labelKey, labelKey, labelKey,
    Prod.Lex.toLex_lt_toLex, Prod.Lex.toLex_lt_toLex, hp, hq]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact Or.inl h
    · exact absurd h hpq
  · rintro (h | ⟨h, -⟩)
    · exact Or.inl h
    · exact absurd h hpq

/-- At a common site, a comparison involving the index `0` is decided the
same way by a permutation fixing `0`. -/
theorem labelLT_perm_iff_of_index_zero {x₀ : Site d} {σ : Equiv.Perm ℕ}
    (hσ0 : σ 0 = 0) {p q : Label d} (hx : p.1 = x₀) (hpq : p.1 = q.1)
    (h0 : p.2 = 0 ∨ q.2 = 0) :
    labelLT (permLabel x₀ σ p) (permLabel x₀ σ q) ↔ labelLT p q := by
  have hp : permLabel x₀ σ p = (p.1, σ p.2) := by
    simp only [permLabel, if_pos hx]
  have hq : permLabel x₀ σ q = (q.1, σ q.2) := by
    simp only [permLabel, if_pos (hpq ▸ hx)]
  rw [hp, hq, labelLT, labelLT, labelKey, labelKey, labelKey, labelKey,
    Prod.Lex.toLex_lt_toLex, Prod.Lex.toLex_lt_toLex]
  rcases h0 with h0 | h0
  · rw [h0, hσ0, perm_pos_iff hσ0 q.2]
  · rw [h0, hσ0]
    simp only [Nat.not_lt_zero, iff_self]

/-- The label order is site-major, and a permutation of the indices at `x₀`
that fixes the index `0` decides every comparison the same way, except between
two labels both at `x₀` with both indices nonzero. -/
theorem labelLT_perm_iff_of_fixes_zero {x₀ : Site d} {σ : Equiv.Perm ℕ}
    (hσ0 : σ 0 = 0) {p q : Label d}
    (h : p.1 ≠ q.1 ∨ p.1 ≠ x₀ ∨ q.1 ≠ x₀ ∨ p.2 = 0 ∨ q.2 = 0) :
    labelLT (permLabel x₀ σ p) (permLabel x₀ σ q) ↔ labelLT p q := by
  by_cases hpq : p.1 = q.1
  · by_cases hx : p.1 = x₀
    · have h0 : p.2 = 0 ∨ q.2 = 0 := by
        rcases h with h1 | h2 | h3 | h4 | h5
        · exact absurd hpq h1
        · exact absurd hx h2
        · exact absurd (hpq ▸ hx) h3
        · exact Or.inl h4
        · exact Or.inr h5
      exact labelLT_perm_iff_of_index_zero hσ0 hx hpq h0
    · have hp : permLabel x₀ σ p = p := by
        simp only [permLabel, if_neg hx]
      have hq : permLabel x₀ σ q = q := by
        have hxq : q.1 ≠ x₀ := fun hh => hx (hh ▸ hpq ▸ rfl)
        simp only [permLabel, if_neg hxq]
      rw [hp, hq]
  · exact labelLT_perm_iff_of_sites_ne hpq

/-- A label whose relabeled image is the tagged label carries the index
`0`. -/
theorem index_zero_of_permLabel_tagged {x₀ : Site d} {σ : Equiv.Perm ℕ}
    (hσ0 : σ 0 = 0) {r : Label d}
    (h : permLabel x₀ σ r = ((0 : Site d), 0)) : r.2 = 0 := by
  unfold permLabel at h
  split at h
  · simp only [Prod.mk.injEq] at h
    exact (perm_eq_zero_iff hσ0 r.2).mp h.2
  · simp only [Prod.mk.injEq] at h
    exact h.2


variable {d : ℕ} {x₀ : Site d} {σ : Equiv.Perm ℕ} {D' D : PDriver d} {S' S : State d}

/-- Every tie of the tagged driver involves the tagged label. -/
def TaggedTies {d : ℕ} (D : PDriver d) : Prop :=
  ∀ (t : ℕ) (p q : Label d), p ≠ q → D.rank (p, t) = D.rank (q, t) →
    p = ((0 : Site d), 0) ∨ q = ((0 : Site d), 0)

theorem tagged_ties_index_zero (hD : RelabelDriver x₀ σ D' D) (hσ0 : σ 0 = 0)
    (hties : TaggedTies D) (t : ℕ) (p q : Label d)
    (hne : p ≠ q) (heq : D'.rank (p, t) = D'.rank (q, t)) : p.2 = 0 ∨ q.2 = 0 := by
  rw [hD.rank p t, hD.rank q t] at heq
  rcases hties t (permLabel x₀ σ p) (permLabel x₀ σ q) (fun h => hne ((permLabelEquiv x₀ σ).injective h)) heq with h | h
  · exact Or.inl (index_zero_of_permLabel_tagged hσ0 h)
  · exact Or.inr (index_zero_of_permLabel_tagged hσ0 h)

/-- Membership in the tie-break filter is preserved by the relabeling, with
the tie clause carried by the label order. -/
theorem mem_filter_prec_perm_of_ties (hD : RelabelDriver x₀ σ D' D)
    (hS : RelabelState x₀ σ S' S)
    (hσ : ∀ i, (D.eta x₀).toNat ≤ i → σ i = i) (hσ0 : σ 0 = 0)
    (hties : TaggedTies D) (t : ℕ) (p b : Label d) :
    (b ∈ (pArrivalsAt D' S' t (pNextPos D' S' t p)).filter fun q =>
        D'.rank (q, t) < D'.rank (p, t) ∨
          (D'.rank (q, t) = D'.rank (p, t) ∧ labelLT q p))
    ↔ (permLabel x₀ σ b ∈ (pArrivalsAt D S t (pNextPos D S t (permLabel x₀ σ p))).filter fun q =>
        D.rank (q, t) < D.rank (permLabel x₀ σ p, t) ∨
          (D.rank (q, t) = D.rank (permLabel x₀ σ p, t) ∧
            labelLT q (permLabel x₀ σ p))) := by
  have hz : pNextPos D' S' t p = pNextPos D S t (permLabel x₀ σ p) := pNextPos_perm hD hS t p
  constructor
  · intro h
    rw [Finset.mem_filter] at h
    obtain ⟨hM, (h | ⟨heq, hlt⟩)⟩ := h
    · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [hz] at hM
        exact (mem_pArrivalsAt_perm hD hS hσ t _ b).mp hM
      · rw [hD.rank b t, hD.rank p t] at h
        exact Or.inl h
    · have hne : b ≠ p := fun h => absurd hlt (by rw [h]; exact lt_irrefl _)
      have hexc : b.1 ≠ p.1 ∨ b.1 ≠ x₀ ∨ p.1 ≠ x₀ ∨ b.2 = 0 ∨ p.2 = 0 :=
        Or.inr (Or.inr (Or.inr (tagged_ties_index_zero hD hσ0 hties t b p hne heq)))
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [hz] at hM
        exact (mem_pArrivalsAt_perm hD hS hσ t _ b).mp hM
      · rw [hD.rank b t, hD.rank p t] at heq
        exact Or.inr ⟨heq, (labelLT_perm_iff_of_fixes_zero hσ0 hexc).mpr hlt⟩
  · intro h
    rw [Finset.mem_filter] at h
    obtain ⟨hM, (h | ⟨heq, hlt⟩)⟩ := h
    · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [hz]
        exact (mem_pArrivalsAt_perm hD hS hσ t _ b).mpr hM
      · rw [hD.rank b t, hD.rank p t]
        exact Or.inl h
    · have hne : permLabel x₀ σ b ≠ permLabel x₀ σ p := by
        intro h
        have : b = p := (permLabelEquiv x₀ σ).injective (by
          simpa only [permLabelEquiv_apply] using h)
        exact absurd (this ▸ hlt) (lt_irrefl _)
      have hexc : b.1 ≠ p.1 ∨ b.1 ≠ x₀ ∨ p.1 ≠ x₀ ∨ b.2 = 0 ∨ p.2 = 0 := by
        rcases hties t (permLabel x₀ σ b) (permLabel x₀ σ p) hne heq with h' | h'
        · exact Or.inr (Or.inr (Or.inr (Or.inl (index_zero_of_permLabel_tagged hσ0 h'))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (index_zero_of_permLabel_tagged hσ0 h'))))
      refine Finset.mem_filter.mpr ⟨?_, Or.inr ⟨?_, ?_⟩⟩
      · rw [hz]
        exact (mem_pArrivalsAt_perm hD hS hσ t _ b).mpr hM
      · rw [hD.rank b t, hD.rank p t]
        exact heq
      · exact (labelLT_perm_iff_of_fixes_zero hσ0 hexc).mp hlt


theorem card_filter_prec_perm_of_ties (hD : RelabelDriver x₀ σ D' D)
    (hS : RelabelState x₀ σ S' S)
    (hσ : ∀ i, (D.eta x₀).toNat ≤ i → σ i = i) (hσ0 : σ 0 = 0)
    (hties : TaggedTies D) (t : ℕ) (p : Label d) :
    ((pArrivalsAt D' S' t (pNextPos D' S' t p)).filter fun q =>
        D'.rank (q, t) < D'.rank (p, t) ∨
          (D'.rank (q, t) = D'.rank (p, t) ∧ labelLT q p)).card
      = ((pArrivalsAt D S t (pNextPos D S t (permLabel x₀ σ p))).filter fun q =>
        D.rank (q, t) < D.rank (permLabel x₀ σ p, t) ∨
          (D.rank (q, t) = D.rank (permLabel x₀ σ p, t) ∧
            labelLT q (permLabel x₀ σ p))).card := by
  have hmap : ((pArrivalsAt D' S' t (pNextPos D' S' t p)).filter fun q =>
        D'.rank (q, t) < D'.rank (p, t) ∨
          (D'.rank (q, t) = D'.rank (p, t) ∧ labelLT q p))
      = (((pArrivalsAt D S t (pNextPos D S t (permLabel x₀ σ p))).filter fun q =>
        D.rank (q, t) < D.rank (permLabel x₀ σ p, t) ∨
          (D.rank (q, t) = D.rank (permLabel x₀ σ p, t) ∧
            labelLT q (permLabel x₀ σ p)))).map
          (permLabelEquiv x₀ σ).symm.toEmbedding := by
    ext b
    rw [Finset.mem_map_equiv]
    simp only [Equiv.symm_symm, permLabelEquiv_apply]
    exact mem_filter_prec_perm_of_ties hD hS hσ hσ0 hties t p b
  rw [hmap, Finset.card_map]

/-- A label settles exactly when its image settles, under the ties hypothesis. -/
theorem pSettles_perm_of_ties (hD : RelabelDriver x₀ σ D' D) (hS : RelabelState x₀ σ S' S)
    (hσ : ∀ i, (D.eta x₀).toNat ≤ i → σ i = i) (hσ0 : σ 0 = 0)
    (hties : TaggedTies D)
    (t : ℕ) (p : Label d) :
    pSettles D' S' t p = pSettles D S t (permLabel x₀ σ p) := by
  have hz : pNextPos D' S' t p = pNextPos D S t (permLabel x₀ σ p) := pNextPos_perm hD hS t p
  have hholes : S'.holes (pNextPos D' S' t p)
      = S.holes (pNextPos D S t (permLabel x₀ σ p)) := by rw [hS.holes, hz]
  simp only [pSettles, hS.active p, card_filter_prec_perm_of_ties hD hS hσ hσ0 hties t p, hholes]


variable {d : ℕ}

end Parking
