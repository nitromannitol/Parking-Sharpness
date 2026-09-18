/-
The equivariance of the TAGGED construction under relabeling the particles at
one site.

`taggedDriver w r ω` puts the prescribed particle back at the origin as the
label `(0, 0)` and pushes the labels of the particles already there up by one.
Its uniform variables are those of `ω`, read at the shifted labels, except at
the tagged label, where they are the prescribed `r`.  So on the set where the
uniform variables of `ω` are pairwise distinct, the non-tagged labels of the
tagged realization carry pairwise distinct values, and EVERY tie involves the
tagged label and exactly one other label.

The label order is site-major, so such a tie is decided by the two sites alone
when the other label is not at the origin, and by the index when it is, where
the tagged label is the unique label of index zero.  Relabeling the particles
present at a site moves no site, and at the origin it permutes the indices at
least one among themselves, so it decides every tie the same way.  That is
`Parking.TieInvariant`, and it is all the equivariance of `Support/RelabelEquiv.lean`
asks for.
-/
import Parking.Support.SubcriticalPair

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

theorem relabelAt_move (x₀ : Site d) (σ : Equiv.Perm ℕ) (ω : PData d) (q : Label d) (s : ℕ) :
    (relabelAt x₀ σ ω).2.1 (q, s) = ω.2.1 ((q.1, if q.1 = x₀ then σ q.2 else q.2), s) := rfl

theorem relabelAt_rank (x₀ : Site d) (σ : Equiv.Perm ℕ) (ω : PData d) (q : Label d) (s : ℕ) :
    (relabelAt x₀ σ ω).2.2 (q, s) = ω.2.2 ((q.1, if q.1 = x₀ then σ q.2 else q.2), s) := rfl

theorem taggedMove_apply (w : ℕ → Fin d × Bool) (m : Label d × ℕ → Fin d × Bool)
    (p : Label d) (s : ℕ) :
    taggedMove w m (p, s)
      = if p.1 = 0 then (if p.2 = 0 then w s else m ((0, p.2 - 1), s)) else m (p, s) := rfl

theorem taggedRank_apply (r : ℕ → ℝ) (v : Label d × ℕ → ℝ) (p : Label d) (s : ℕ) :
    taggedRank r v (p, s)
      = if p.1 = 0 then (if p.2 = 0 then r s else v ((0, p.2 - 1), s)) else v (p, s) := rfl

/-- The label of `ω` whose walk and uniform variables the non-tagged label `p`
of the tagged realization carries. -/
def taggedSource (p : Label d) : Label d := if p.1 = 0 then (0, p.2 - 1) else p

/-- Away from the tagged label the tagged uniform variables are those of the
realization, read at the source label. -/
theorem taggedRank_apply_of_ne (r : ℕ → ℝ) (v : Label d × ℕ → ℝ) (p : Label d) (s : ℕ)
    (hp : p ≠ ((0 : Site d), 0)) : taggedRank r v (p, s) = v (taggedSource p, s) := by
  unfold taggedRank taggedSource
  by_cases h0 : p.1 = 0
  · have h2 : p.2 ≠ 0 := fun h2 => hp (Prod.ext h0 h2)
    rw [if_pos h0, if_pos h0, if_neg h2]
  · rw [if_neg h0, if_neg h0]

/-- The source map is injective on the non-tagged labels. -/
theorem taggedSource_inj {p q : Label d} (hp : p ≠ ((0 : Site d), 0))
    (hq : q ≠ ((0 : Site d), 0)) (h : taggedSource p = taggedSource q) : p = q := by
  unfold taggedSource at h
  by_cases hp0 : p.1 = 0 <;> by_cases hq0 : q.1 = 0
  · rw [if_pos hp0, if_pos hq0] at h
    have h2 : p.2 - 1 = q.2 - 1 := congrArg Prod.snd h
    have hp2 : p.2 ≠ 0 := fun hh => hp (Prod.ext hp0 hh)
    have hq2 : q.2 ≠ 0 := fun hh => hq (Prod.ext hq0 hh)
    exact Prod.ext (hp0.trans hq0.symm) (by omega)
  · rw [if_pos hp0, if_neg hq0] at h
    exact absurd (congrArg Prod.fst h).symm hq0
  · rw [if_neg hp0, if_pos hq0] at h
    exact absurd (congrArg Prod.fst h) hp0
  · rw [if_neg hp0, if_neg hq0] at h
    exact h

/-- **Every tie in the tagged driver involves the tagged label.**  The non-tagged
labels carry the uniform variables of `ω` read at distinct labels. -/
theorem tagged_tie_eq (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) {ω : PData d}
    (hinj : Function.Injective ω.2.2) (s : ℕ) {p q : Label d}
    (h : (taggedDriver w r ω).rank (p, s) = (taggedDriver w r ω).rank (q, s))
    (hpq : p ≠ q) : p = ((0 : Site d), 0) ∨ q = ((0 : Site d), 0) := by
  by_cases hp : p = ((0 : Site d), 0)
  · exact Or.inl hp
  by_cases hq : q = ((0 : Site d), 0)
  · exact Or.inr hq
  exfalso
  have hrp : (taggedDriver w r ω).rank (p, s) = ω.2.2 (taggedSource p, s) :=
    taggedRank_apply_of_ne r ω.2.2 p s hp
  have hrq : (taggedDriver w r ω).rank (q, s) = ω.2.2 (taggedSource q, s) :=
    taggedRank_apply_of_ne r ω.2.2 q s hq
  rw [hrp, hrq] at h
  exact hpq (taggedSource_inj hp hq (congrArg Prod.fst (hinj h)))

/-- The label order compares two labels at different sites by their sites alone. -/
theorem labelLT_iff_lex (p q : Label d) :
    labelLT p q ↔ ((toLex p.1 : Lex (Fin d → ℤ)) < toLex q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)) := by
  simp only [labelLT, labelKey, Prod.Lex.toLex_lt_toLex, toLex_inj]

theorem labelLT_of_fst_ne {p q : Label d} (h : p.1 ≠ q.1) (i j : ℕ) :
    labelLT p q ↔ labelLT ((p.1, i) : Label d) (q.1, j) := by
  rw [labelLT_iff_lex, labelLT_iff_lex]
  constructor
  · rintro (h1 | ⟨h1, -⟩)
    · exact Or.inl h1
    · exact absurd h1 h
  · rintro (h1 | ⟨h1, -⟩)
    · exact Or.inl h1
    · exact absurd h1 h

/-- The label order compares two labels at the same site by their indices. -/
theorem labelLT_same_fst (x : Site d) (i j : ℕ) :
    labelLT ((x, i) : Label d) (x, j) ↔ i < j := by
  rw [labelLT_iff_lex]
  simp

/-- A comparison with the tagged label, read as a lexicographic comparison. -/
theorem labelLT_origin_iff (q : Label d) :
    labelLT ((0 : Site d), 0) q ↔
      ((toLex (0 : Site d) : Lex (Fin d → ℤ)) < toLex q.1 ∨ ((0 : Site d) = q.1 ∧ q.2 ≠ 0)) := by
  rw [labelLT_iff_lex]
  simp [Nat.pos_iff_ne_zero]

theorem labelLT_to_origin_iff (q : Label d) :
    labelLT q ((0 : Site d), 0) ↔ (toLex q.1 : Lex (Fin d → ℤ)) < toLex (0 : Site d) := by
  rw [labelLT_iff_lex]
  simp

/-- A relabeling that fixes the tagged label sends the nonzero indices at the
origin to nonzero indices. -/
theorem permLabel_snd_eq_zero_iff {x₀ : Site d} {σ : Equiv.Perm ℕ}
    (hfix : permLabel x₀ σ ((0 : Site d), 0) = ((0 : Site d), 0)) (j : ℕ) :
    (permLabel x₀ σ ((0 : Site d), j)).2 = 0 ↔ j = 0 := by
  by_cases hx : (0 : Site d) = x₀
  · have h0 : σ 0 = 0 := by
      have h := congrArg Prod.snd hfix
      simpa only [permLabel, if_pos hx] using h
    have hval : (permLabel x₀ σ ((0 : Site d), j)).2 = σ j := by
      simp only [permLabel, if_pos hx]
    rw [hval]
    constructor
    · intro h
      exact σ.injective (h.trans h0.symm)
    · intro h
      rw [h, h0]
  · have hval : (permLabel x₀ σ ((0 : Site d), j)).2 = j := by
      simp only [permLabel, if_neg hx]
    rw [hval]

/-- A relabeling of the particles present at a site that fixes the tagged label
compares every label with the tagged label the same way before and after. -/
theorem labelLT_tagged_perm {x₀ : Site d} {σ : Equiv.Perm ℕ}
    (hfix : permLabel x₀ σ ((0 : Site d), 0) = ((0 : Site d), 0)) (q : Label d) :
    (labelLT ((0 : Site d), 0) q ↔ labelLT ((0 : Site d), 0) (permLabel x₀ σ q)) ∧
      (labelLT q ((0 : Site d), 0) ↔ labelLT (permLabel x₀ σ q) ((0 : Site d), 0)) := by
  have hfst : (permLabel x₀ σ q).1 = q.1 := rfl
  constructor
  · rw [labelLT_origin_iff, labelLT_origin_iff, hfst]
    refine or_congr Iff.rfl (and_congr_right fun hy => ?_)
    have hq : permLabel x₀ σ q = permLabel x₀ σ ((0 : Site d), q.2) := by rw [hy]
    rw [hq]
    exact not_congr (permLabel_snd_eq_zero_iff hfix q.2).symm
  · rw [labelLT_to_origin_iff, labelLT_to_origin_iff, hfst]

/-- **The tagged driver is tie-invariant** under relabeling the particles
present at a site, at every realization whose uniform variables are pairwise
distinct, provided the relabeling fixes the tagged label. -/
theorem tieInvariant_tagged {x₀ : Site d} {σ : Equiv.Perm ℕ} {ω : PData d} {D' : PDriver d}
    (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) (hinj : Function.Injective ω.2.2)
    (hfix : permLabel x₀ σ ((0 : Site d), 0) = ((0 : Site d), 0))
    (hD : RelabelDriver x₀ σ D' (taggedDriver w r ω)) : TieInvariant x₀ σ D' := by
  intro t a b h
  rw [hD.rank a t, hD.rank b t] at h
  by_cases hab : permLabel x₀ σ a = permLabel x₀ σ b
  · have hab' : a = b := (permLabelEquiv x₀ σ).injective hab
    subst hab'
    constructor
    · intro h1; exact absurd h1 (LatticeProb.labelLT_irrefl a)
    · intro h1; exact absurd h1 (LatticeProb.labelLT_irrefl _)
  · rcases tagged_tie_eq w r hinj t h hab with h0 | h0
    · have ha : a = ((0 : Site d), 0) := (permLabelEquiv x₀ σ).injective (h0.trans hfix.symm)
      subst ha
      rw [hfix]
      exact (labelLT_tagged_perm hfix b).1
    · have hb : b = ((0 : Site d), 0) := (permLabelEquiv x₀ σ).injective (h0.trans hfix.symm)
      subst hb
      rw [hfix]
      exact (labelLT_tagged_perm hfix a).2

/-- The permutation of the indices at the origin induced by `σ` once the tagged
particle sits at the bottom label: the tagged index `0` is fixed, and the index
`i + 1` follows `i`. -/
def shiftPerm (σ : Equiv.Perm ℕ) : Equiv.Perm ℕ where
  toFun := fun i => if i = 0 then 0 else σ (i - 1) + 1
  invFun := fun i => if i = 0 then 0 else σ.symm (i - 1) + 1
  left_inv := by
    intro i
    by_cases h : i = 0
    · subst h; rfl
    · simp only [if_neg h, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel,
        Equiv.symm_apply_apply]
      omega
  right_inv := by
    intro i
    by_cases h : i = 0
    · subst h; rfl
    · simp only [if_neg h, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel,
        Equiv.apply_symm_apply]
      omega

@[simp] theorem shiftPerm_zero (σ : Equiv.Perm ℕ) : shiftPerm σ 0 = 0 := rfl

theorem shiftPerm_apply_ne (σ : Equiv.Perm ℕ) {i : ℕ} (h : i ≠ 0) :
    shiftPerm σ i = σ (i - 1) + 1 := by
  show (if i = 0 then 0 else σ (i - 1) + 1) = σ (i - 1) + 1
  rw [if_neg h]

/-- **Relabeling the particles present at a site other than the origin** carries
over to the tagged realization by the same permutation. -/
theorem relabelDriver_tagged_ne (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) {x₀ : Site d}
    (hx₀ : x₀ ≠ (0 : Site d)) (σ : Equiv.Perm ℕ) (ω : PData d) :
    RelabelDriver x₀ σ (taggedDriver w r (relabelAt x₀ σ ω)) (taggedDriver w r ω) := by
  have h0x : ¬ ((0 : Site d) = x₀) := fun hh => hx₀ hh.symm
  refine ⟨fun x => rfl, fun p s => ?_, fun p s => ?_⟩
  · show taggedMove w (relabelAt x₀ σ ω).2.1 (p, s) = taggedMove w ω.2.1 (permLabel x₀ σ p, s)
    have hfst : (permLabel x₀ σ p).1 = p.1 := rfl
    by_cases h0 : p.1 = (0 : Site d)
    · have hne : ¬ (p.1 = x₀) := by rw [h0]; exact h0x
      have hsnd : (permLabel x₀ σ p).2 = p.2 := by simp only [permLabel, if_neg hne]
      rw [taggedMove_apply, taggedMove_apply, hfst, hsnd, if_pos h0, if_pos h0]
      by_cases h2 : p.2 = 0
      · rw [if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2, relabelAt_move]
        simp only [if_neg h0x]
    · rw [taggedMove_apply, taggedMove_apply, hfst, if_neg h0, if_neg h0, relabelAt_move]
      rfl
  · show taggedRank r (relabelAt x₀ σ ω).2.2 (p, s) = taggedRank r ω.2.2 (permLabel x₀ σ p, s)
    have hfst : (permLabel x₀ σ p).1 = p.1 := rfl
    by_cases h0 : p.1 = (0 : Site d)
    · have hne : ¬ (p.1 = x₀) := by rw [h0]; exact h0x
      have hsnd : (permLabel x₀ σ p).2 = p.2 := by simp only [permLabel, if_neg hne]
      rw [taggedRank_apply, taggedRank_apply, hfst, hsnd, if_pos h0, if_pos h0]
      by_cases h2 : p.2 = 0
      · rw [if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2, relabelAt_rank]
        simp only [if_neg h0x]
    · rw [taggedRank_apply, taggedRank_apply, hfst, if_neg h0, if_neg h0, relabelAt_rank]
      rfl

/-- **Relabeling the particles present at the origin** carries over to the
tagged realization by `Parking.shiftPerm`, which fixes the tagged label. -/
theorem relabelDriver_tagged_origin (w : ℕ → Fin d × Bool) (r : ℕ → ℝ)
    (σ : Equiv.Perm ℕ) (ω : PData d) :
    RelabelDriver (0 : Site d) (shiftPerm σ) (taggedDriver w r (relabelAt 0 σ ω))
      (taggedDriver w r ω) := by
  refine ⟨fun x => rfl, fun p s => ?_, fun p s => ?_⟩
  · show taggedMove w (relabelAt 0 σ ω).2.1 (p, s)
        = taggedMove w ω.2.1 (permLabel 0 (shiftPerm σ) p, s)
    have hfst : (permLabel (0 : Site d) (shiftPerm σ) p).1 = p.1 := rfl
    by_cases h0 : p.1 = (0 : Site d)
    · have hsnd : (permLabel (0 : Site d) (shiftPerm σ) p).2 = shiftPerm σ p.2 := by
        simp only [permLabel, if_pos h0]
      rw [taggedMove_apply, taggedMove_apply, hfst, hsnd, if_pos h0, if_pos h0]
      by_cases h2 : p.2 = 0
      · rw [h2, shiftPerm_zero, if_pos rfl, if_pos rfl]
      · rw [if_neg h2, shiftPerm_apply_ne σ h2,
          if_neg (Nat.succ_ne_zero (σ (p.2 - 1))), Nat.add_sub_cancel, relabelAt_move,
          if_pos rfl]
    · have hsnd : (permLabel (0 : Site d) (shiftPerm σ) p).2 = p.2 := by
        simp only [permLabel, if_neg h0]
      rw [taggedMove_apply, taggedMove_apply, hfst, hsnd, if_neg h0, if_neg h0,
        relabelAt_move, if_neg h0]
      simp only [permLabel, if_neg h0]
  · show taggedRank r (relabelAt 0 σ ω).2.2 (p, s)
        = taggedRank r ω.2.2 (permLabel 0 (shiftPerm σ) p, s)
    have hfst : (permLabel (0 : Site d) (shiftPerm σ) p).1 = p.1 := rfl
    by_cases h0 : p.1 = (0 : Site d)
    · have hsnd : (permLabel (0 : Site d) (shiftPerm σ) p).2 = shiftPerm σ p.2 := by
        simp only [permLabel, if_pos h0]
      rw [taggedRank_apply, taggedRank_apply, hfst, hsnd, if_pos h0, if_pos h0]
      by_cases h2 : p.2 = 0
      · rw [h2, shiftPerm_zero, if_pos rfl, if_pos rfl]
      · rw [if_neg h2, shiftPerm_apply_ne σ h2,
          if_neg (Nat.succ_ne_zero (σ (p.2 - 1))), Nat.add_sub_cancel, relabelAt_rank,
          if_pos rfl]
    · have hsnd : (permLabel (0 : Site d) (shiftPerm σ) p).2 = p.2 := by
        simp only [permLabel, if_neg h0]
      rw [taggedRank_apply, taggedRank_apply, hfst, hsnd, if_neg h0, if_neg h0,
        relabelAt_rank, if_neg h0]
      simp only [permLabel, if_neg h0]

/-- The induced permutation at the origin fixes every index at or above the
count the tagged realization carries there. -/
theorem shiftPerm_fixes {σ : Equiv.Perm ℕ} {η : Site d → ℤ}
    (hσ : ∀ i, (η (0 : Site d)).toNat ≤ i → σ i = i) :
    ∀ i, ((addParticle (0 : Site d) η) 0).toNat ≤ i → shiftPerm σ i = i := by
  intro i hi
  have hval : (addParticle (0 : Site d) η) 0 = η 0 + 1 := by
    simp [addParticle]
  rw [hval] at hi
  by_cases h0 : i = 0
  · rw [h0]; rfl
  · rw [shiftPerm_apply_ne σ h0, hσ (i - 1) (by omega)]
    omega

/-- **The tagged particle's activity is unchanged by relabeling the particles
present at a site**, at every realization whose uniform variables are pairwise
distinct.  This is the clause `thm:subcritical` needs of its survival
observable. -/
theorem taggedActive_relabelAt (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) {x₀ : Site d}
    {σ : Equiv.Perm ℕ} {ω : PData d} (hσ : ∀ i, (ω.1 x₀).toNat ≤ i → σ i = i)
    (hinj : Function.Injective ω.2.2) (t : ℕ) :
    (pState (taggedDriver w r (relabelAt x₀ σ ω)) t).active ((0 : Site d), 0)
      = (pState (taggedDriver w r ω) t).active ((0 : Site d), 0) := by
  by_cases hx : x₀ = (0 : Site d)
  · subst hx
    have hD := relabelDriver_tagged_origin w r σ ω
    have hfix : permLabel (0 : Site d) (shiftPerm σ) ((0 : Site d), 0) = ((0 : Site d), 0) := by
      simp [permLabel]
    have hσ' : ∀ i, ((taggedDriver w r ω).eta (0 : Site d)).toNat ≤ i → shiftPerm σ i = i :=
      shiftPerm_fixes hσ
    have h := (pState_perm hD hσ' (tieInvariant_tagged w r hinj hfix hD) t).active
      ((0 : Site d), 0)
    rw [h, hfix]
  · have hD := relabelDriver_tagged_ne w r hx σ ω
    have hfix : permLabel x₀ σ ((0 : Site d), 0) = ((0 : Site d), 0) := by
      simp only [permLabel, if_neg (fun hh : (0 : Site d) = x₀ => hx hh.symm)]
    have hσ' : ∀ i, ((taggedDriver w r ω).eta x₀).toNat ≤ i → σ i = i := by
      intro i hi
      refine hσ i ?_
      have heta : (taggedDriver w r ω).eta x₀ = ω.1 x₀ := by
        show addParticle (0 : Site d) ω.1 x₀ = ω.1 x₀
        simp only [addParticle, if_neg hx]
      rwa [heta] at hi
    have h := (pState_perm hD hσ' (tieInvariant_tagged w r hinj hfix hD) t).active
      ((0 : Site d), 0)
    rw [h, hfix]

end Parking

end
