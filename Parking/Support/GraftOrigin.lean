/-
Prescribing the particles at the origin.

`thm:subcritical` (`parking.tex:2434-2440`) begins "Prescribe the `k` particles
at the origin and temporarily condition on all their walks and uniform
variables", and writes `Ê_λ` for the expectation in which "the origin carries
the remaining `k-1` prescribed particles and every other site has the tilted
law".  `graftOrigin ω₁ ω` is that realization: the count, the walks and the
uniform variables at the origin are read off the prescription `ω₁`, and every
other site is read off `ω`.

The observables of the theorem, read at `graftOrigin ω₁ ω`, are then functions
of the data at the sites OTHER than the origin, which is what `lem:product` asks
of them once the origin is held fixed.  Their two relabeling clauses survive the
graft:

- relabeling the particles at the ORIGIN changes nothing at all, because the
  graft overwrites exactly the data such a relabeling moves;
- relabeling the particles at another site `x₀` is the same relabeling of the
  grafted realization, and there every tie among the uniform variables involves
  a label AT THE ORIGIN, because off the origin the grafted uniform variables
  are those of `ω` read at distinct labels.  The label order is site-major and
  `x₀` is not the origin, so the permutation fixes every label of the origin and
  compares it with any other label by the two sites alone.  That is
  `Parking.TieInvariant`, which is all that `Support/RelabelEquiv.lean` needs.
-/
import Parking.Support.SubcriticalRelabel

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- The realization carrying the prescription `ω₁` at the origin and `ω`
everywhere else. -/
def graftOrigin (ω₁ ω : PData d) : PData d :=
  ((fun x => if x = (0 : Site d) then ω₁.1 x else ω.1 x),
    (fun q : Label d × ℕ => if q.1.1 = (0 : Site d) then ω₁.2.1 q else ω.2.1 q),
    (fun q : Label d × ℕ => if q.1.1 = (0 : Site d) then ω₁.2.2 q else ω.2.2 q))

@[simp] theorem graftOrigin_eta_zero (ω₁ ω : PData d) :
    (graftOrigin ω₁ ω).1 (0 : Site d) = ω₁.1 (0 : Site d) := by
  simp [graftOrigin]

theorem graftOrigin_eta_of_ne {x : Site d} (hx : x ≠ (0 : Site d)) (ω₁ ω : PData d) :
    (graftOrigin ω₁ ω).1 x = ω.1 x := by
  simp [graftOrigin, hx]

theorem graftOrigin_move_of_ne {q : Label d × ℕ} (hq : q.1.1 ≠ (0 : Site d))
    (ω₁ ω : PData d) : (graftOrigin ω₁ ω).2.1 q = ω.2.1 q := by
  simp [graftOrigin, hq]

theorem graftOrigin_rank_of_ne {q : Label d × ℕ} (hq : q.1.1 ≠ (0 : Site d))
    (ω₁ ω : PData d) : (graftOrigin ω₁ ω).2.2 q = ω.2.2 q := by
  simp [graftOrigin, hq]

/-- Relabeling the particles at the ORIGIN is erased by the graft. -/
theorem graftOrigin_relabelAt_zero (σ : Equiv.Perm ℕ) (ω₁ ω : PData d) :
    graftOrigin ω₁ (relabelAt (0 : Site d) σ ω) = graftOrigin ω₁ ω := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext x
    simp only [graftOrigin, relabelAt]
  · funext q
    simp only [graftOrigin, relabelAt]
    by_cases hq : q.1.1 = (0 : Site d)
    · rw [if_pos hq, if_pos hq]
    · rw [if_neg hq, if_neg hq, if_neg hq]
  · funext q
    simp only [graftOrigin, relabelAt]
    by_cases hq : q.1.1 = (0 : Site d)
    · rw [if_pos hq, if_pos hq]
    · rw [if_neg hq, if_neg hq, if_neg hq]

/-- Relabeling the particles at another site commutes with the graft. -/
theorem graftOrigin_relabelAt {x₀ : Site d} (hx₀ : x₀ ≠ (0 : Site d)) (σ : Equiv.Perm ℕ)
    (ω₁ ω : PData d) :
    graftOrigin ω₁ (relabelAt x₀ σ ω) = relabelAt x₀ σ (graftOrigin ω₁ ω) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext x
    simp only [graftOrigin, relabelAt]
  · funext q
    simp only [graftOrigin, relabelAt]
    by_cases hq : q.1.1 = (0 : Site d)
    · have hne : ¬ (q.1.1 = x₀) := by rw [hq]; exact fun hh => hx₀ hh.symm
      rw [if_pos hq, if_neg hne, if_pos hq]
    · rw [if_neg hq, if_neg hq]
  · funext q
    simp only [graftOrigin, relabelAt]
    by_cases hq : q.1.1 = (0 : Site d)
    · have hne : ¬ (q.1.1 = x₀) := by rw [hq]; exact fun hh => hx₀ hh.symm
      rw [if_pos hq, if_neg hne, if_pos hq]
    · rw [if_neg hq, if_neg hq]

/-- Adding a particle at the origin is erased by the graft. -/
theorem graftOrigin_addAt_zero (ω₁ ω : PData d) :
    graftOrigin ω₁ (addAt (0 : Site d) ω) = graftOrigin ω₁ ω := by
  refine Prod.ext ?_ rfl
  funext x
  by_cases hx : x = (0 : Site d)
  · simp [graftOrigin, addAt, addParticle, hx]
  · simp [graftOrigin, addAt, addParticle, hx]

/-- Deleting a particle at the origin is erased by the graft. -/
theorem graftOrigin_delAt_zero (ω₁ ω : PData d) :
    graftOrigin ω₁ (delAt (0 : Site d) ω) = graftOrigin ω₁ ω := by
  refine Prod.ext ?_ rfl
  funext x
  by_cases hx : x = (0 : Site d)
  · simp [graftOrigin, delAt, hx]
  · simp [graftOrigin, delAt, hx]

/-- Adding a particle at another site commutes with the graft. -/
theorem graftOrigin_addAt {x₀ : Site d} (hx₀ : x₀ ≠ (0 : Site d)) (ω₁ ω : PData d) :
    graftOrigin ω₁ (addAt x₀ ω) = addAt x₀ (graftOrigin ω₁ ω) := by
  refine Prod.ext ?_ rfl
  funext x
  simp only [graftOrigin, addAt, addParticle]
  by_cases hx : x = (0 : Site d)
  · have hne : ¬ (x = x₀) := by rw [hx]; exact fun hh => hx₀ hh.symm
    rw [if_pos hx, if_neg hne, if_pos hx]
  · rw [if_neg hx, if_neg hx]

/-- Deleting a particle at another site commutes with the graft. -/
theorem graftOrigin_delAt {x₀ : Site d} (hx₀ : x₀ ≠ (0 : Site d)) (ω₁ ω : PData d) :
    graftOrigin ω₁ (delAt x₀ ω) = delAt x₀ (graftOrigin ω₁ ω) := by
  refine Prod.ext ?_ rfl
  funext x
  simp only [graftOrigin, delAt]
  by_cases hx : x = (0 : Site d)
  · have hne : ¬ (x = x₀) := by rw [hx]; exact fun hh => hx₀ hh.symm
    rw [if_pos hx, if_neg hne, if_pos hx]
  · rw [if_neg hx, if_neg hx]

theorem measurable_graftOrigin (ω₁ : PData d) : Measurable (graftOrigin (d := d) ω₁) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · refine measurable_pi_lambda _ fun x => ?_
    by_cases hx : x = (0 : Site d)
    · simp [hx]
    · simpa [graftOrigin, hx] using (measurable_fst.eval : Measurable fun ω : PData d => ω.1 x)
  · refine measurable_pi_lambda _ fun q => ?_
    by_cases hq : q.1.1 = (0 : Site d)
    · simp [hq]
    · simpa [graftOrigin, hq] using
        (measurable_snd.fst.eval : Measurable fun ω : PData d => ω.2.1 q)
  · refine measurable_pi_lambda _ fun q => ?_
    by_cases hq : q.1.1 = (0 : Site d)
    · simp [hq]
    · simpa [graftOrigin, hq] using
        (measurable_snd.snd.eval : Measurable fun ω : PData d => ω.2.2 q)

/-- Two labels at different sites compare the same way before and after a
relabeling, because the label order is site-major. -/
theorem labelLT_permLabel_of_fst_ne {x₀ : Site d} {σ : Equiv.Perm ℕ} {a b : Label d}
    (h : a.1 ≠ b.1) : labelLT a b ↔ labelLT (permLabel x₀ σ a) (permLabel x₀ σ b) := by
  have h1 : (permLabel x₀ σ a).1 = a.1 := rfl
  have h2 : (permLabel x₀ σ b).1 = b.1 := rfl
  rw [labelLT_iff_lex, labelLT_iff_lex, h1, h2]
  constructor
  · rintro (hl | ⟨hl, -⟩)
    · exact Or.inl hl
    · exact absurd hl h
  · rintro (hl | ⟨hl, -⟩)
    · exact Or.inl hl
    · exact absurd hl h

/-- **A driver whose every tie involves a label at the origin is tie-invariant
under relabeling the particles at any other site.**  Such a relabeling fixes
every label of the origin, and compares it with a label elsewhere by the two
sites alone. -/
theorem tieInvariant_of_ties_at_origin {x₀ : Site d} {σ : Equiv.Perm ℕ} {D' : PDriver d}
    (hx₀ : x₀ ≠ (0 : Site d))
    (hties : ∀ (s : ℕ) (a b : Label d), D'.rank (a, s) = D'.rank (b, s) → a ≠ b →
      a.1 = (0 : Site d) ∨ b.1 = (0 : Site d)) :
    TieInvariant x₀ σ D' := by
  have hfix : ∀ p : Label d, p.1 = (0 : Site d) → permLabel x₀ σ p = p := by
    intro p hp
    have hne : ¬ (p.1 = x₀) := by rw [hp]; exact fun hh => hx₀ hh.symm
    simp only [permLabel, if_neg hne]
  intro t a b h
  by_cases hab : a = b
  · subst hab
    constructor
    · intro h1; exact absurd h1 (LatticeProb.labelLT_irrefl a)
    · intro h1; exact absurd h1 (LatticeProb.labelLT_irrefl _)
  · rcases hties t a b h hab with ha | hb
    · by_cases hb : b.1 = (0 : Site d)
      · rw [hfix a ha, hfix b hb]
      · exact labelLT_permLabel_of_fst_ne (by rw [ha]; exact fun hh => hb hh.symm)
    · by_cases ha : a.1 = (0 : Site d)
      · rw [hfix a ha, hfix b hb]
      · exact labelLT_permLabel_of_fst_ne (by rw [hb]; exact ha)

/-- The same for a relabelled driver, whose ties are those of the original one
read at the permuted labels. -/
theorem tieInvariant_of_base_ties {x₀ : Site d} {σ : Equiv.Perm ℕ} {D' D : PDriver d}
    (hx₀ : x₀ ≠ (0 : Site d)) (hD : RelabelDriver x₀ σ D' D)
    (hties : ∀ (s : ℕ) (a b : Label d), D.rank (a, s) = D.rank (b, s) → a ≠ b →
      a.1 = (0 : Site d) ∨ b.1 = (0 : Site d)) :
    TieInvariant x₀ σ D' := by
  refine tieInvariant_of_ties_at_origin hx₀ ?_
  intro s a b h hab
  rw [hD.rank a s, hD.rank b s] at h
  have hab' : permLabel x₀ σ a ≠ permLabel x₀ σ b := fun hh =>
    hab ((permLabelEquiv x₀ σ).injective hh)
  exact hties s (permLabel x₀ σ a) (permLabel x₀ σ b) h hab'

/-- **Every tie in the grafted realization involves a label at the origin.**  Off
the origin the grafted uniform variables are those of `ω`, read at distinct
labels. -/
theorem graft_tie_origin {ω ω₁ : PData d} (hinj : Function.Injective ω.2.2) (s : ℕ)
    {p q : Label d} (h : (toPDriver (graftOrigin ω₁ ω)).rank (p, s)
      = (toPDriver (graftOrigin ω₁ ω)).rank (q, s)) (hpq : p ≠ q) :
    p.1 = (0 : Site d) ∨ q.1 = (0 : Site d) := by
  by_cases hp : p.1 = (0 : Site d)
  · exact Or.inl hp
  by_cases hq : q.1 = (0 : Site d)
  · exact Or.inr hq
  exfalso
  have hrp : (toPDriver (graftOrigin ω₁ ω)).rank (p, s) = ω.2.2 (p, s) :=
    graftOrigin_rank_of_ne (q := (p, s)) hp ω₁ ω
  have hrq : (toPDriver (graftOrigin ω₁ ω)).rank (q, s) = ω.2.2 (q, s) :=
    graftOrigin_rank_of_ne (q := (q, s)) hq ω₁ ω
  rw [hrp, hrq] at h
  exact hpq (congrArg Prod.fst (hinj h))

/-- **Every tie in the tagged grafted realization involves a label at the
origin.** -/
theorem graftTagged_tie_origin (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) {ω ω₁ : PData d}
    (hinj : Function.Injective ω.2.2) (s : ℕ) {p q : Label d}
    (h : (taggedDriver w r (graftOrigin ω₁ ω)).rank (p, s)
      = (taggedDriver w r (graftOrigin ω₁ ω)).rank (q, s)) (hpq : p ≠ q) :
    p.1 = (0 : Site d) ∨ q.1 = (0 : Site d) := by
  by_cases hp : p.1 = (0 : Site d)
  · exact Or.inl hp
  by_cases hq : q.1 = (0 : Site d)
  · exact Or.inr hq
  exfalso
  have hp0 : p ≠ ((0 : Site d), 0) := fun hh => hp (congrArg Prod.fst hh)
  have hq0 : q ≠ ((0 : Site d), 0) := fun hh => hq (congrArg Prod.fst hh)
  have hsp : taggedSource p = p := by unfold taggedSource; rw [if_neg hp]
  have hsq : taggedSource q = q := by unfold taggedSource; rw [if_neg hq]
  have hrp : (taggedDriver w r (graftOrigin ω₁ ω)).rank (p, s)
      = (graftOrigin ω₁ ω).2.2 (taggedSource p, s) :=
    taggedRank_apply_of_ne r (graftOrigin ω₁ ω).2.2 p s hp0
  have hrq : (taggedDriver w r (graftOrigin ω₁ ω)).rank (q, s)
      = (graftOrigin ω₁ ω).2.2 (taggedSource q, s) :=
    taggedRank_apply_of_ne r (graftOrigin ω₁ ω).2.2 q s hq0
  rw [hrp, hrq, hsp, hsq, graftOrigin_rank_of_ne (q := (p, s)) hp,
    graftOrigin_rank_of_ne (q := (q, s)) hq] at h
  exact hpq (congrArg Prod.fst (hinj h))

/-- **Relabeling the particles at a site other than the origin leaves the hole
counts of the grafted realization alone.** -/
theorem pHoleCount_graft_relabelAt {x₀ : Site d} {σ : Equiv.Perm ℕ} {ω ω₁ : PData d}
    (hx₀ : x₀ ≠ (0 : Site d)) (hσ : ∀ i, (ω.1 x₀).toNat ≤ i → σ i = i)
    (hinj : Function.Injective ω.2.2) (t : ℕ) (x : Site d) :
    pHoleCount (toPDriver (relabelAt x₀ σ (graftOrigin ω₁ ω))) t x
      = pHoleCount (toPDriver (graftOrigin ω₁ ω)) t x := by
  have hD := relabelDriver_relabelAt x₀ σ (graftOrigin ω₁ ω)
  have hσ' : ∀ i, ((toPDriver (graftOrigin ω₁ ω)).eta x₀).toNat ≤ i → σ i = i := by
    intro i hi
    refine hσ i ?_
    have heta : (toPDriver (graftOrigin ω₁ ω)).eta x₀ = ω.1 x₀ :=
      graftOrigin_eta_of_ne hx₀ ω₁ ω
    rwa [heta] at hi
  exact (pState_perm hD hσ' (tieInvariant_of_base_ties hx₀ hD
    fun s a b h hab => graft_tie_origin hinj s h hab) t).holes x

/-- **The tagged particle's activity in the grafted realization is unchanged by
relabeling the particles at a site other than the origin.** -/
theorem taggedActive_graft_relabelAt (w : ℕ → Fin d × Bool) (r : ℕ → ℝ) {x₀ : Site d}
    {σ : Equiv.Perm ℕ} {ω ω₁ : PData d} (hx₀ : x₀ ≠ (0 : Site d))
    (hσ : ∀ i, (ω.1 x₀).toNat ≤ i → σ i = i) (hinj : Function.Injective ω.2.2) (t : ℕ) :
    (pState (taggedDriver w r (relabelAt x₀ σ (graftOrigin ω₁ ω))) t).active
        ((0 : Site d), 0)
      = (pState (taggedDriver w r (graftOrigin ω₁ ω)) t).active ((0 : Site d), 0) := by
  have hD := relabelDriver_tagged_ne w r hx₀ σ (graftOrigin ω₁ ω)
  have hfix : permLabel x₀ σ ((0 : Site d), 0) = ((0 : Site d), 0) := by
    simp only [permLabel, if_neg (fun hh : (0 : Site d) = x₀ => hx₀ hh.symm)]
  have hσ' : ∀ i, ((taggedDriver w r (graftOrigin ω₁ ω)).eta x₀).toNat ≤ i → σ i = i := by
    intro i hi
    refine hσ i ?_
    have heta : (taggedDriver w r (graftOrigin ω₁ ω)).eta x₀ = ω.1 x₀ := by
      show addParticle (0 : Site d) (graftOrigin ω₁ ω).1 x₀ = ω.1 x₀
      rw [addParticle, if_neg hx₀]
      exact graftOrigin_eta_of_ne hx₀ ω₁ ω
    rwa [heta] at hi
  have h := (pState_perm hD hσ' (tieInvariant_of_base_ties hx₀ hD
    fun s a b h hab => graftTagged_tie_origin w r hinj s h hab) t).active ((0 : Site d), 0)
  rw [h, hfix]

end Parking

end
