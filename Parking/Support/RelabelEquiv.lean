/-
The equivariance of the particle-driven construction under relabeling the
particles at one site.

`relabelAt x₀ σ` carries the walk and the uniform variables of the label
`(x₀, i)` to the label `(x₀, σ i)`.  When `σ` fixes every index at or above the
count at `x₀` it permutes the particles PRESENT there, and the whole process is
then carried along: the state of the relabelled realization is the state of the
original one read at the permuted labels, and the holes, the departures and the
counts at every site are unchanged.

The one place where the two realizations could differ is the tie-break of
`pSettles`, which orders two arrivals of equal rank by their labels.  On the set
where the uniform variables are pairwise distinct that clause never fires, so the
equivariance holds there; the set of realizations with a repeated uniform
variable is null.
-/
import Parking.Support.Relabel

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- The permutation of labels induced by `σ` at the site `x₀`. -/
def permLabel (x₀ : Site d) (σ : Equiv.Perm ℕ) (p : Label d) : Label d :=
  (p.1, if p.1 = x₀ then σ p.2 else p.2)

/-- `permLabel` as a permutation of the labels. -/
def permLabelEquiv (x₀ : Site d) (σ : Equiv.Perm ℕ) : Equiv.Perm (Label d) where
  toFun := permLabel x₀ σ
  invFun := permLabel x₀ σ.symm
  left_inv := by
    rintro ⟨x, i⟩
    by_cases h : x = x₀
    · subst h; simp only [permLabel, Equiv.symm_apply_apply, if_pos]
    · simp only [permLabel, if_neg h]
  right_inv := by
    rintro ⟨x, i⟩
    by_cases h : x = x₀
    · subst h; simp only [permLabel, Equiv.apply_symm_apply, if_pos]
    · simp only [permLabel, if_neg h]

@[simp] theorem permLabelEquiv_apply (x₀ : Site d) (σ : Equiv.Perm ℕ) (p : Label d) :
    permLabelEquiv x₀ σ p = permLabel x₀ σ p := rfl

@[simp] theorem permLabelEquiv_symm_apply (x₀ : Site d) (σ : Equiv.Perm ℕ) (p : Label d) :
    (permLabelEquiv x₀ σ).symm p = permLabel x₀ σ.symm p := rfl

@[simp] theorem permLabel_fst (x₀ : Site d) (σ : Equiv.Perm ℕ) (p : Label d) :
    (permLabel x₀ σ p).1 = p.1 := rfl

/-- The relabelled driver, described against the original one. -/
structure RelabelDriver (x₀ : Site d) (σ : Equiv.Perm ℕ) (D' D : PDriver d) : Prop where
  /-- The counts are untouched. -/
  eta : ∀ x, D'.eta x = D.eta x
  /-- The walk of a label is the walk of its image. -/
  move : ∀ (p : Label d) (t : ℕ), D'.move (p, t) = D.move (permLabel x₀ σ p, t)
  /-- The uniform variable of a label is that of its image. -/
  rank : ∀ (p : Label d) (t : ℕ), D'.rank (p, t) = D.rank (permLabel x₀ σ p, t)

/-- The state of the relabelled realization, described against the original one. -/
structure RelabelState (x₀ : Site d) (σ : Equiv.Perm ℕ) (S' S : State d) : Prop where
  /-- A label is active exactly when its image is. -/
  active : ∀ p, S'.active p = S.active (permLabel x₀ σ p)
  /-- A label stands where its image stands. -/
  pos : ∀ p, S'.pos p = S.pos (permLabel x₀ σ p)
  /-- The holes are unchanged. -/
  holes : ∀ x, S'.holes x = S.holes x
  /-- The departures are unchanged. -/
  departures : ∀ x, S'.departures x = S.departures x

/-- A permutation that fixes every index at or above `m` maps the indices below
`m` onto themselves. -/
theorem perm_lt_iff {σ : Equiv.Perm ℕ} {m : ℕ} (hσ : ∀ i, m ≤ i → σ i = i) (i : ℕ) :
    σ i < m ↔ i < m := by
  constructor
  · intro h
    by_contra hi
    rw [hσ i (Nat.le_of_not_lt hi)] at h
    omega
  · intro h
    by_contra hs
    have h2 : σ (σ i) = σ i := hσ (σ i) (Nat.le_of_not_lt hs)
    have h3 : σ i = i := σ.injective h2
    omega

/-- With pairwise distinct uniform variables the tie-break of `pSettles` never
fires: two arrivals of equal rank in the same round are the same particle. -/
theorem prec_iff_of_injective {D : PDriver d} (hinj : Function.Injective D.rank)
    (t : ℕ) (p q : Label d) :
    (D.rank (q, t) < D.rank (p, t) ∨ (D.rank (q, t) = D.rank (p, t) ∧ labelLT q p))
      ↔ D.rank (q, t) < D.rank (p, t) := by
  constructor
  · rintro (h | ⟨heq, hlt⟩)
    · exact h
    · have hqp : q = p := congrArg Prod.fst (hinj heq)
      exact absurd (hqp ▸ hlt) (LatticeProb.labelLT_irrefl p)
  · exact Or.inl

/-- Every tie among the uniform variables of `D'` at a round is decided by data
the relabeling does not move: two labels of equal uniform variable compare the
same way before and after the permutation.  Pairwise distinct uniform variables
give this for nothing, and the tagged driver has it on the set where the
uniform variables of the realization are pairwise distinct, because there every
tie involves the tagged label and one other, and the site-major label order
decides such a tie by the sites alone, or at the origin by the index of a label
the permutation fixes. -/
def TieInvariant (x₀ : Site d) (σ : Equiv.Perm ℕ) (D' : PDriver d) : Prop :=
  ∀ (t : ℕ) (a b : Label d), D'.rank (a, t) = D'.rank (b, t) →
    (labelLT a b ↔ labelLT (permLabel x₀ σ a) (permLabel x₀ σ b))

/-- Pairwise distinct uniform variables decide every tie trivially: a tie is
then a label compared with itself. -/
theorem tieInvariant_of_injective {x₀ : Site d} {σ : Equiv.Perm ℕ} {D' : PDriver d}
    (hinj : Function.Injective D'.rank) : TieInvariant x₀ σ D' := by
  intro t a b h
  have hab : a = b := congrArg Prod.fst (hinj h)
  subst hab
  constructor
  · intro h1; exact absurd h1 (LatticeProb.labelLT_irrefl a)
  · intro h1; exact absurd h1 (LatticeProb.labelLT_irrefl _)

variable {x₀ : Site d} {σ : Equiv.Perm ℕ} {D' D : PDriver d} {S' S : State d}

/-- Relabeling the particles present at `x₀` permutes the candidates. -/
theorem mem_candidates_perm {η : Site d → ℤ}
    (hσ : ∀ i, (η x₀).toNat ≤ i → σ i = i) (y : Site d) (r : ℕ) (p : Label d) :
    permLabel x₀ σ p ∈ candidates η y r ↔ p ∈ candidates η y r := by
  rw [LatticeProb.mem_candidates_iff, LatticeProb.mem_candidates_iff]
  have hfst : (permLabel x₀ σ p).1 = p.1 := rfl
  rw [hfst]
  by_cases h : p.1 = x₀
  · have hsnd : (permLabel x₀ σ p).2 = σ p.2 := by simp only [permLabel, if_pos h]
    rw [hsnd, h]
    exact and_congr_right fun _ => perm_lt_iff hσ p.2
  · have hsnd : (permLabel x₀ σ p).2 = p.2 := by simp only [permLabel, if_neg h]
    rw [hsnd]

/-- The relabelled driver again has pairwise distinct uniform variables. -/
theorem injective_rank_of_relabel (hD : RelabelDriver x₀ σ D' D)
    (hinj : Function.Injective D.rank) : Function.Injective D'.rank := by
  rintro ⟨p, t⟩ ⟨q, s⟩ h
  rw [hD.rank p t, hD.rank q s] at h
  have h2 : (permLabel x₀ σ p, t) = (permLabel x₀ σ q, s) := hinj h
  have hp : permLabel x₀ σ p = permLabel x₀ σ q := congrArg Prod.fst h2
  have ht : t = s := congrArg Prod.snd h2
  have hpq : p = q := (permLabelEquiv x₀ σ).injective hp
  rw [hpq, ht]

/-- The active particles at a site are permuted. -/
theorem mem_pActiveAt_perm (hD : RelabelDriver x₀ σ D' D) (hS : RelabelState x₀ σ S' S)
    (hσ : ∀ i, (D.eta x₀).toNat ≤ i → σ i = i) (t : ℕ) (y : Site d) (p : Label d) :
    p ∈ pActiveAt D' S' t y ↔ permLabel x₀ σ p ∈ pActiveAt D S t y := by
  have hη : D'.eta = D.eta := funext hD.eta
  simp only [pActiveAt, Finset.mem_filter, hη, hS.active p, hS.pos p]
  rw [mem_candidates_perm hσ y t p]

/-- A label steps to where its image steps. -/
theorem pNextPos_perm (hD : RelabelDriver x₀ σ D' D) (hS : RelabelState x₀ σ S' S)
    (t : ℕ) (p : Label d) :
    pNextPos D' S' t p = pNextPos D S t (permLabel x₀ σ p) := by
  simp only [pNextPos, hS.active p, hS.pos p, hD.move p t]

/-- The number of active particles at a site is unchanged. -/
theorem card_pActiveAt_perm (hD : RelabelDriver x₀ σ D' D) (hS : RelabelState x₀ σ S' S)
    (hσ : ∀ i, (D.eta x₀).toNat ≤ i → σ i = i) (t : ℕ) (y : Site d) :
    (pActiveAt D' S' t y).card = (pActiveAt D S t y).card := by
  have h : pActiveAt D' S' t y
      = (pActiveAt D S t y).map (permLabelEquiv x₀ σ).symm.toEmbedding := by
    ext b
    rw [Finset.mem_map_equiv]
    simpa using mem_pActiveAt_perm hD hS hσ t y b
  rw [h, Finset.card_map]

/-- The particles arriving at a site are permuted. -/
theorem mem_pArrivalsAt_perm (hD : RelabelDriver x₀ σ D' D) (hS : RelabelState x₀ σ S' S)
    (hσ : ∀ i, (D.eta x₀).toNat ≤ i → σ i = i) (t : ℕ) (x : Site d) (p : Label d) :
    p ∈ pArrivalsAt D' S' t x ↔ permLabel x₀ σ p ∈ pArrivalsAt D S t x := by
  have hη : D'.eta = D.eta := funext hD.eta
  simp only [pArrivalsAt, Finset.mem_filter, hη, hS.active p, pNextPos_perm hD hS t p]
  rw [mem_candidates_perm hσ x (t + 1) p]

/-- The number of arrivals at a site is unchanged. -/
theorem card_pArrivalsAt_perm (hD : RelabelDriver x₀ σ D' D) (hS : RelabelState x₀ σ S' S)
    (hσ : ∀ i, (D.eta x₀).toNat ≤ i → σ i = i) (t : ℕ) (x : Site d) :
    (pArrivalsAt D' S' t x).card = (pArrivalsAt D S t x).card := by
  have h : pArrivalsAt D' S' t x
      = (pArrivalsAt D S t x).map (permLabelEquiv x₀ σ).symm.toEmbedding := by
    ext b
    rw [Finset.mem_map_equiv]
    simpa using mem_pArrivalsAt_perm hD hS hσ t x b
  rw [h, Finset.card_map]

/-- The arrivals of smaller rank are permuted: the rank comparison transfers
because the relabelled driver reads the ranks at the permuted labels, and the
tie-break transfers by `TieInvariant`. -/
theorem card_filter_prec_perm (hD : RelabelDriver x₀ σ D' D) (hS : RelabelState x₀ σ S' S)
    (hσ : ∀ i, (D.eta x₀).toNat ≤ i → σ i = i) (htie : TieInvariant x₀ σ D')
    (t : ℕ) (p : Label d) :
    ((pArrivalsAt D' S' t (pNextPos D' S' t p)).filter fun q =>
        D'.rank (q, t) < D'.rank (p, t) ∨
          (D'.rank (q, t) = D'.rank (p, t) ∧ labelLT q p)).card
      = ((pArrivalsAt D S t (pNextPos D S t (permLabel x₀ σ p))).filter fun q =>
        D.rank (q, t) < D.rank (permLabel x₀ σ p, t) ∨
          (D.rank (q, t) = D.rank (permLabel x₀ σ p, t) ∧
            labelLT q (permLabel x₀ σ p))).card := by
  classical
  have hz : pNextPos D' S' t p = pNextPos D S t (permLabel x₀ σ p) := pNextPos_perm hD hS t p
  rw [hz]
  have hmap : ((pArrivalsAt D' S' t (pNextPos D S t (permLabel x₀ σ p))).filter fun q =>
        D'.rank (q, t) < D'.rank (p, t) ∨
          (D'.rank (q, t) = D'.rank (p, t) ∧ labelLT q p))
      = (((pArrivalsAt D S t (pNextPos D S t (permLabel x₀ σ p))).filter fun q =>
        D.rank (q, t) < D.rank (permLabel x₀ σ p, t) ∨
          (D.rank (q, t) = D.rank (permLabel x₀ σ p, t) ∧
            labelLT q (permLabel x₀ σ p)))).map
          (permLabelEquiv x₀ σ).symm.toEmbedding := by
    ext b
    rw [Finset.mem_map_equiv]
    have hmem := mem_pArrivalsAt_perm hD hS hσ t (pNextPos D S t (permLabel x₀ σ p)) b
    have hrb : D'.rank (b, t) = D.rank (permLabel x₀ σ b, t) := hD.rank b t
    have hrp : D'.rank (p, t) = D.rank (permLabel x₀ σ p, t) := hD.rank p t
    simp only [Equiv.symm_symm, permLabelEquiv_apply, Finset.mem_filter]
    rw [hmem, hrb, hrp]
    refine and_congr_right fun _ => ?_
    refine or_congr Iff.rfl (and_congr_right fun heq => ?_)
    exact htie t b p (by rw [hrb, hrp]; exact heq)
  rw [hmap, Finset.card_map]

/-- A label settles exactly when its image settles. -/
theorem pSettles_perm (hD : RelabelDriver x₀ σ D' D) (hS : RelabelState x₀ σ S' S)
    (hσ : ∀ i, (D.eta x₀).toNat ≤ i → σ i = i) (htie : TieInvariant x₀ σ D')
    (t : ℕ) (p : Label d) :
    pSettles D' S' t p = pSettles D S t (permLabel x₀ σ p) := by
  have hz : pNextPos D' S' t p = pNextPos D S t (permLabel x₀ σ p) := pNextPos_perm hD hS t p
  have hholes : S'.holes (pNextPos D' S' t p)
      = S.holes (pNextPos D S t (permLabel x₀ σ p)) := by rw [hS.holes, hz]
  simp only [pSettles, hS.active p, card_filter_prec_perm hD hS hσ htie t p, hholes]

/-- One round carries the description of the relabelled state along. -/
theorem pStep_perm (hD : RelabelDriver x₀ σ D' D) (hS : RelabelState x₀ σ S' S)
    (hσ : ∀ i, (D.eta x₀).toNat ≤ i → σ i = i) (htie : TieInvariant x₀ σ D')
    (t : ℕ) : RelabelState x₀ σ (pStep D' S' t) (pStep D S t) := by
  refine ⟨fun p => ?_, fun p => ?_, fun x => ?_, fun y => ?_⟩
  · simp only [pStep, hS.active p, pSettles_perm hD hS hσ htie t p]
  · exact pNextPos_perm hD hS t p
  · simp only [pStep, hS.holes x, card_pArrivalsAt_perm hD hS hσ t x]
  · simp only [pStep, hS.departures y, card_pActiveAt_perm hD hS hσ t y]

/-- **The particle-driven construction is equivariant under relabeling the
particles present at one site.**  The state of the relabelled realization is the
state of the original one read at the permuted labels; the holes, the departures
and the counts at every site are unchanged. -/
theorem pState_perm (hD : RelabelDriver x₀ σ D' D)
    (hσ : ∀ i, (D.eta x₀).toNat ≤ i → σ i = i) (htie : TieInvariant x₀ σ D')
    (t : ℕ) : RelabelState x₀ σ (pState D' t) (pState D t) := by
  induction t with
  | zero =>
    have hη : D'.eta = D.eta := funext hD.eta
    refine ⟨fun p => ?_, fun p => ?_, fun x => ?_, fun _ => rfl⟩
    · simp only [pState, LatticeProb.initial, hη]
      by_cases h : p.1 = x₀
      · have h2 : (permLabel x₀ σ p).2 = σ p.2 := by simp only [permLabel, if_pos h]
        have h1 : (permLabel x₀ σ p).1 = p.1 := rfl
        rw [h1, h2, h]
        exact decide_eq_decide.mpr (perm_lt_iff hσ p.2).symm
      · have h2 : (permLabel x₀ σ p).2 = p.2 := by simp only [permLabel, if_neg h]
        have h1 : (permLabel x₀ σ p).1 = p.1 := rfl
        rw [h1, h2]
    · rfl
    · simp only [pState, LatticeProb.initial, hη]
  | succ t ih => exact pStep_perm hD ih hσ htie t

/-- `relabelAt` builds exactly a relabelled driver. -/
theorem relabelDriver_relabelAt (x₀ : Site d) (σ : Equiv.Perm ℕ) (ω : PData d) :
    RelabelDriver x₀ σ (toPDriver (relabelAt x₀ σ ω)) (toPDriver ω) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- With pairwise distinct uniform variables the relabelled realization has the
tie-invariance for nothing. -/
theorem tieInvariant_relabelAt (x₀ : Site d) (σ : Equiv.Perm ℕ) {ω : PData d}
    (hinj : Function.Injective ω.2.2) :
    TieInvariant x₀ σ (toPDriver (relabelAt x₀ σ ω)) :=
  tieInvariant_of_injective (injective_rank_of_relabel (relabelDriver_relabelAt x₀ σ ω) hinj)

section Realization

variable {x₀ : Site d} {σ : Equiv.Perm ℕ} {ω : PData d}
  (hσ : ∀ i, (ω.1 x₀).toNat ≤ i → σ i = i) (hinj : Function.Injective ω.2.2)

include hσ hinj

/-- A label is active in the relabelled realization exactly when its image is
active in the original one. -/
theorem pState_active_relabelAt (t : ℕ) (p : Label d) :
    (pState (toPDriver (relabelAt x₀ σ ω)) t).active p
      = (pState (toPDriver ω) t).active (permLabel x₀ σ p) :=
  (pState_perm (relabelDriver_relabelAt x₀ σ ω) hσ (tieInvariant_relabelAt x₀ σ hinj) t).active p

/-- Relabeling the particles present at a site leaves every hole count alone. -/
theorem pHoleCount_relabelAt (t : ℕ) (x : Site d) :
    pHoleCount (toPDriver (relabelAt x₀ σ ω)) t x = pHoleCount (toPDriver ω) t x :=
  (pState_perm (relabelDriver_relabelAt x₀ σ ω) hσ (tieInvariant_relabelAt x₀ σ hinj) t).holes x

/-- Relabeling the particles present at a site leaves every count of active
particles alone. -/
theorem pActiveCount_relabelAt (t : ℕ) (x : Site d) :
    pActiveCount (toPDriver (relabelAt x₀ σ ω)) t x = pActiveCount (toPDriver ω) t x :=
  card_pActiveAt_perm (relabelDriver_relabelAt x₀ σ ω)
    (pState_perm (relabelDriver_relabelAt x₀ σ ω) hσ (tieInvariant_relabelAt x₀ σ hinj) t) hσ t x

/-- Relabeling the particles present at a site leaves the odometer alone. -/
theorem pOdometer_relabelAt (t : ℕ) (x : Site d) :
    pOdometer (toPDriver (relabelAt x₀ σ ω)) t x = pOdometer (toPDriver ω) t x :=
  (pState_perm (relabelDriver_relabelAt x₀ σ ω) hσ (tieInvariant_relabelAt x₀ σ hinj) t).departures x

end Realization

end Parking

end
