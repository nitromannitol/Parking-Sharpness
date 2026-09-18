/-
Exchangeability of the particles at the origin.

`lem:transport` asserts that, conditionally on `η(0) = k`, the `k` particles at
the origin are exchangeable.  In the stack construction they are not: the
instruction a particle reads at a site is the odometer there plus its rank
among the co-departing labels, so permuting the labels at the origin changes
which instruction each of them reads.  In the particle-driven construction the
permutation is a relabelling of two independent families, the displacements and
the uniform variables, and the process commutes with it.

It commutes with it EXCEPT at ties among the uniform variables, which the
settling rule breaks by the label order and which a relabelling does not
preserve.  Ties are a null event, and `NoTies` is the pathwise hypothesis under
which the commutation holds.
-/
import LatticeProb.Prob.FiniteMarginal
import Parking.Support.ConfMonotone
import Parking.Support.DensityCompare

noncomputable section

open MeasureTheory

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-- Relabelling the particles at the origin by a permutation of their indices. -/
def relabel (σ : Equiv.Perm ℕ) (p : Label d) : Label d :=
  if p.1 = 0 then (0, σ p.2) else p

theorem relabel_fst (σ : Equiv.Perm ℕ) (p : Label d) : (relabel σ p).1 = p.1 := by
  unfold relabel
  split
  · simp_all
  · rfl

theorem relabel_relabel (σ : Equiv.Perm ℕ) (p : Label d) :
    relabel σ⁻¹ (relabel σ p) = p := by
  unfold relabel
  by_cases h : p.1 = 0
  · simp only [h, if_pos]
    exact Prod.ext h.symm (by simp)
  · simp [h]

theorem relabel_relabel' (σ : Equiv.Perm ℕ) (p : Label d) :
    relabel σ (relabel σ⁻¹ p) = p := by
  unfold relabel
  by_cases h : p.1 = 0
  · simp only [h, if_pos]
    exact Prod.ext h.symm (by simp)
  · simp [h]

theorem relabel_origin (σ : Equiv.Perm ℕ) (i : ℕ) :
    relabel σ (((0 : Site d), i) : Label d) = (0, σ i) := by
  unfold relabel
  simp

theorem relabel_injective (σ : Equiv.Perm ℕ) :
    Function.Injective (relabel (d := d) σ) := by
  intro p q h
  have := congrArg (relabel σ⁻¹) h
  rwa [relabel_relabel, relabel_relabel] at this

/-- A permutation fixing every index at least `k` permutes the indices below
`k`. -/
theorem lt_iff_perm_lt {σ : Equiv.Perm ℕ} {k : ℕ} (hk : ∀ i, k ≤ i → σ i = i) (i : ℕ) :
    i < k ↔ σ i < k := by
  constructor
  · intro hi
    by_contra hc
    rw [not_lt] at hc
    have := hk (σ i) hc
    have : σ i = i := by
      have h2 : σ (σ i) = σ i := this
      exact σ.injective h2
    omega
  · intro hi
    by_contra hc
    rw [not_lt] at hc
    rw [hk i hc] at hi
    omega

/-- The index condition defining the candidates is invariant under the
relabelling, on a configuration whose value at the origin is `k`. -/
theorem relabel_lt_toNat {σ : Equiv.Perm ℕ} {k : ℕ} (hk : ∀ i, k ≤ i → σ i = i)
    {η : Site d → ℤ} (heta : (η 0).toNat = k) (p : Label d) :
    (p.2 < (η p.1).toNat) ↔ ((relabel σ p).2 < (η p.1).toNat) := by
  unfold relabel
  by_cases h : p.1 = 0
  · rw [if_pos h]
    simp only
    rw [h, heta]
    exact lt_iff_perm_lt hk p.2
  · rw [if_neg h]

/-- The candidate sets are invariant under the relabelling, on a configuration
whose value at the origin is `k`. -/
theorem mem_candidates_relabel {σ : Equiv.Perm ℕ} {k : ℕ} (hk : ∀ i, k ≤ i → σ i = i)
    {η : Site d → ℤ} (heta : (η 0).toNat = k) (y : Site d) (r : ℕ) (p : Label d) :
    p ∈ candidates η y r ↔ relabel σ p ∈ candidates η y r := by
  rw [mem_candidates_iff, mem_candidates_iff, relabel_fst]
  exact and_congr Iff.rfl (relabel_lt_toNat hk heta p)

/-- The driver with the displacements and the uniform variables of the origin
particles permuted. -/
def relabelDriver (σ : Equiv.Perm ℕ) (D : LatticeProb.PDriver d) : LatticeProb.PDriver d where
  eta := D.eta
  move := fun q => D.move (relabel σ q.1, q.2)
  rank := fun q => D.rank (relabel σ q.1, q.2)

/-- No two particles draw the same uniform variable in the same round. -/
def NoTies (D : LatticeProb.PDriver d) : Prop :=
  ∀ (t : ℕ) (p q : Label d), p ≠ q → D.rank (p, t) ≠ D.rank (q, t)

theorem noTies_relabel (σ : Equiv.Perm ℕ) {D : LatticeProb.PDriver d} (h : NoTies D) :
    NoTies (relabelDriver σ D) := by
  intro t p q hpq
  exact h t _ _ fun hc => hpq (relabel_injective σ hc)

/-- Counting a relabelled filter. -/
theorem card_filter_relabel (σ : Equiv.Perm ℕ) (s s' : Finset (Label d))
    (hs : ∀ p, p ∈ s ↔ relabel σ p ∈ s') (P Q : Label d → Prop)
    [DecidablePred P] [DecidablePred Q] (hPQ : ∀ p, P p ↔ Q (relabel σ p)) :
    (s.filter P).card = (s'.filter Q).card := by
  refine Finset.card_nbij' (relabel σ) (relabel σ⁻¹) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter] at hp ⊢
    exact ⟨(hs p).mp hp.1, (hPQ p).mp hp.2⟩
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter] at hp ⊢
    have hmem : relabel σ (relabel σ⁻¹ p) ∈ s' := by rw [relabel_relabel']; exact hp.1
    refine ⟨(hs _).mpr hmem, ?_⟩
    refine (hPQ (relabel σ⁻¹ p)).mpr ?_
    rw [relabel_relabel']
    exact hp.2
  · intro p _
    exact relabel_relabel σ p
  · intro p _
    exact relabel_relabel' σ p

/-! ### The relabelled process -/

/-- **The particle-driven process commutes with the relabelling.**  Away from
ties among the uniform variables, the state of the relabelled driver is the
state of the driver read at the relabelled particles. -/
theorem pState_relabel {σ : Equiv.Perm ℕ} {k : ℕ} (hk : ∀ i, k ≤ i → σ i = i)
    {D : LatticeProb.PDriver d} (heta : (D.eta 0).toNat = k) (hnt : NoTies D) :
    ∀ t : ℕ,
      (∀ p : Label d, (LatticeProb.pState (relabelDriver σ D) t).active p
          = (LatticeProb.pState D t).active (relabel σ p)) ∧
      (∀ p : Label d, (LatticeProb.pState (relabelDriver σ D) t).pos p
          = (LatticeProb.pState D t).pos (relabel σ p)) ∧
      (∀ x : Site d, (LatticeProb.pState (relabelDriver σ D) t).holes x
          = (LatticeProb.pState D t).holes x) := by
  classical
  intro t
  induction t with
  | zero =>
      refine ⟨fun p => ?_, fun p => ?_, fun x => rfl⟩
      · show decide (p.2 < ((relabelDriver σ D).eta p.1).toNat)
            = decide ((relabel σ p).2 < (D.eta (relabel σ p).1).toNat)
        rw [relabel_fst]
        exact decide_eq_decide.mpr (relabel_lt_toNat hk heta p)
      · exact (relabel_fst σ p).symm
  | succ t ih =>
      obtain ⟨iha, ihp, ihh⟩ := ih
      have hnext : ∀ p : Label d,
          LatticeProb.pNextPos (relabelDriver σ D)
              (LatticeProb.pState (relabelDriver σ D) t) t p
            = LatticeProb.pNextPos D (LatticeProb.pState D t) t (relabel σ p) := by
        intro p
        show (if (LatticeProb.pState (relabelDriver σ D) t).active p
              then (LatticeProb.pState (relabelDriver σ D) t).pos p
                + D.move (relabel σ p, t)
              else (LatticeProb.pState (relabelDriver σ D) t).pos p)
            = (if (LatticeProb.pState D t).active (relabel σ p)
              then (LatticeProb.pState D t).pos (relabel σ p) + D.move (relabel σ p, t)
              else (LatticeProb.pState D t).pos (relabel σ p))
        rw [iha p, ihp p]
      have hcand : ∀ (y : Site d) (r : ℕ) (p : Label d),
          p ∈ candidates D.eta y r ↔ relabel σ p ∈ candidates D.eta y r :=
        fun y r p => mem_candidates_relabel hk heta y r p
      have hmemAct : ∀ (y : Site d) (p : Label d),
          p ∈ LatticeProb.pActiveAt (relabelDriver σ D)
              (LatticeProb.pState (relabelDriver σ D) t) t y
            ↔ relabel σ p ∈ LatticeProb.pActiveAt D (LatticeProb.pState D t) t y := by
        intro y p
        simp only [LatticeProb.pActiveAt, Finset.mem_filter]
        rw [iha p, ihp p]
        exact and_congr (hcand y t p) Iff.rfl
      have hmemArr : ∀ (x : Site d) (p : Label d),
          p ∈ LatticeProb.pArrivalsAt (relabelDriver σ D)
              (LatticeProb.pState (relabelDriver σ D) t) t x
            ↔ relabel σ p ∈ LatticeProb.pArrivalsAt D (LatticeProb.pState D t) t x := by
        intro x p
        simp only [LatticeProb.pArrivalsAt, Finset.mem_filter]
        rw [iha p, hnext p]
        exact and_congr (hcand x (t + 1) p) Iff.rfl
      have hcardAct : ∀ y : Site d,
          (LatticeProb.pActiveAt (relabelDriver σ D)
            (LatticeProb.pState (relabelDriver σ D) t) t y).card
            = (LatticeProb.pActiveAt D (LatticeProb.pState D t) t y).card := by
        intro y
        refine card_filter_relabel σ _ _ (hcand y t) _ _ fun p => ?_
        rw [iha p, ihp p]
      have hcardArr : ∀ x : Site d,
          (LatticeProb.pArrivalsAt (relabelDriver σ D)
            (LatticeProb.pState (relabelDriver σ D) t) t x).card
            = (LatticeProb.pArrivalsAt D (LatticeProb.pState D t) t x).card := by
        intro x
        refine card_filter_relabel σ _ _ (hcand x (t + 1)) _ _ fun p => ?_
        rw [iha p, hnext p]
      have hsettle : ∀ p : Label d,
          LatticeProb.pSettles (relabelDriver σ D)
              (LatticeProb.pState (relabelDriver σ D) t) t p
            = LatticeProb.pSettles D (LatticeProb.pState D t) t (relabel σ p) := by
        intro p
        have hcardF : ((LatticeProb.pArrivalsAt (relabelDriver σ D)
              (LatticeProb.pState (relabelDriver σ D) t) t
                (LatticeProb.pNextPos (relabelDriver σ D)
                  (LatticeProb.pState (relabelDriver σ D) t) t p)).filter
            fun q => (relabelDriver σ D).rank (q, t) < (relabelDriver σ D).rank (p, t) ∨
              ((relabelDriver σ D).rank (q, t) = (relabelDriver σ D).rank (p, t)
                ∧ labelLT q p)).card
            = ((LatticeProb.pArrivalsAt D (LatticeProb.pState D t) t
              (LatticeProb.pNextPos D (LatticeProb.pState D t) t (relabel σ p))).filter
            fun q => D.rank (q, t) < D.rank (relabel σ p, t) ∨
              (D.rank (q, t) = D.rank (relabel σ p, t) ∧ labelLT q (relabel σ p))).card := by
          rw [hnext p]
          refine card_filter_relabel σ _ _ (hmemArr _) _ _ fun q => ?_
          show (D.rank (relabel σ q, t) < D.rank (relabel σ p, t) ∨
              (D.rank (relabel σ q, t) = D.rank (relabel σ p, t) ∧ labelLT q p))
            ↔ (D.rank (relabel σ q, t) < D.rank (relabel σ p, t) ∨
              (D.rank (relabel σ q, t) = D.rank (relabel σ p, t)
                ∧ labelLT (relabel σ q) (relabel σ p)))
          have hno : ¬ (D.rank (relabel σ q, t) = D.rank (relabel σ p, t) ∧ labelLT q p) := by
            rintro ⟨heq, hlt⟩
            have hne : relabel σ q ≠ relabel σ p := by
              intro hc
              exact absurd (relabel_injective σ hc) (fun h => labelLT_irrefl p (h ▸ hlt))
            exact hnt t _ _ hne heq
          have hno' : ¬ (D.rank (relabel σ q, t) = D.rank (relabel σ p, t)
              ∧ labelLT (relabel σ q) (relabel σ p)) := by
            rintro ⟨heq, hlt⟩
            have hne : relabel σ q ≠ relabel σ p := fun hc =>
              labelLT_irrefl (relabel σ p) (hc ▸ hlt)
            exact hnt t _ _ hne heq
          constructor
          · rintro (h | h)
            · exact Or.inl h
            · exact absurd h hno
          · rintro (h | h)
            · exact Or.inl h
            · exact absurd h hno'
        rw [LatticeProb.pSettles, LatticeProb.pSettles, hcardF, hnext p, iha p, ihh _]
      refine ⟨fun p => ?_, fun p => ?_, fun x => ?_⟩
      · rw [pState_succ_active, pState_succ_active, iha p, hsettle p]
      · rw [pState_succ_pos, pState_succ_pos]
        exact hnext p
      · rw [pState_succ_holes, pState_succ_holes, ihh x, hcardArr x]

/-! ### The relabelling preserves the law -/

/-- Reindexing an independent family along an injection leaves its law
unchanged.  This is the exploration lemma with a constant index map. -/
theorem infinitePi_map_inj {ι α : Type*} [MeasurableSpace ι] [Countable ι]
    [MeasurableSingletonClass ι] [DecidableEq ι] [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (e : ι → ι) (he : Function.Injective e) :
    (Measure.infinitePi fun _ : ι => ν).map (fun ω i => ω (e i))
      = Measure.infinitePi fun _ : ι => ν := by
  classical
  have hdag : LatticeProb.IsDagExploration (X := fun _ : ι => α) (κ := ι)
      (fun a _ => e a) (fun _ => (∅ : Finset ι)) := by
    refine ⟨fun _ => measurable_const, ?_, fun a b _ hab hc => hab (he hc),
      fun _ _ _ _ _ => rfl⟩
    refine WellFounded.intro fun a => Acc.intro a fun b hb => ?_
    exact absurd hb (Finset.notMem_empty b)
  have := LatticeProb.map_revealed_dag (X := fun _ : ι => α) (κ := ι)
    (fun _ : ι => ν) (g := fun _ => id) hdag (fun _ => measurable_id)
    (fun _ => Measure.map_id)
  exact this

/-- The uniform variables of two distinct particles in one round differ almost
surely. -/
theorem rankLaw_ne (a b : Label d × ℕ) (hab : a ≠ b) :
    ∀ᵐ r ∂(LatticeProb.rankLaw d), r a ≠ r b := by
  classical
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  set U : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1) with hU
  have hmeas : Measurable fun r : Label d × ℕ → ℝ => ((r a, r b) : ℝ × ℝ) :=
    (measurable_pi_apply a).prodMk (measurable_pi_apply b)
  have hg2 : Measurable fun x : Fin 2 → ℝ => ((x 0, x 1) : ℝ × ℝ) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have hpair : (LatticeProb.rankLaw d).map (fun r => ((r a, r b) : ℝ × ℝ)) = U.prod U := by
    have hv : Function.Injective (![a, b] : Fin 2 → Label d × ℕ) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have h2 := LatticeProb.infinitePi_map_comp (ι := Label d × ℕ) U (κ := Fin 2) ![a, b] hv
    have hf2 : Measurable fun (r : Label d × ℕ → ℝ) (i : Fin 2) => r (![a, b] i) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply (![a, b] i)
    calc (LatticeProb.rankLaw d).map (fun r => ((r a, r b) : ℝ × ℝ))
        = ((Measure.infinitePi fun _ : Label d × ℕ => U).map
            (fun (r : Label d × ℕ → ℝ) (i : Fin 2) => r (![a, b] i))).map
            (fun x : Fin 2 → ℝ => ((x 0, x 1) : ℝ × ℝ)) := by
          rw [Measure.map_map hg2 hf2]
          rfl
      _ = (Measure.pi fun _ : Fin 2 => U).map
            (fun x : Fin 2 → ℝ => ((x 0, x 1) : ℝ × ℝ)) := by rw [h2]
      _ = U.prod U := by
          have hmp := (MeasureTheory.measurePreserving_piFinTwo fun _ : Fin 2 => U).map_eq
          simpa using hmp
  have hdiag : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hnull : (U.prod U) {p : ℝ × ℝ | p.1 = p.2} = 0 := by
    rw [Measure.prod_apply hdiag]
    have : ∀ x : ℝ, U (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0 := by
      intro x
      have hset : (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = {x} := by
        ext y; simp [eq_comm]
      rw [hset, hU]
      simp
    simp
  refine MeasureTheory.ae_iff.mpr ?_
  have hset : {r : Label d × ℕ → ℝ | ¬ r a ≠ r b}
      = (fun r : Label d × ℕ → ℝ => ((r a, r b) : ℝ × ℝ)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} := by
    ext r; simp
  rw [hset, ← Measure.map_apply hmeas hdiag, hpair, hnull]

/-! ### The relabelling of the data, and its law -/

/-- The driving data with the displacements and the uniform variables of the
origin particles permuted. -/
def relabelData (σ : Equiv.Perm ℕ) (ω : LatticeProb.PData d) : LatticeProb.PData d :=
  (ω.1, (fun q => ω.2.1 (relabel σ q.1, q.2), fun q => ω.2.2 (relabel σ q.1, q.2)))

theorem toPDriver_relabelData (σ : Equiv.Perm ℕ) (ω : LatticeProb.PData d) :
    LatticeProb.toPDriver (relabelData σ ω) = relabelDriver σ (LatticeProb.toPDriver ω) := rfl

theorem measurable_relabelData (σ : Equiv.Perm ℕ) :
    Measurable (relabelData (d := d) σ) :=
  measurable_fst.prodMk
    ((measurable_pi_lambda _ fun q =>
      (measurable_pi_apply (relabel σ q.1, q.2)).comp
        (measurable_fst.comp measurable_snd)).prodMk
      (measurable_pi_lambda _ fun q =>
        (measurable_pi_apply (relabel σ q.1, q.2)).comp
          (measurable_snd.comp measurable_snd)))

theorem prodMap_fst_injective {α β : Type*} (f : α → α) (hf : Function.Injective f) :
    Function.Injective fun q : α × β => (f q.1, q.2) := by
  intro q₁ q₂ h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (hf h.1) h.2

theorem relabelPair_injective (σ : Equiv.Perm ℕ) :
    Function.Injective fun q : Label d × ℕ => (relabel σ q.1, q.2) :=
  prodMap_fst_injective _ (relabel_injective σ)

/-- The relabelling preserves the law of the particle-driven data. -/
theorem map_pLaw_relabelData (hd : 1 ≤ d) (σ : Equiv.Perm ℕ)
    (μ : Measure (Site d → ℤ)) [IsProbabilityMeasure μ] :
    (pLaw d μ).map (relabelData σ) = pLaw d μ := by
  haveI : IsProbabilityMeasure (LatticeProb.displacementLaw d) :=
    LatticeProb.instructionLaw_isProbability hd 0
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  haveI : IsProbabilityMeasure (LatticeProb.moveLaw d) := by
    unfold LatticeProb.moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  have hmove : (LatticeProb.moveLaw d).map
      (fun f : Label d × ℕ → Site d => fun q => f (relabel σ q.1, q.2))
      = LatticeProb.moveLaw d :=
    infinitePi_map_inj _ _ (relabelPair_injective σ)
  have hrank : (LatticeProb.rankLaw d).map
      (fun f : Label d × ℕ → ℝ => fun q => f (relabel σ q.1, q.2))
      = LatticeProb.rankLaw d :=
    infinitePi_map_inj _ _ (relabelPair_injective σ)
  have hmm : Measurable fun (f : Label d × ℕ → Site d) (q : Label d × ℕ) =>
      f (relabel σ q.1, q.2) :=
    measurable_pi_lambda _ fun q => measurable_pi_apply (relabel σ q.1, q.2)
  have hmr : Measurable fun (f : Label d × ℕ → ℝ) (q : Label d × ℕ) =>
      f (relabel σ q.1, q.2) :=
    measurable_pi_lambda _ fun q => measurable_pi_apply (relabel σ q.1, q.2)
  show ((μ.prod ((LatticeProb.moveLaw d).prod (LatticeProb.rankLaw d))).map
    (Prod.map id (Prod.map
      (fun (f : Label d × ℕ → Site d) (q : Label d × ℕ) => f (relabel σ q.1, q.2))
      (fun (f : Label d × ℕ → ℝ) (q : Label d × ℕ) => f (relabel σ q.1, q.2))))
      : Measure (LatticeProb.PData d)) = _
  rw [← Measure.map_prod_map _ _ measurable_id (hmm.prodMap hmr), Measure.map_id,
    ← Measure.map_prod_map _ _ hmm hmr, hmove, hrank]
  rfl

/-- Almost surely no two particles draw the same uniform variable in one
round. -/
theorem ae_noTies (μ : Measure (Site d → ℤ)) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂(pLaw d μ), NoTies (LatticeProb.toPDriver ω) := by
  have hbase : ∀ (t : ℕ) (p q : Label d), p ≠ q →
      ∀ᵐ r ∂(LatticeProb.rankLaw d), r (p, t) ≠ r (q, t) := by
    intro t p q hpq
    exact rankLaw_ne (p, t) (q, t) fun hc => hpq (congrArg Prod.fst hc)
  have hall : ∀ᵐ r ∂(LatticeProb.rankLaw d),
      ∀ (t : ℕ) (p q : Label d), p ≠ q → r (p, t) ≠ r (q, t) := by
    rw [MeasureTheory.ae_all_iff]
    intro t
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro q
    by_cases hpq : p = q
    · subst hpq; filter_upwards with r h; exact absurd rfl h
    · filter_upwards [hbase t p q hpq] with r hr _; exact hr
  exact (Measure.quasiMeasurePreserving_snd).ae
    ((Measure.quasiMeasurePreserving_snd).ae hall)

/-! ### Exchangeability of the particles at the origin -/

theorem map_restrict_comp {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (P : Measure A) {Φ : A → B} (hΦ : Measurable Φ)
    {G : B → C} (hG : Measurable G) {E : Set B} (hE : MeasurableSet E) :
    (P.restrict (Φ ⁻¹' E)).map (fun a => G (Φ a)) = ((P.map Φ).restrict E).map G := by
  rw [Measure.restrict_map hΦ hE, Measure.map_map hG hΦ]
  rfl

theorem map_restrict_of_map_eq {A : Type*} [MeasurableSpace A] (P : Measure A)
    {T : A → A} (hT : Measurable T) (hP : P.map T = P) {E : Set A}
    (hE : MeasurableSet E) (hTE : T ⁻¹' E = E) :
    (P.restrict E).map T = P.restrict E := by
  rw [← hTE, ← Measure.restrict_map hT hE, hP, hTE]

/-- **Exchangeability in the particle-driven construction.**  Conditionally on
`η(0) = k`, permuting the indices of the particles at the origin leaves the
joint law of their activity histories unchanged. -/
theorem exchangeable_particle (hd : 1 ≤ d) (μ : Measure (Site d → ℤ))
    [IsProbabilityMeasure μ] (k : ℕ) (σ : Equiv.Perm ℕ) (hk : ∀ i, k ≤ i → σ i = i) :
    ((pLaw d μ).restrict {ω : LatticeProb.PData d | ω.1 0 = (k : ℤ)}).map
        (fun ω => fun q : ℕ × ℕ =>
          (LatticeProb.pState (LatticeProb.toPDriver ω) q.1).active (0, σ q.2))
      = ((pLaw d μ).restrict {ω : LatticeProb.PData d | ω.1 0 = (k : ℤ)}).map
        (fun ω => fun q : ℕ × ℕ =>
          (LatticeProb.pState (LatticeProb.toPDriver ω) q.1).active (0, q.2)) := by
  classical
  haveI : IsProbabilityMeasure (LatticeProb.displacementLaw d) :=
    LatticeProb.instructionLaw_isProbability hd 0
  haveI : IsProbabilityMeasure (LatticeProb.moveLaw d) := by
    unfold LatticeProb.moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  set A : Set (LatticeProb.PData d) := {ω | ω.1 0 = (k : ℤ)} with hAdef
  have hAmeas : MeasurableSet A := by
    have : A = (fun ω : LatticeProb.PData d => ω.1 0) ⁻¹' {(k : ℤ)} := rfl
    rw [this]
    exact ((measurable_pi_apply (0 : Site d)).comp measurable_fst) (measurableSet_singleton _)
  have hTA : relabelData (d := d) σ ⁻¹' A = A := rfl
  have hG : Measurable fun ω : LatticeProb.PData d => fun q : ℕ × ℕ =>
      (LatticeProb.pState (LatticeProb.toPDriver ω) q.1).active (0, q.2) :=
    measurable_pi_lambda _ fun q => (measurable_pState (d := d) q.1).1 (0, q.2)
  have hstep : ((pLaw d μ).restrict A).map (relabelData σ) = (pLaw d μ).restrict A :=
    map_restrict_of_map_eq _ (measurable_relabelData σ)
      (map_pLaw_relabelData hd σ μ) hAmeas hTA
  have hae : (fun ω : LatticeProb.PData d => fun q : ℕ × ℕ =>
        (LatticeProb.pState (LatticeProb.toPDriver ω) q.1).active (0, σ q.2))
      =ᵐ[(pLaw d μ).restrict A]
      (fun ω : LatticeProb.PData d => fun q : ℕ × ℕ =>
        (LatticeProb.pState (LatticeProb.toPDriver (relabelData σ ω)) q.1).active (0, q.2)) := by
    have hnt : ∀ᵐ ω ∂((pLaw d μ).restrict A), NoTies (LatticeProb.toPDriver ω) :=
      ae_restrict_of_ae (ae_noTies μ)
    filter_upwards [hnt, ae_restrict_mem hAmeas] with ω hntω hmem
    have heta : ((LatticeProb.toPDriver ω).eta 0).toNat = k := by
      show (ω.1 0).toNat = k
      rw [show ω.1 0 = (k : ℤ) from hmem]
      simp
    funext q
    have := (pState_relabel hk heta hntω q.1).1 (0, q.2)
    rw [toPDriver_relabelData, this, relabel_origin]
  calc ((pLaw d μ).restrict A).map (fun ω => fun q : ℕ × ℕ =>
        (LatticeProb.pState (LatticeProb.toPDriver ω) q.1).active (0, σ q.2))
      = ((pLaw d μ).restrict A).map (fun ω => fun q : ℕ × ℕ =>
        (LatticeProb.pState (LatticeProb.toPDriver (relabelData σ ω)) q.1).active (0, q.2)) :=
        Measure.map_congr hae
    _ = (((pLaw d μ).restrict A).map (relabelData σ)).map (fun ω => fun q : ℕ × ℕ =>
        (LatticeProb.pState (LatticeProb.toPDriver ω) q.1).active (0, q.2)) := by
        rw [Measure.map_map hG (measurable_relabelData σ)]
        rfl
    _ = ((pLaw d μ).restrict A).map (fun ω => fun q : ℕ × ℕ =>
        (LatticeProb.pState (LatticeProb.toPDriver ω) q.1).active (0, q.2)) := by rw [hstep]

/-- **Exchangeability in the stack construction.**  The two constructions have
the same law, so the exchangeability of the origin particles transports. -/
theorem exchangeable_origin (hd : 1 ≤ d) (μ : Measure (Site d → ℤ))
    [IsProbabilityMeasure μ] (k : ℕ) (σ : Equiv.Perm ℕ) (hk : ∀ i, k ≤ i → σ i = i) :
    ((dataLaw d μ).restrict {ω : Data d | ω.1 0 = (k : ℤ)}).map
        (fun ω => fun q : ℕ × ℕ =>
          (state (toDriver ω) q.1).active (0, σ q.2))
      = ((dataLaw d μ).restrict {ω : Data d | ω.1 0 = (k : ℤ)}).map
        (fun ω => fun q : ℕ × ℕ =>
          (state (toDriver ω) q.1).active (0, q.2)) := by
  classical
  set E : Set ((Site d → ℤ) × ((ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) ×
      (ℕ × Label d → Bool))) := {z | z.1 0 = (k : ℤ)} with hEdef
  have hEmeas : MeasurableSet E :=
    ((measurable_pi_apply (0 : Site d)).comp measurable_fst) (measurableSet_singleton _)
  have hGmeas : ∀ τ : Equiv.Perm ℕ, Measurable fun z : (Site d → ℤ) ×
      ((ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) × (ℕ × Label d → Bool)) =>
      fun q : ℕ × ℕ => z.2.2.2.2 (q.1, ((0 : Site d), τ q.2)) := by
    intro τ
    refine measurable_pi_lambda _ fun q => ?_
    exact (measurable_pi_apply (q.1, ((0 : Site d), τ q.2))).comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hΦ : Measurable fun ω : Data d => (ω.1, LatticeProb.stackObservables ω) :=
    measurable_fst.prodMk measurable_stackObservables
  have hΨ : Measurable fun ω : LatticeProb.PData d => (ω.1, LatticeProb.pObservables ω) :=
    measurable_fst.prodMk measurable_pObservables
  have hkey : (dataLaw d μ).map (fun ω : Data d => (ω.1, LatticeProb.stackObservables ω))
      = (pLaw d μ).map (fun ω : LatticeProb.PData d => (ω.1, LatticeProb.pObservables ω)) :=
    constructionsAgree_conf d hd μ
  have htrans : ∀ τ : Equiv.Perm ℕ,
      ((dataLaw d μ).restrict {ω : Data d | ω.1 0 = (k : ℤ)}).map
          (fun ω => fun q : ℕ × ℕ => (state (toDriver ω) q.1).active (0, τ q.2))
        = ((pLaw d μ).restrict {ω : LatticeProb.PData d | ω.1 0 = (k : ℤ)}).map
          (fun ω => fun q : ℕ × ℕ =>
            (LatticeProb.pState (LatticeProb.toPDriver ω) q.1).active (0, τ q.2)) := by
    intro τ
    calc ((dataLaw d μ).restrict {ω : Data d | ω.1 0 = (k : ℤ)}).map
          (fun ω => fun q : ℕ × ℕ => (state (toDriver ω) q.1).active (0, τ q.2))
        = (((dataLaw d μ).map
            (fun ω : Data d => (ω.1, LatticeProb.stackObservables ω))).restrict E).map
            (fun z => fun q : ℕ × ℕ => z.2.2.2.2 (q.1, ((0 : Site d), τ q.2))) :=
          map_restrict_comp _ hΦ (hGmeas τ) hEmeas
      _ = (((pLaw d μ).map
            (fun ω : LatticeProb.PData d => (ω.1, LatticeProb.pObservables ω))).restrict E).map
            (fun z => fun q : ℕ × ℕ => z.2.2.2.2 (q.1, ((0 : Site d), τ q.2))) := by
          rw [hkey]
      _ = ((pLaw d μ).restrict {ω : LatticeProb.PData d | ω.1 0 = (k : ℤ)}).map
            (fun ω => fun q : ℕ × ℕ =>
              (LatticeProb.pState (LatticeProb.toPDriver ω) q.1).active (0, τ q.2)) :=
          (map_restrict_comp _ hΨ (hGmeas τ) hEmeas).symm
  have h2 := htrans (Equiv.refl ℕ)
  simp only [Equiv.refl_apply] at h2
  rw [htrans σ, h2]
  exact exchangeable_particle hd μ k σ hk

end Parking

end
