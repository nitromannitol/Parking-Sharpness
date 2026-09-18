/-
A particle never settles where the configuration is nonnegative.

`lem:range-lower` follows particle `1` from the origin along its own walk and
bounds its survival below by the chance that the configuration is nonnegative at
every site of the walk's range.  In the particle-driven construction that is a
PATHWISE statement, and this file proves it: a site whose configuration value is
nonnegative carries no unfilled hole at any time, so nothing settles there, so a
particle whose walk stays in such sites is active forever and its position is
the position of the walk.

Also here, and useful beyond this lemma: reindexing an independent family along
an injection between two arbitrary index sets leaves its law unchanged.  It is
the exploration lemma along a well-founded dependency with a CONSTANT index map
and an empty dependency.
-/
import Parking.Support.SurvivorExpansion
import Parking.Support.Range
import Parking.Support.MassTransport

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### Reindexing an independent family -/

/-- Reading an independent family along an injection gives an independent family
with the same one-coordinate law. -/
theorem infinitePi_map_inj' {ι κ α : Type*} [MeasurableSpace ι] [Countable ι]
    [MeasurableSingletonClass ι] [DecidableEq ι] [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (e : κ → ι) (he : Function.Injective e) :
    (Measure.infinitePi fun _ : ι => ν).map (fun ω a => ω (e a))
      = Measure.infinitePi fun _ : κ => ν := by
  classical
  have hdag : LatticeProb.IsDagExploration (X := fun _ : ι => α) (κ := κ)
      (fun a _ => e a) (fun _ => (∅ : Finset κ)) := by
    refine ⟨fun _ => measurable_const, ?_, fun a b _ hab hc => hab (he hc),
      fun _ _ _ _ _ => rfl⟩
    refine WellFounded.intro fun a => Acc.intro a fun b hb => ?_
    exact absurd hb (Finset.notMem_empty b)
  exact LatticeProb.map_revealed_dag (X := fun _ : ι => α) (κ := κ)
    (fun _ : ι => ν) (g := fun _ => id) hdag (fun _ => measurable_id)
    (fun _ => Measure.map_id)

/-! ### Nothing settles where the configuration is nonnegative -/

/-- A site whose configuration value is nonnegative carries no unfilled hole at
any time. -/
theorem pHoles_eq_zero_of_nonneg (D : PDriver d) (y : Site d) (hy : 0 ≤ D.eta y) :
    ∀ t : ℕ, (pState D t).holes y = 0 := by
  intro t
  induction t with
  | zero =>
      show (-(D.eta y)).toNat = 0
      omega
  | succ t ih =>
      rw [pHoles_succ, ih]
      simp

/-- A particle never settles at a site whose configuration value is
nonnegative. -/
theorem not_pSettles_of_nonneg (D : PDriver d) (t : ℕ) (p : Label d)
    (hy : 0 ≤ D.eta (pNextPos D (pState D t) t p)) :
    pSettles D (pState D t) t p = false := by
  have hz : (pState D t).holes (pNextPos D (pState D t) t p) = 0 :=
    pHoles_eq_zero_of_nonneg D _ hy t
  show decide (_ ∧ _) = false
  simp only [decide_eq_false_iff_not, not_and, not_lt, hz]
  intro _
  exact Nat.zero_le _

/-- **A particle whose walk stays where the configuration is nonnegative is
active forever.** -/
theorem pActive_of_nonneg (D : PDriver d) (p : Label d)
    (h0 : p.2 < (D.eta p.1).toNat) :
    ∀ t : ℕ, (∀ s, s < t → 0 ≤ D.eta ((pState D (s + 1)).pos p)) →
      (pState D t).active p = true := by
  intro t
  induction t with
  | zero =>
      intro _
      show decide (p.2 < (D.eta p.1).toNat) = true
      simpa using h0
  | succ t ih =>
      intro hpos
      have hact : (pState D t).active p = true :=
        ih fun s hs => hpos s (Nat.lt_succ_of_lt hs)
      refine (pActive_succ_iff D t p).mpr ⟨hact, ?_⟩
      refine not_pSettles_of_nonneg D t p ?_
      have := hpos t (Nat.lt_succ_self t)
      rwa [pPos_succ] at this

/-- While a particle is active its position is the position of its own walk. -/
theorem pPos_eq_walkPath (D : PDriver d) (p : Label d) :
    ∀ t : ℕ, (∀ s, s < t → (pState D s).active p = true) →
      (pState D t).pos p = walkPath p.1 (fun j => D.move (p, j)) t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro hact
      have h1 : (pState D t).pos p = walkPath p.1 (fun j => D.move (p, j)) t :=
        ih fun s hs => hact s (Nat.lt_succ_of_lt hs)
      rw [pPos_succ, pNextPos_of_active D _ t p (hact t (Nat.lt_succ_self t)), h1]
      rfl

/-- The displacements of one particle are a walk: the family of its own
displacements has the law of the direction sequence of a simple random walk. -/
theorem moveLaw_map_label (hd : 1 ≤ d) (p : Label d) :
    (moveLaw d).map (fun m : Label d × ℕ → Fin d × Bool => fun j : ℕ => m (p, j))
      = walkLaw d := by
  haveI := stepLaw_isProbability hd
  unfold moveLaw walkLaw
  exact infinitePi_map_inj' (stepLaw d) (fun j : ℕ => (p, j))
    fun a b h => by simpa [Prod.mk.injEq] using h

theorem pActive_walk_of_nonneg (D : PDriver d) (p : Label d)
    (h0 : p.2 < (D.eta p.1).toNat) (t : ℕ)
    (hnn : ∀ s, s ≤ t → 0 ≤ D.eta (walkPath p.1 (fun j => D.move (p, j)) s)) :
    (pState D t).active p = true ∧
      (pState D t).pos p = walkPath p.1 (fun j => D.move (p, j)) t := by
  induction t with
  | zero =>
      refine ⟨?_, rfl⟩
      show decide (p.2 < (D.eta p.1).toNat) = true
      simpa using h0
  | succ t ih =>
      obtain ⟨hact, hpos⟩ := ih fun s hs => hnn s (Nat.le_succ_of_le hs)
      have hnext : pNextPos D (pState D t) t p
          = walkPath p.1 (fun j => D.move (p, j)) (t + 1) := by
        rw [pNextPos_of_active D _ t p hact, hpos]
        rfl
      have hset : pSettles D (pState D t) t p = false := by
        refine not_pSettles_of_nonneg D t p ?_
        rw [hnext]
        exact hnn (t + 1) le_rfl
      refine ⟨(pActive_succ_iff D t p).mpr ⟨hact, hset⟩, ?_⟩
      rw [pPos_succ, hnext]

theorem measurable_rangeCard (x : Site d) (t : ℕ) :
    Measurable fun p : ℕ → Fin d × Bool => Parking.rangeCard x p t := by
  classical
  have himg : ∀ p : ℕ → Fin d × Bool,
      ((Finset.range (t + 1)).image fun j => walkPath x p j)
        = Finset.univ.image (fun j : Fin (t + 1) => walkPath x p j.val) := by
    intro p
    ext y
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, hj⟩, rfl⟩
    · rintro ⟨j, rfl⟩; exact ⟨j.val, j.isLt, rfl⟩
  have hproj : Measurable fun (p : ℕ → Fin d × Bool) (j : Fin (t + 1)) => walkPath x p j.val :=
    measurable_pi_lambda _ fun j => measurable_walkPath x j.val
  have hfun : (fun p : ℕ → Fin d × Bool => Parking.rangeCard x p t)
      = (fun q : Fin (t + 1) → Site d => (Finset.univ.image q).card)
        ∘ (fun (p : ℕ → Fin d × Bool) (j : Fin (t + 1)) => walkPath x p j.val) := by
    funext p
    show Parking.rangeCard x p t = _
    rw [Parking.rangeCard, himg p]
    rfl
  rw [hfun]
  exact (measurable_from_countable' _).comp hproj

theorem iidLaw_cylinder (ν : Measure ℤ) [IsProbabilityMeasure ν] (R : Finset (Site d))
    (A : Site d → Set ℤ) (hA : ∀ x, MeasurableSet (A x)) :
    LatticeProb.iidLaw d ν {η : Site d → ℤ | ∀ x ∈ R, η x ∈ A x} = ∏ x ∈ R, ν (A x) := by
  classical
  have hv : Function.Injective (fun k : {x // x ∈ R} => (k : Site d)) := Subtype.val_injective
  have hmap : (Measure.infinitePi fun _ : Site d => ν).map
      (fun (ω : Site d → ℤ) (k : {x // x ∈ R}) => ω (k : Site d))
      = Measure.pi fun _ : {x // x ∈ R} => ν :=
    LatticeProb.infinitePi_map_comp ν (fun k : {x // x ∈ R} => (k : Site d)) hv
  have hmeas : Measurable fun (ω : Site d → ℤ) (k : {x // x ∈ R}) => ω (k : Site d) :=
    measurable_pi_lambda _ fun k => measurable_pi_apply _
  have hpi : MeasurableSet (Set.univ.pi fun k : {x // x ∈ R} => A (k : Site d)) :=
    MeasurableSet.univ_pi fun k => hA _
  have hpre : {η : Site d → ℤ | ∀ x ∈ R, η x ∈ A x}
      = (fun (ω : Site d → ℤ) (k : {x // x ∈ R}) => ω (k : Site d)) ⁻¹'
        (Set.univ.pi fun k : {x // x ∈ R} => A (k : Site d)) := by
    ext η
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h k; exact h k.1 k.2
    · intro h x hx; exact h ⟨x, hx⟩
  calc LatticeProb.iidLaw d ν {η : Site d → ℤ | ∀ x ∈ R, η x ∈ A x}
      = (Measure.infinitePi fun _ : Site d => ν)
          ((fun (ω : Site d → ℤ) (k : {x // x ∈ R}) => ω (k : Site d)) ⁻¹'
            (Set.univ.pi fun k : {x // x ∈ R} => A (k : Site d))) := by
        rw [← hpre]; rfl
    _ = ((Measure.infinitePi fun _ : Site d => ν).map
          (fun (ω : Site d → ℤ) (k : {x // x ∈ R}) => ω (k : Site d)))
          (Set.univ.pi fun k : {x // x ∈ R} => A (k : Site d)) := by
        rw [Measure.map_apply hmeas hpi]
    _ = (Measure.pi fun _ : {x // x ∈ R} => ν)
          (Set.univ.pi fun k : {x // x ∈ R} => A (k : Site d)) := by rw [hmap]
    _ = ∏ k : {x // x ∈ R}, ν (A (k : Site d)) := by
        rw [Measure.pi_pi]
    _ = ∏ x ∈ R, ν (A x) := by
        rw [← Finset.prod_coe_sort R fun x => ν (A x)]

/-- The walk of the first particle at the origin, read off the data. -/
def firstWalk (ω : PData d) : ℕ → Fin d × Bool := fun j => ω.2.1 (((0 : Site d), 0), j)

theorem measurable_firstWalk : Measurable (firstWalk (d := d)) :=
  measurable_pi_lambda _ fun _ =>
    (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)

theorem measurable_walkPath_var (x : Site d) (s : ℕ) :
    Measurable fun ω : PData d => walkPath x (firstWalk ω) s := by
  induction s with
  | zero => exact measurable_const
  | succ s ih =>
      exact ih.add ((measurable_from_countable' (stepVec (d := d))).comp
        ((measurable_pi_apply s).comp measurable_firstWalk))

/-- The event of `lem:range-lower`: the configuration is `m` at the origin and
nonnegative along the walk of the first particle there. -/
def walkGood (d : ℕ) (m : ℤ) (t : ℕ) : Set (PData d) :=
  {ω | ω.1 0 = m ∧ ∀ s ≤ t, 0 ≤ ω.1 (walkPath 0 (firstWalk ω) s)}

theorem measurableSet_walkGood (m : ℤ) (t : ℕ) : MeasurableSet (walkGood d m t) := by
  classical
  have h1 : MeasurableSet {ω : PData d | ω.1 0 = m} := by
    have : {ω : PData d | ω.1 0 = m} = (fun ω : PData d => ω.1 0) ⁻¹' {m} := rfl
    rw [this]
    exact ((measurable_pi_apply (0 : Site d)).comp measurable_fst) (measurableSet_singleton m)
  have h2 : ∀ s : ℕ, MeasurableSet {ω : PData d | 0 ≤ ω.1 (walkPath 0 (firstWalk ω) s)} := by
    intro s
    have hm : Measurable fun ω : PData d => ω.1 (walkPath 0 (firstWalk ω) s) :=
      measurable_eval_var (fun ω : PData d => walkPath (0 : Site d) (firstWalk ω) s)
        (measurable_walkPath_var 0 s) (fun ω => ω.1)
        (fun x => (measurable_pi_apply x).comp measurable_fst)
    exact measurableSet_le measurable_const hm
  have : walkGood d m t
      = {ω : PData d | ω.1 0 = m} ∩ ⋂ s ∈ Finset.range (t + 1),
          {ω : PData d | 0 ≤ ω.1 (walkPath 0 (firstWalk ω) s)} := by
    ext ω
    simp only [walkGood, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_range,
      Nat.lt_succ_iff]
  rw [this]
  exact h1.inter (MeasurableSet.biInter (Set.to_countable _) fun s _ => h2 s)

theorem one_le_rangeCard (x : Site d) (p : ℕ → Fin d × Bool) (t : ℕ) :
    1 ≤ Parking.rangeCard x p t := by
  refine Finset.card_pos.mpr ⟨x, ?_⟩
  exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos t), rfl⟩

/-- The cylinder computation of `lem:range-lower`: the configuration is `m` at
the origin and nonnegative along the rest of the walk's range. -/
theorem iidLaw_walk_cylinder (ν : Measure ℤ) [IsProbabilityMeasure ν] (m : ℤ) (hm : 1 ≤ m)
    (w : ℕ → Fin d × Bool) (t : ℕ) :
    LatticeProb.iidLaw d ν {η : Site d → ℤ | η 0 = m ∧ ∀ s ≤ t, 0 ≤ η (walkPath 0 w s)}
      = ν {m} * (ν {j : ℤ | 0 ≤ j}) ^ (Parking.rangeCard (0 : Site d) w t - 1) := by
  classical
  set R : Finset (Site d) := (Finset.range (t + 1)).image (fun j => walkPath (0 : Site d) w j)
    with hR
  set A : Site d → Set ℤ := fun x => if x = 0 then {m} else {j : ℤ | 0 ≤ j} with hAdef
  have hA : ∀ x, MeasurableSet (A x) := by
    intro x
    by_cases h : x = 0
    · simp only [hAdef, if_pos h]; exact measurableSet_singleton m
    · simp only [hAdef, if_neg h]
      exact measurableSet_le measurable_const measurable_id
  have h0R : (0 : Site d) ∈ R := by
    refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos t), rfl⟩
  have hset : {η : Site d → ℤ | η 0 = m ∧ ∀ s ≤ t, 0 ≤ η (walkPath 0 w s)}
      = {η : Site d → ℤ | ∀ x ∈ R, η x ∈ A x} := by
    ext η
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩ x hx
      rcases Finset.mem_image.mp hx with ⟨s, hs, rfl⟩
      by_cases hz : walkPath (0 : Site d) w s = 0
      · have hAx : A (walkPath (0 : Site d) w s) = {m} := by simp [hAdef, hz]
        rw [hAx, hz, h1]
        exact rfl
      · simp only [hAdef, if_neg hz, Set.mem_setOf_eq]
        exact h2 s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs))
    · intro h
      have h1 : η 0 = m := by
        have := h 0 h0R
        simpa [hAdef] using this
      refine ⟨h1, fun s hs => ?_⟩
      have hx : walkPath (0 : Site d) w s ∈ R :=
        Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr (Nat.lt_succ_of_le hs), rfl⟩
      have := h _ hx
      by_cases hz : walkPath (0 : Site d) w s = 0
      · rw [hz, h1]; omega
      · simpa [hAdef, if_neg hz] using this
  rw [hset, iidLaw_cylinder ν R A hA]
  rw [← Finset.mul_prod_erase R (fun x => ν (A x)) h0R]
  have hA0 : ν (A 0) = ν {m} := by simp [hAdef]
  have hprod : ∏ x ∈ R.erase 0, ν (A x) = (ν {j : ℤ | 0 ≤ j}) ^ (R.erase 0).card := by
    rw [Finset.prod_congr rfl (fun x hx => ?_), Finset.prod_const]
    have : x ≠ 0 := Finset.ne_of_mem_erase hx
    simp [hAdef, if_neg this]
  rw [hA0, hprod, Finset.card_erase_of_mem h0R]
  rfl

/-- The law of the walk of the first particle at the origin. -/
theorem map_firstWalk (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    ((moveLaw d).prod (LatticeProb.rankLaw d)).map
        (fun y : (Label d × ℕ → Fin d × Bool) × (Label d × ℕ → ℝ) =>
          fun j : ℕ => y.1 (((0 : Site d), 0), j))
      = walkLaw d := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  have hg : Measurable fun m : Label d × ℕ → Fin d × Bool =>
      fun j : ℕ => m (((0 : Site d), 0), j) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  have hfst : ((moveLaw d).prod (LatticeProb.rankLaw d)).map Prod.fst = moveLaw d :=
    Measure.fst_prod
  calc ((moveLaw d).prod (LatticeProb.rankLaw d)).map
        (fun y : (Label d × ℕ → Fin d × Bool) × (Label d × ℕ → ℝ) =>
          fun j : ℕ => y.1 (((0 : Site d), 0), j))
      = (((moveLaw d).prod (LatticeProb.rankLaw d)).map Prod.fst).map
          (fun m : Label d × ℕ → Fin d × Bool => fun j : ℕ => m (((0 : Site d), 0), j)) := by
        rw [Measure.map_map hg measurable_fst]; rfl
    _ = (moveLaw d).map
          (fun m : Label d × ℕ → Fin d × Bool => fun j : ℕ => m (((0 : Site d), 0), j)) := by
        rw [hfst]
    _ = walkLaw d := moveLaw_map_label hd ((0 : Site d), 0)

/-- The probability of the good event, in terms of the walk alone. -/
theorem pDataLaw_walkGood (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] (m : ℤ)
    (hm : 1 ≤ m) (t : ℕ) :
    (pDataLaw d ν) (walkGood d m t)
      = ν {m} * ∫⁻ w, (ν {j : ℤ | 0 ≤ j}) ^ (Parking.rangeCard (0 : Site d) w t - 1)
          ∂(walkLaw d) := by
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (moveLaw d) := by unfold moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hpow : Measurable fun w : ℕ → Fin d × Bool =>
      (ν {j : ℤ | 0 ≤ j}) ^ (Parking.rangeCard (0 : Site d) w t - 1) :=
    (measurable_from_countable' fun n : ℕ => (ν {j : ℤ | 0 ≤ j}) ^ (n - 1)).comp
      (measurable_rangeCard 0 t)
  have hprod : pDataLaw d ν
      = (LatticeProb.iidLaw d ν).prod ((moveLaw d).prod (LatticeProb.rankLaw d)) := rfl
  rw [hprod, Measure.prod_apply_symm (measurableSet_walkGood m t)]
  have hslice : ∀ y : (Label d × ℕ → Fin d × Bool) × (Label d × ℕ → ℝ),
      (LatticeProb.iidLaw d ν) ((fun η : Site d → ℤ => (η, y)) ⁻¹' walkGood d m t)
        = ν {m} * (ν {j : ℤ | 0 ≤ j}) ^
            (Parking.rangeCard (0 : Site d) (fun j : ℕ => y.1 (((0 : Site d), 0), j)) t - 1) := by
    intro y
    have hpre : (fun η : Site d → ℤ => (η, y)) ⁻¹' walkGood d m t
        = {η : Site d → ℤ | η 0 = m ∧ ∀ s ≤ t,
            0 ≤ η (walkPath 0 (fun j : ℕ => y.1 (((0 : Site d), 0), j)) s)} := rfl
    rw [hpre]
    exact iidLaw_walk_cylinder ν m hm _ t
  simp only [hslice]
  rw [lintegral_const_mul' _ _ (measure_ne_top ν {m})]
  congr 1
  rw [← map_firstWalk hd ν, lintegral_map hpow
    (measurable_pi_lambda _ fun _ => (measurable_pi_apply _).comp measurable_fst)]

/-! ### The good event sits inside the survival event -/

theorem walkGood_subset (m : ℤ) (hm : 1 ≤ m) (t : ℕ) :
    walkGood d m t ⊆ {ω : PData d | ω.1 0 = m ∧ (pState (toPDriver ω) t).active (0, 0) = true} := by
  rintro ω ⟨h1, h2⟩
  refine ⟨h1, ?_⟩
  have h0 : (((0 : Site d), 0) : Label d).2 < ((toPDriver ω).eta (((0 : Site d), 0) : Label d).1).toNat := by
    show 0 < (ω.1 0).toNat
    rw [h1]; omega
  exact (pActive_walk_of_nonneg (toPDriver ω) ((0 : Site d), 0) h0 t
    fun s hs => h2 s hs).1

/-! ### The survival probability, transferred and bounded -/

theorem measurable_active_pdata (t : ℕ) (p : Label d) :
    Measurable fun ω : PData d => (pState (toPDriver ω) t).active p := by
  have hmeas : Measurable (stepVec (d := d)) := measurable_from_countable' _
  have hrecode : Measurable fun ω : PData d =>
      ((ω.1, (fun q => stepVec (ω.2.1 q), ω.2.2)) : LatticeProb.PData d) :=
    measurable_fst.prodMk
      ((measurable_pi_lambda _ fun q =>
        hmeas.comp ((measurable_pi_apply q).comp (measurable_fst.comp measurable_snd))).prodMk
        (measurable_snd.comp measurable_snd))
  have hcomp : (fun ω : PData d => (pState (toPDriver ω) t).active p)
      = (fun ω : LatticeProb.PData d => (LatticeProb.pState (LatticeProb.toPDriver ω) t).active p)
        ∘ (fun ω : PData d => ((ω.1, (fun q => stepVec (ω.2.1 q), ω.2.2)) : LatticeProb.PData d)) := by
    funext ω
    show (pState (toPDriver ω) t).active p
        = (LatticeProb.pState ⟨ω.1, fun q => stepVec (ω.2.1 q), ω.2.2⟩ t).active p
    have h := pState_stepVec ω.1 ω.2.1 ω.2.2 t
    show (pState ⟨ω.1, ω.2.1, ω.2.2⟩ t).active p = _
    rw [h]
  rw [hcomp]
  exact ((measurable_pState (d := d) t).1 p).comp hrecode

theorem measurableSet_conf_active (m : ℤ) (t : ℕ) (i : ℕ) :
    MeasurableSet {ω : PData d | ω.1 0 = m ∧ (pState (toPDriver ω) t).active (0, i) = true} := by
  have h1 : MeasurableSet {ω : PData d | ω.1 0 = m} := by
    have : {ω : PData d | ω.1 0 = m} = (fun ω : PData d => ω.1 0) ⁻¹' {m} := rfl
    rw [this]
    exact ((measurable_pi_apply (0 : Site d)).comp measurable_fst) (measurableSet_singleton m)
  have h2 : MeasurableSet {ω : PData d | (pState (toPDriver ω) t).active (0, i) = true} :=
    measurable_active_pdata t (0, i) (measurableSet_singleton true)
  exact h1.inter h2

/-- The configuration and the activity field have the same joint law in the two
constructions. -/
theorem map_conf_active_agree (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    (law d ν).map (fun ω : Data d =>
        (ω.1, fun ti : ℕ × Label d => (LatticeProb.state (toDriver ω) ti.1).active ti.2))
      = (pDataLaw d ν).map (fun ω : PData d =>
        (ω.1, fun ti : ℕ × Label d => (pState (toPDriver ω) ti.1).active ti.2)) := by
  classical
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  set Obs := (ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) × (ℕ × Label d → Bool)
    with hObs
  set π : (Site d → ℤ) × Obs → (Site d → ℤ) × (ℕ × Label d → Bool) :=
    fun z => (z.1, z.2.2.2.2) with hπ
  have hπmeas : Measurable π :=
    measurable_fst.prodMk
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hmeas : Measurable (stepVec (d := d)) := measurable_from_countable' _
  have hrecode : Measurable fun ω : PData d =>
      ((ω.1, (fun q => stepVec (ω.2.1 q), ω.2.2)) : LatticeProb.PData d) :=
    measurable_fst.prodMk
      ((measurable_pi_lambda _ fun q =>
        hmeas.comp ((measurable_pi_apply q).comp (measurable_fst.comp measurable_snd))).prodMk
        (measurable_snd.comp measurable_snd))
  have hlaw : (pDataLaw d ν).map (fun ω : PData d =>
      ((ω.1, (fun q => stepVec (ω.2.1 q), ω.2.2)) : LatticeProb.PData d))
      = LatticeProb.pDataLaw d ν :=
    LatticeProb.map_pDataLaw_of_map (stepLaw d) stepVec hmeas map_stepLaw_stepVec ν hd
  have hGs : Measurable fun ω : LatticeProb.StackData d =>
      (ω.1, LatticeProb.stackObservables ω) :=
    measurable_fst.prodMk measurable_stackObservables
  have hGp : Measurable fun ω : LatticeProb.PData d => (ω.1, LatticeProb.pObservables ω) :=
    measurable_fst.prodMk measurable_pObservables
  have hagree := constructionsAgree_conf d hd (LatticeProb.iidLaw d ν)
  have hlawdef : law d ν
      = (LatticeProb.iidLaw d ν).prod ((LatticeProb.stackLaw d).prod (LatticeProb.rankLaw d)) := rfl
  have hpdef : LatticeProb.pDataLaw d ν
      = (LatticeProb.iidLaw d ν).prod ((LatticeProb.moveLaw d).prod (LatticeProb.rankLaw d)) := rfl
  calc (law d ν).map (fun ω : Data d =>
          (ω.1, fun ti : ℕ × Label d => (LatticeProb.state (toDriver ω) ti.1).active ti.2))
      = ((law d ν).map (fun ω : LatticeProb.StackData d =>
          (ω.1, LatticeProb.stackObservables ω))).map π := by
        rw [Measure.map_map hπmeas hGs]; rfl
    _ = ((LatticeProb.pDataLaw d ν).map (fun ω : LatticeProb.PData d =>
          (ω.1, LatticeProb.pObservables ω))).map π := by
        rw [hlawdef, hpdef, hagree]
    _ = (((pDataLaw d ν).map (fun ω : PData d =>
          ((ω.1, (fun q => stepVec (ω.2.1 q), ω.2.2)) : LatticeProb.PData d))).map
          (fun ω : LatticeProb.PData d => (ω.1, LatticeProb.pObservables ω))).map π := by
        rw [hlaw]
    _ = ((pDataLaw d ν).map (fun ω : PData d =>
          (ω.1, fun ti : ℕ × Label d => (pState (toPDriver ω) ti.1).active ti.2))) := by
        rw [Measure.map_map hGp hrecode, Measure.map_map hπmeas (hGp.comp hrecode)]
        refine congrArg (fun f => Measure.map f (pDataLaw d ν)) ?_
        funext ω
        refine Prod.ext rfl (funext fun ti => ?_)
        show (LatticeProb.pState ⟨ω.1, fun q => stepVec (ω.2.1 q), ω.2.2⟩ ti.1).active ti.2
          = (pState (toPDriver ω) ti.1).active ti.2
        have h := pState_stepVec ω.1 ω.2.1 ω.2.2 ti.1
        show _ = (pState ⟨ω.1, ω.2.1, ω.2.2⟩ ti.1).active ti.2
        rw [h]

/-- The mean of the positive part of an integer law, expanded over its values. -/
theorem integral_posPart_eq_tsum (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) :
    ∫ k, max (k : ℝ) 0 ∂ν = ∑' m : ℕ, ((m : ℝ) + 1) * (ν {(m : ℤ) + 1}).toReal := by
  classical
  have hmeas : Measurable fun k : ℤ => max (k : ℝ) 0 := measurable_from_countable' _
  have hI : Integrable (fun k : ℤ => max (k : ℝ) 0) ν := by
    refine hint.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun k => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right (k : ℝ) 0)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  rw [MeasureTheory.integral_countable hI]
  have hg : Function.Injective fun m : ℕ => (m : ℤ) + 1 := by
    intro a b h
    simp only [add_left_inj, Nat.cast_inj] at h
    exact h
  have hsupp : Function.support (fun k : ℤ => ν.real {k} • max (k : ℝ) 0)
      ⊆ Set.range fun m : ℕ => (m : ℤ) + 1 := by
    intro k hk
    have hk0 : 0 < k := by
      rcases lt_or_ge 0 k with h | h
      · exact h
      · exfalso
        apply hk
        have hz : max (k : ℝ) 0 = 0 := max_eq_right (by exact_mod_cast h)
        show ν.real {k} • max (k : ℝ) 0 = 0
        rw [hz, smul_zero]
    refine ⟨(k - 1).toNat, ?_⟩
    show ((k - 1).toNat : ℤ) + 1 = k
    omega
  rw [← hg.tsum_eq hsupp]
  refine tsum_congr fun m => ?_
  have hcast : (((m : ℤ) + 1 : ℤ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hmax : max (((m : ℤ) + 1 : ℤ) : ℝ) 0 = (m : ℝ) + 1 := by
    rw [hcast]
    exact max_eq_left (by positivity)
  show ν.real {(m : ℤ) + 1} • max (((m : ℤ) + 1 : ℤ) : ℝ) 0 = _
  rw [hmax, smul_eq_mul, measureReal_def]
  ring



theorem walkLaw_isProbability (hd : 1 ≤ d) : IsProbabilityMeasure (walkLaw d) := by
  haveI := stepLaw_isProbability hd
  unfold walkLaw
  infer_instance

theorem measurable_rangePow (ν : Measure ℤ) (t : ℕ) :
    Measurable fun p : ℕ → Fin d × Bool => (ν {j : ℤ | 0 ≤ j}).toReal ^
      (Parking.rangeCard (0 : Site d) p t - 1) :=
  (measurable_from_countable' fun n : ℕ => (ν {j : ℤ | 0 ≤ j}).toReal ^ (n - 1)).comp
    (measurable_rangeCard 0 t)

theorem rangePow_le_one (ν : Measure ℤ) [IsProbabilityMeasure ν] (p : ℕ → Fin d × Bool)
    (t : ℕ) :
    (ν {j : ℤ | 0 ≤ j}).toReal ^ (Parking.rangeCard (0 : Site d) p t - 1) ≤ 1 := by
  refine pow_le_one₀ ENNReal.toReal_nonneg ?_
  have h1 : ν {j : ℤ | 0 ≤ j} ≤ 1 := prob_le_one
  calc (ν {j : ℤ | 0 ≤ j}).toReal ≤ (1 : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono ENNReal.one_ne_top h1
    _ = 1 := ENNReal.toReal_one

/-- The bound of `lem:range-lower` is an integrable function of the walk. -/
theorem integrable_rangePow (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] (t : ℕ) :
    Integrable (fun p => (ν {j : ℤ | 0 ≤ j}).toReal ^
        (Parking.rangeCard (0 : Site d) p t - 1)) (Parking.walkLaw d) := by
  haveI := walkLaw_isProbability (d := d) hd
  refine (integrable_const (1 : ℝ)).mono'
    (measurable_rangePow ν t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ENNReal.toReal_nonneg _)]
  exact rangePow_le_one ν p t

/-- The bound of `lem:range-lower`, in `ℝ≥0∞` and in `ℝ`. -/
theorem lintegral_rangePow_toReal (ν : Measure ℤ) [IsProbabilityMeasure ν] (t : ℕ) :
    (∫⁻ w, (ν {j : ℤ | 0 ≤ j}) ^ (Parking.rangeCard (0 : Site d) w t - 1) ∂(walkLaw d)).toReal
      = ∫ w, (ν {j : ℤ | 0 ≤ j}).toReal ^ (Parking.rangeCard (0 : Site d) w t - 1)
          ∂(walkLaw d) := by
  have hofReal : ∀ w : ℕ → Fin d × Bool,
      ENNReal.ofReal ((ν {j : ℤ | 0 ≤ j}).toReal ^ (Parking.rangeCard (0 : Site d) w t - 1))
        = (ν {j : ℤ | 0 ≤ j}) ^ (Parking.rangeCard (0 : Site d) w t - 1) := by
    intro w
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (measure_ne_top ν _)]
  have h := MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (μ := walkLaw d)
    (f := fun w : ℕ → Fin d × Bool => (ν {j : ℤ | 0 ≤ j}).toReal ^
      (Parking.rangeCard (0 : Site d) w t - 1))
    (Filter.Eventually.of_forall fun w => pow_nonneg ENNReal.toReal_nonneg _)
    (measurable_rangePow ν t).aestronglyMeasurable
  rw [h]
  congr 1
  exact lintegral_congr fun w => (hofReal w).symm



theorem measurable_confActive_stack :
    Measurable fun ω : Data d =>
      ((ω.1, fun ti : ℕ × Label d => (LatticeProb.state (toDriver ω) ti.1).active ti.2) :
        (Site d → ℤ) × (ℕ × Label d → Bool)) :=
  measurable_fst.prodMk (measurable_pi_lambda _ fun ti => (measurable_state ti.1).1 ti.2)

theorem measurable_confActive_particle :
    Measurable fun ω : PData d =>
      ((ω.1, fun ti : ℕ × Label d => (pState (toPDriver ω) ti.1).active ti.2) :
        (Site d → ℤ) × (ℕ × Label d → Bool)) :=
  measurable_fst.prodMk
    (measurable_pi_lambda _ fun ti => measurable_active_pdata ti.1 ti.2)

/-- The joint probability of the configuration at the origin and the survival of
the first particle there is the same in the two constructions. -/
theorem measure_conf_active_transfer (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (m : ℤ) (t : ℕ) :
    (law d ν) {ω : Data d | ω.1 0 = m ∧
        (LatticeProb.state (toDriver ω) t).active (0, 0) = true}
      = (pDataLaw d ν) {ω : PData d | ω.1 0 = m ∧
        (pState (toPDriver ω) t).active (0, 0) = true} := by
  classical
  set E : Set ((Site d → ℤ) × (ℕ × Label d → Bool)) :=
    {z | z.1 0 = m ∧ z.2 (t, ((0 : Site d), 0)) = true} with hE
  have hEmeas : MeasurableSet E := by
    have h1 : MeasurableSet {z : (Site d → ℤ) × (ℕ × Label d → Bool) | z.1 0 = m} := by
      have : {z : (Site d → ℤ) × (ℕ × Label d → Bool) | z.1 0 = m}
          = (fun z : (Site d → ℤ) × (ℕ × Label d → Bool) => z.1 0) ⁻¹' {m} := rfl
      rw [this]
      exact ((measurable_pi_apply (0 : Site d)).comp measurable_fst) (measurableSet_singleton m)
    have h2 : MeasurableSet
        {z : (Site d → ℤ) × (ℕ × Label d → Bool) | z.2 (t, ((0 : Site d), 0)) = true} := by
      have : {z : (Site d → ℤ) × (ℕ × Label d → Bool) | z.2 (t, ((0 : Site d), 0)) = true}
          = (fun z : (Site d → ℤ) × (ℕ × Label d → Bool) => z.2 (t, ((0 : Site d), 0))) ⁻¹'
            {true} := rfl
      rw [this]
      exact ((measurable_pi_apply _).comp measurable_snd) (measurableSet_singleton true)
    exact h1.inter h2
  have hs : (law d ν) {ω : Data d | ω.1 0 = m ∧
      (LatticeProb.state (toDriver ω) t).active (0, 0) = true}
      = ((law d ν).map (fun ω : Data d =>
        (ω.1, fun ti : ℕ × Label d => (LatticeProb.state (toDriver ω) ti.1).active ti.2))) E := by
    rw [Measure.map_apply measurable_confActive_stack hEmeas]
    rfl
  have hp : (pDataLaw d ν) {ω : PData d | ω.1 0 = m ∧
      (pState (toPDriver ω) t).active (0, 0) = true}
      = ((pDataLaw d ν).map (fun ω : PData d =>
        (ω.1, fun ti : ℕ × Label d => (pState (toPDriver ω) ti.1).active ti.2))) E := by
    rw [Measure.map_apply measurable_confActive_particle hEmeas]
    rfl
  rw [hs, hp, map_conf_active_agree hd ν]

/-- **The lower bound of `lem:range-lower`, before the conditioning.** -/
theorem measure_conf_active_ge (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (m : ℤ) (hm : 1 ≤ m) (t : ℕ) :
    ν {m} * ∫⁻ w, (ν {j : ℤ | 0 ≤ j}) ^ (Parking.rangeCard (0 : Site d) w t - 1) ∂(walkLaw d)
      ≤ (law d ν) {ω : Data d | ω.1 0 = m ∧
          (LatticeProb.state (toDriver ω) t).active (0, 0) = true} := by
  rw [measure_conf_active_transfer hd ν m t, ← pDataLaw_walkGood hd ν m hm t]
  exact measure_mono (walkGood_subset m hm t)

end Parking

end
