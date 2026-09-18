/-
The second clause of `lem:exposure`: conditionally on the exposure filtration,
the instructions the odometer has not reached are independent with their own
laws.

The mathematical content is that overwriting an unread instruction changes
nothing the filtration records.  That is a PATHWISE statement once the
instructions are neighbours of the site carrying them: if the odometer after
`k` rounds at `y` has not reached the index `j`, then no round up to `k` reads
the entry `(y, j)`, so the state after every round up to `k` is unchanged, and
with it the whole odometer field and every instruction the filtration records.
Both directions hold, because whether the odometer reaches `j` is itself
decided without reading the entry of index `j` (`odometer_ge_congr`).

So the sets of the filtration, intersected with the event that the family of
indices in question is unread, form a class closed under complements and
countable unions and containing the generators, hence contain the whole
filtration.  The product rule for a finite family of coordinates of an infinite
product then applies to the indicator of such a set, one coordinate at a time,
and gives the identity of set integrals that characterizes the conditional
expectation.
-/
import Parking.Support.Exposure
import Parking.Support.DeferredIntegral
import LatticeProb.Prob.Exposure

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### Overwriting an unread instruction -/

/-- If the odometer after `k` rounds at `q₀.1` has not reached the index `q₀.2`,
then overwriting the instruction there leaves the state after every round up to
`k` unchanged. -/
theorem state_update_unread {η : Site d → ℤ} {σ : Site d × ℕ → Site d}
    {r : Label d × ℕ → ℝ} (hσ : ∀ q, σ q ∈ nbrFinset q.1)
    (q₀ : Site d × ℕ) (c : Site d) {k : ℕ}
    (h : U ((η, σ, r) : Data d) k q₀.1 ≤ q₀.2) :
    ∀ m ≤ k, state (toDriver ((η, σ, r) : Data d)) m
      = state (toDriver ((η, Function.update σ q₀ c, r) : Data d)) m := by
  intro m hm
  refine state_congr (D := toDriver ((η, σ, r) : Data d))
    (D' := toDriver ((η, Function.update σ q₀ c, r) : Data d))
    (stepsToNeighbour_of_mem (D := toDriver ((η, σ, r) : Data d)) hσ) rfl rfl m ?_
  intro z i hi
  show σ (z, i) = Function.update σ q₀ c (z, i)
  refine (Function.update_of_ne ?_ _ _).symm
  rintro rfl
  have hmono : particleOdometer (toDriver ((η, σ, r) : Data d)) m z
      ≤ particleOdometer (toDriver ((η, σ, r) : Data d)) k z :=
    particleOdometer_mono _ _ hm
  have hk : particleOdometer (toDriver ((η, σ, r) : Data d)) k z ≤ i := h
  omega

/-- The odometer field up to time `k` does not see the overwriting. -/
theorem U_update_unread {η : Site d → ℤ} {σ : Site d × ℕ → Site d}
    {r : Label d × ℕ → ℝ} (hσ : ∀ q, σ q ∈ nbrFinset q.1)
    (q₀ : Site d × ℕ) (c : Site d) {k : ℕ}
    (h : U ((η, σ, r) : Data d) k q₀.1 ≤ q₀.2) :
    ∀ m ≤ k, ∀ z : Site d,
      U ((η, Function.update σ q₀ c, r) : Data d) m z = U ((η, σ, r) : Data d) m z := by
  intro m hm z
  show (state (toDriver ((η, Function.update σ q₀ c, r) : Data d)) m).departures z
    = (state (toDriver ((η, σ, r) : Data d)) m).departures z
  rw [← state_update_unread hσ q₀ c h m hm]

/-- Whether the odometer after `k` rounds has reached an index is decided
without reading the instruction of that index. -/
theorem U_le_update_iff {η : Site d → ℤ} {σ : Site d × ℕ → Site d}
    {r : Label d × ℕ → ℝ} (hσ : ∀ q, σ q ∈ nbrFinset q.1)
    (q₀ : Site d × ℕ) {c : Site d} (hc : c ∈ nbrFinset q₀.1) (k : ℕ) :
    U ((η, Function.update σ q₀ c, r) : Data d) k q₀.1 ≤ q₀.2
      ↔ U ((η, σ, r) : Data d) k q₀.1 ≤ q₀.2 := by
  have hσ' : ∀ q, Function.update σ q₀ c q ∈ nbrFinset q.1 := by
    intro q
    by_cases hq : q = q₀
    · subst hq; simpa using hc
    · rw [Function.update_of_ne hq]; exact hσ q
  have hne : ∀ q : Site d × ℕ, q ≠ (q₀.1, q₀.2) → σ q = Function.update σ q₀ c q := by
    intro q hq
    exact (Function.update_of_ne (by simpa using hq) _ _).symm
  have hiff := odometer_ge_congr (D := toDriver ((η, σ, r) : Data d))
    (D' := toDriver ((η, Function.update σ q₀ c, r) : Data d))
    (stepsToNeighbour_of_mem (D := toDriver ((η, σ, r) : Data d)) hσ)
    (stepsToNeighbour_of_mem (D := toDriver ((η, Function.update σ q₀ c, r) : Data d)) hσ')
    rfl rfl q₀.1 q₀.2 k hne
  have e1 : U ((η, σ, r) : Data d) k q₀.1
      = particleOdometer (toDriver ((η, σ, r) : Data d)) k q₀.1 := rfl
  have e2 : U ((η, Function.update σ q₀ c, r) : Data d) k q₀.1
      = particleOdometer (toDriver ((η, Function.update σ q₀ c, r) : Data d)) k q₀.1 := rfl
  omega

/-! ### The sets the filtration cannot tell apart -/

/-- A set whose membership is unchanged by overwriting any one of the
instructions indexed by `s`, on realizations whose instructions are neighbours
of their site and for which every index of `s` is still unread after `k`
rounds. -/
def UpdInvariant (d k : ℕ) (s : Finset (Site d × ℕ)) (c : Site d × ℕ → Site d)
    (A : Set (Data d)) : Prop :=
  ∀ q₀ ∈ s, ∀ (η : Site d → ℤ) (σ : Site d × ℕ → Site d) (r : Label d × ℕ → ℝ),
    (∀ q, σ q ∈ nbrFinset q.1) → (∀ q ∈ s, U ((η, σ, r) : Data d) k q.1 ≤ q.2) →
      ((((η, σ, r) : Data d) ∈ A) ↔ (((η, Function.update σ q₀ (c q₀), r) : Data d) ∈ A))

/-- Those sets form a σ-algebra. -/
@[implicit_reducible] def updInvSpace (d k : ℕ) (s : Finset (Site d × ℕ)) (c : Site d × ℕ → Site d) :
    MeasurableSpace (Data d) where
  MeasurableSet' := UpdInvariant d k s c
  measurableSet_empty := by intro q₀ _ η σ r _ _; simp
  measurableSet_compl := by
    intro A hA q₀ hq₀ η σ r hσ hB
    have h := hA q₀ hq₀ η σ r hσ hB
    simp only [Set.mem_compl_iff]
    tauto
  measurableSet_iUnion := by
    intro g hg q₀ hq₀ η σ r hσ hB
    simp only [Set.mem_iUnion]
    exact exists_congr fun n => hg n q₀ hq₀ η σ r hσ hB

/-- Every set of the exposure filtration after `m ≤ k` rounds is invariant
under overwriting an instruction that the odometer after `k` rounds has not
reached. -/
theorem expFiltration_le_updInvSpace (k : ℕ) (s : Finset (Site d × ℕ))
    (c : Site d × ℕ → Site d) :
    ∀ m, m ≤ k → expFiltration d m ≤ updInvSpace d k s c := by
  intro m
  induction m with
  | zero =>
      intro _
      refine MeasurableSpace.comap_le_iff_le_map.mpr ?_
      intro S _ q₀ _ η σ r _ _
      exact Iff.rfl
  | succ m ih =>
      intro hm
      refine sup_le (ih (by omega)) (MeasurableSpace.generateFrom_le ?_)
      rintro A ⟨y, j, x, rfl⟩
      intro q₀ hq₀ η σ r hσ hB
      have hq : U ((η, σ, r) : Data d) k q₀.1 ≤ q₀.2 := hB q₀ hq₀
      have hU := U_update_unread hσ q₀ (c q₀) hq (m + 1) hm
      have hmono : ∀ z : Site d, U ((η, σ, r) : Data d) (m + 1) z
          ≤ U ((η, σ, r) : Data d) k z := fun z => particleOdometer_mono _ _ hm
      have hkey : j + 1 ≤ U ((η, σ, r) : Data d) (m + 1) y →
          Function.update σ q₀ (c q₀) (y, j) = σ (y, j) := by
        intro h1
        refine Function.update_of_ne ?_ _ _
        rintro rfl
        have := hmono y
        simp only at hq
        omega
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · show j + 1 ≤ U ((η, Function.update σ q₀ (c q₀), r) : Data d) (m + 1) y
          rw [hU y]; exact h1
        · show Function.update σ q₀ (c q₀) (y, j) = x
          rw [hkey h1]; exact h2
      · rintro ⟨h1, h2⟩
        have h1' : j + 1 ≤ U ((η, σ, r) : Data d) (m + 1) y := by
          rw [← hU y]; exact h1
        refine ⟨h1', ?_⟩
        show σ (y, j) = x
        rw [← hkey h1']; exact h2

/-! ### The event that a family of instructions is unread -/

/-- The realizations for which every index of `s` is still unread after `k`
rounds. -/
def unreadSet (d k : ℕ) (s : Finset (Site d × ℕ)) : Set (Data d) :=
  {ω : Data d | ∀ q ∈ s, U ω k q.1 ≤ q.2}

theorem measurableSet_unreadSet (k : ℕ) (s : Finset (Site d × ℕ)) :
    MeasurableSet (unreadSet d k s) := by
  have hrw : unreadSet d k s = ⋂ q ∈ s, {ω : Data d | U ω k q.1 ≤ q.2} := by
    ext ω; simp [unreadSet]
  rw [hrw]
  refine MeasurableSet.biInter (Finset.countable_toSet s) fun q _ => ?_
  exact (measurable_U k q.1) (Set.to_countable {m : ℕ | m ≤ q.2}).measurableSet

/-- Overwriting one of the instructions of `s` does not change whether the
whole family is unread. -/
theorem mem_unreadSet_update_iff {k : ℕ} {s : Finset (Site d × ℕ)}
    {η : Site d → ℤ} {σ : Site d × ℕ → Site d} {r : Label d × ℕ → ℝ}
    (hσ : ∀ q, σ q ∈ nbrFinset q.1) {q₀ : Site d × ℕ} (hq₀ : q₀ ∈ s)
    {c : Site d} (hc : c ∈ nbrFinset q₀.1) :
    (((η, σ, r) : Data d) ∈ unreadSet d k s
      ↔ ((η, Function.update σ q₀ c, r) : Data d) ∈ unreadSet d k s) := by
  constructor
  · intro h
    have hq : U ((η, σ, r) : Data d) k q₀.1 ≤ q₀.2 := h q₀ hq₀
    have hU := U_update_unread hσ q₀ c hq k le_rfl
    intro q hq'
    rw [hU q.1]
    exact h q hq'
  · intro h
    have hq' : U ((η, Function.update σ q₀ c, r) : Data d) k q₀.1 ≤ q₀.2 := h q₀ hq₀
    have hq : U ((η, σ, r) : Data d) k q₀.1 ≤ q₀.2 :=
      (U_le_update_iff hσ q₀ hc k).mp hq'
    have hU := U_update_unread hσ q₀ c hq k le_rfl
    intro q hqs
    rw [← hU q.1]
    exact h q hqs

/-! ### The product rule for one configuration -/

/-- The product of the indicators of a finite family of sets is the indicator
of the set where all of them hold. -/
theorem prod_indicator_setOf {α ι : Type*} [DecidableEq ι] (s : Finset ι)
    (S : ι → Set α) (ω : α) :
    ∏ q ∈ s, Set.indicator (S q) (fun _ => (1 : ℝ)) ω
      = Set.indicator {x : α | ∀ q ∈ s, x ∈ S q} (fun _ => (1 : ℝ)) ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih]
      by_cases h1 : ω ∈ S a
      · rw [Set.indicator_of_mem h1, one_mul]
        by_cases h2 : ω ∈ {x : α | ∀ q ∈ s, x ∈ S q}
        · rw [Set.indicator_of_mem h2, Set.indicator_of_mem]
          intro q hq
          rcases Finset.mem_insert.mp hq with rfl | hq'
          · exact h1
          · exact h2 q hq'
        · rw [Set.indicator_of_notMem h2, Set.indicator_of_notMem]
          intro hcon
          exact h2 fun q hq => hcon q (Finset.mem_insert_of_mem hq)
      · rw [Set.indicator_of_notMem h1, zero_mul, Set.indicator_of_notMem]
        intro hcon
        exact h1 (hcon a (Finset.mem_insert_self a s))

/-- The product rule with the configuration held fixed: a set that does not
see the instructions of `s` splits off the prescribed values. -/
theorem exposure_core_given (hd : 1 ≤ d) (s : Finset (Site d × ℕ))
    (f : Site d × ℕ → Site d) {W : Set (Data d)} (hW : MeasurableSet W)
    (hinv : ∀ q₀ ∈ s, ∀ (η : Site d → ℤ) (σ : Site d × ℕ → Site d) (r : Label d × ℕ → ℝ),
      (∀ q, σ q ∈ nbrFinset q.1) →
        ((((η, σ, r) : Data d) ∈ W)
          ↔ (((η, Function.update σ q₀ (q₀.1 + unit ⟨0, hd⟩), r) : Data d) ∈ W)))
    (η : Site d → ℤ) :
    ∫ p : Randomness d, Set.indicator W (fun _ => (1 : ℝ)) ((η, p) : Data d)
        * ∏ q ∈ s, Set.indicator ({f q} : Set (Site d)) (fun _ => (1 : ℝ)) (p.1 q)
        ∂(stackRankLaw d)
      = (∏ q ∈ s, kern d q.1 (f q))
        * ∫ p : Randomness d, Set.indicator W (fun _ => (1 : ℝ)) ((η, p) : Data d)
            ∂(stackRankLaw d) := by
  classical
  haveI : ∀ q : Site d × ℕ, IsProbabilityMeasure (instructionLaw (d := d) q.1) :=
    fun q => instructionLaw_isProbability hd q.1
  haveI := rankLaw_isProbability d
  haveI : IsProbabilityMeasure (stackRankLaw d) := by
    unfold stackRankLaw stackLaw
    infer_instance
  set i₀ : Fin d := ⟨0, hd⟩ with hi₀
  set c : Site d × ℕ → Site d := fun q => q.1 + unit i₀ with hcdef
  have hcmem : ∀ q : Site d × ℕ, c q ∈ nbrFinset q.1 := fun q => mem_nbrFinset_add q.1 i₀
  have hembP : Measurable fun p : Randomness d => ((η, nbrProj i₀ p.1, p.2) : Data d) :=
    measurable_const.prodMk
      (((measurable_nbrProj i₀).comp measurable_fst).prodMk measurable_snd)
  set G : Randomness d → ℝ :=
    fun p => Set.indicator W (fun _ => (1 : ℝ)) ((η, nbrProj i₀ p.1, p.2) : Data d) with hG
  have hGmeas : Measurable G := (measurable_one.indicator hW).comp hembP
  have hGint : Integrable G (stackRankLaw d) := by
    refine (integrable_const (1 : ℝ)).mono' hGmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [hG]
    by_cases hp : ((η, nbrProj i₀ p.1, p.2) : Data d) ∈ W
    · simp [Set.indicator_of_mem hp]
    · simp [Set.indicator_of_notMem hp]
  have hGinv : ∀ q₀ ∈ s, ∀ (σ : Site d × ℕ → Site d) (r : Label d × ℕ → ℝ),
      G (Function.update σ q₀ (c q₀), r) = G (σ, r) := by
    intro q₀ hq₀ σ r
    show Set.indicator W (fun _ => (1 : ℝ))
        ((η, nbrProj i₀ (Function.update σ q₀ (c q₀)), r) : Data d)
      = Set.indicator W (fun _ => (1 : ℝ)) ((η, nbrProj i₀ σ, r) : Data d)
    rw [nbrProj_update i₀ σ q₀ (hcmem q₀)]
    have hiff := hinv q₀ hq₀ η (nbrProj i₀ σ) r (nbrProj_mem i₀ σ)
    by_cases h1 : ((η, nbrProj i₀ σ, r) : Data d) ∈ W
    · rw [Set.indicator_of_mem (hiff.mp h1), Set.indicator_of_mem h1]
    · rw [Set.indicator_of_notMem (fun hcon => h1 (hiff.mpr hcon)),
        Set.indicator_of_notMem h1]
  have hlaw : stackRankLaw d
      = (Measure.infinitePi fun q : Site d × ℕ => instructionLaw (d := d) q.1).prod
          (rankLaw d) := rfl
  have hlib := LatticeProb.integral_mul_prod_indicator_eval_prod
    (μ := fun q : Site d × ℕ => instructionLaw (d := d) q.1) (ν := rankLaw d)
    c G hGmeas (by rw [← hlaw]; exact hGint)
    (fun q => ({f q} : Set (Site d))) (fun q => measurableSet_singleton _) s
    (fun q₀ hq₀ σ r => hGinv q₀ hq₀ σ r)
  have hae : ∀ᵐ p ∂(stackRankLaw d), nbrProj i₀ p.1 = p.1 := by
    have h1 : ∀ᵐ σ ∂(stackLaw d), nbrProj i₀ σ = σ :=
      (stackLaw_ae_nbr hd).mono fun σ hσ => nbrProj_eq_self hσ
    exact (Measure.quasiMeasurePreserving_fst).ae h1
  have hFG : ∀ᵐ p ∂(stackRankLaw d),
      G p = Set.indicator W (fun _ => (1 : ℝ)) ((η, p) : Data d) :=
    hae.mono fun p hp => by
      show Set.indicator W (fun _ => (1 : ℝ)) ((η, nbrProj i₀ p.1, p.2) : Data d)
        = Set.indicator W (fun _ => (1 : ℝ)) ((η, p) : Data d)
      rw [hp]
  have hleft : ∫ p : Randomness d, Set.indicator W (fun _ => (1 : ℝ)) ((η, p) : Data d)
        * ∏ q ∈ s, Set.indicator ({f q} : Set (Site d)) (fun _ => (1 : ℝ)) (p.1 q)
        ∂(stackRankLaw d)
      = ∫ p : Randomness d, G p
        * ∏ q ∈ s, Set.indicator ({f q} : Set (Site d)) (fun _ => (1 : ℝ)) (p.1 q)
        ∂(stackRankLaw d) :=
    integral_congr_ae (hFG.mono fun p hp => by simp only [hp])
  rw [hleft, hlaw, hlib, ← hlaw, integral_congr_ae hFG]
  congr 1
  refine Finset.prod_congr rfl fun q _ => ?_
  exact instructionLaw_singleton hd q.1 (f q)

/-! ### The product rule under the law -/

theorem integrable_indicator_one {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {S : Set α} (hS : MeasurableSet S) :
    Integrable (Set.indicator S (fun _ => (1 : ℝ))) μ := by
  refine (integrable_const (1 : ℝ)).mono' (measurable_one.indicator hS).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases h : x ∈ S
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- The realizations whose instructions at the indices of `s` are the
prescribed ones. -/
def prescribedSet (d : ℕ) (s : Finset (Site d × ℕ)) (f : Site d × ℕ → Site d) :
    Set (Data d) :=
  {ω : Data d | ∀ q ∈ s, ω.2.1 q ∈ ({f q} : Set (Site d))}

theorem measurableSet_prescribedSet (s : Finset (Site d × ℕ)) (f : Site d × ℕ → Site d) :
    MeasurableSet (prescribedSet d s f) := by
  have hrw : prescribedSet d s f = ⋂ q ∈ s, {ω : Data d | ω.2.1 q = f q} := by
    ext ω; simp [prescribedSet]
  rw [hrw]
  refine MeasurableSet.biInter (Finset.countable_toSet s) fun q _ => ?_
  have hm : Measurable fun ω : Data d => ω.2.1 q :=
    (measurable_pi_apply q).comp (measurable_fst.comp measurable_snd)
  exact hm (measurableSet_singleton (f q))

theorem indicator_prescribed_mul (s : Finset (Site d × ℕ)) (f : Site d × ℕ → Site d)
    (W : Set (Data d)) :
    (fun ω : Data d => Set.indicator W (fun _ => (1 : ℝ)) ω
        * ∏ q ∈ s, Set.indicator ({f q} : Set (Site d)) (fun _ => (1 : ℝ)) (ω.2.1 q))
      = Set.indicator (prescribedSet d s f ∩ W) (fun _ => (1 : ℝ)) := by
  have h := LatticeProb.prod_indicator_eval_eq (X := fun _ : Site d × ℕ => Site d) s
    (fun q => ({f q} : Set (Site d))) (fun ω : Data d => ω.2.1)
    (Set.indicator W (fun _ => (1 : ℝ)))
  rw [h]
  exact Set.indicator_indicator _ _ _

/-- A set of the exposure filtration, intersected with the event that the
family `s` is unread, splits off the prescribed instructions. -/
theorem exposure_core (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (k : ℕ) (s : Finset (Site d × ℕ)) (f : Site d × ℕ → Site d)
    {A : Set (Data d)} (hA : MeasurableSet[expFiltration d k] A) :
    ∫ ω, Set.indicator (prescribedSet d s f ∩ (A ∩ unreadSet d k s))
        (fun _ => (1 : ℝ)) ω ∂(law d ν)
      = (∏ q ∈ s, kern d q.1 (f q))
        * ∫ ω, Set.indicator (A ∩ unreadSet d k s) (fun _ => (1 : ℝ)) ω ∂(law d ν) := by
  classical
  haveI := rankLaw_isProbability d
  haveI : IsProbabilityMeasure (stackRankLaw d) := by
    unfold stackRankLaw stackLaw
    haveI : ∀ q : Site d × ℕ, IsProbabilityMeasure (instructionLaw (d := d) q.1) :=
      fun q => instructionLaw_isProbability hd q.1
    infer_instance
  haveI : IsProbabilityMeasure (law d ν) := by
    unfold law
    haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
      unfold LatticeProb.iidLaw; infer_instance
    haveI : IsProbabilityMeasure ((LatticeProb.stackLaw d).prod (LatticeProb.rankLaw d)) :=
      inferInstanceAs (IsProbabilityMeasure (stackRankLaw d))
    infer_instance
  set i₀ : Fin d := ⟨0, hd⟩ with hi₀
  set W : Set (Data d) := A ∩ unreadSet d k s with hWdef
  have hAamb : MeasurableSet A := expFiltration_le d k A hA
  have hW : MeasurableSet W := hAamb.inter (measurableSet_unreadSet k s)
  have hinv : ∀ q₀ ∈ s, ∀ (η : Site d → ℤ) (σ : Site d × ℕ → Site d) (r : Label d × ℕ → ℝ),
      (∀ q, σ q ∈ nbrFinset q.1) →
        ((((η, σ, r) : Data d) ∈ W)
          ↔ (((η, Function.update σ q₀ (q₀.1 + unit i₀), r) : Data d) ∈ W)) := by
    intro q₀ hq₀ η σ r hσ
    have hcmem : q₀.1 + unit i₀ ∈ nbrFinset q₀.1 := mem_nbrFinset_add q₀.1 i₀
    have hunread := mem_unreadSet_update_iff (k := k) (s := s) (η := η) (σ := σ) (r := r)
      hσ hq₀ hcmem
    constructor
    · rintro ⟨hA1, hB1⟩
      refine ⟨?_, hunread.mp hB1⟩
      exact (expFiltration_le_updInvSpace (d := d) k s (fun q => q.1 + unit i₀) k le_rfl A hA
        q₀ hq₀ η σ r hσ hB1).mp hA1
    · rintro ⟨hA1, hB1⟩
      have hB0 : ((η, σ, r) : Data d) ∈ unreadSet d k s := hunread.mpr hB1
      refine ⟨?_, hB0⟩
      exact (expFiltration_le_updInvSpace (d := d) k s (fun q => q.1 + unit i₀) k le_rfl A hA
        q₀ hq₀ η σ r hσ hB0).mpr hA1
  have hlawprod : law d ν = (LatticeProb.iidLaw d ν).prod (stackRankLaw d) := rfl
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hleft : ∫ ω, Set.indicator (prescribedSet d s f ∩ W) (fun _ => (1 : ℝ)) ω ∂(law d ν)
      = ∫ η, ∫ p : Randomness d, Set.indicator W (fun _ => (1 : ℝ)) ((η, p) : Data d)
          * ∏ q ∈ s, Set.indicator ({f q} : Set (Site d)) (fun _ => (1 : ℝ)) (p.1 q)
          ∂(stackRankLaw d) ∂(LatticeProb.iidLaw d ν) := by
    have hfun : ∀ ω : Data d, Set.indicator (prescribedSet d s f ∩ W) (fun _ => (1 : ℝ)) ω
        = Set.indicator W (fun _ => (1 : ℝ)) ω
          * ∏ q ∈ s, Set.indicator ({f q} : Set (Site d)) (fun _ => (1 : ℝ)) (ω.2.1 q) :=
      fun ω => (congrFun (indicator_prescribed_mul s f W) ω).symm
    rw [integral_congr_ae (Filter.Eventually.of_forall hfun), hlawprod]
    refine integral_prod _ ?_
    rw [← hlawprod]
    exact (integrable_indicator_one ((measurableSet_prescribedSet s f).inter hW)).congr
      (Filter.Eventually.of_forall hfun)
  have hright : ∫ ω, Set.indicator W (fun _ => (1 : ℝ)) ω ∂(law d ν)
      = ∫ η, ∫ p : Randomness d, Set.indicator W (fun _ => (1 : ℝ)) ((η, p) : Data d)
          ∂(stackRankLaw d) ∂(LatticeProb.iidLaw d ν) := by
    rw [hlawprod]
    exact integral_prod _ (by rw [← hlawprod]; exact integrable_indicator_one hW)
  rw [hleft, hright, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  exact exposure_core_given hd s f hW hinv η

/-! ### The conditional form -/

theorem measurableSet_unreadSet_expFiltration (k : ℕ) (s : Finset (Site d × ℕ)) :
    MeasurableSet[expFiltration d k] (unreadSet d k s) := by
  have hrw : unreadSet d k s = ⋂ q ∈ s, {ω : Data d | U ω k q.1 ≤ q.2} := by
    ext ω; simp [unreadSet]
  rw [hrw]
  exact @MeasurableSet.biInter _ _ (expFiltration d k) _ _ (Finset.countable_toSet s)
    fun q _ => measurableSet_U_le_expFiltration k q.1 q.2

set_option maxHeartbeats 1000000 in
/-- `lem:exposure`, second clause: conditionally on the exposure filtration,
prescribing the destination of each of a family of unread instructions has the
product of the transition probabilities as its conditional probability, on the
event that all of them are still unread. -/
theorem exposure_condExp (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (k : ℕ) (s : Finset (Site d × ℕ)) (f : Site d × ℕ → Site d) :
    (law d ν)[fun ω : Data d => ∏ q ∈ s,
        Set.indicator {ω' : Data d | U ω' k q.1 ≤ q.2 ∧ ω'.2.1 q = f q}
          (fun _ => (1 : ℝ)) ω | expFiltration d k]
      =ᵐ[law d ν] fun ω : Data d =>
        (∏ q ∈ s, Set.indicator {ω' : Data d | U ω' k q.1 ≤ q.2} (fun _ => (1 : ℝ)) ω)
          * ∏ q ∈ s, kern d q.1 (f q) := by
  classical
  haveI := rankLaw_isProbability d
  haveI : IsProbabilityMeasure (stackRankLaw d) := by
    unfold stackRankLaw stackLaw
    haveI : ∀ q : Site d × ℕ, IsProbabilityMeasure (instructionLaw (d := d) q.1) :=
      fun q => instructionLaw_isProbability hd q.1
    infer_instance
  haveI : IsProbabilityMeasure (law d ν) := by
    unfold law
    haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
      unfold LatticeProb.iidLaw; infer_instance
    haveI : IsProbabilityMeasure ((LatticeProb.stackLaw d).prod (LatticeProb.rankLaw d)) :=
      inferInstanceAs (IsProbabilityMeasure (stackRankLaw d))
    infer_instance
  have hle := expFiltration_le d k
  haveI : IsFiniteMeasure ((law d ν).trim hle) := isFiniteMeasure_trim hle
  set C : ℝ := ∏ q ∈ s, kern d q.1 (f q) with hC
  set E : Set (Data d) := unreadSet d k s ∩ prescribedSet d s f with hE
  have hEmeas : MeasurableSet E :=
    (measurableSet_unreadSet k s).inter (measurableSet_prescribedSet s f)
  have hFeq : (fun ω : Data d => ∏ q ∈ s,
      Set.indicator {ω' : Data d | U ω' k q.1 ≤ q.2 ∧ ω'.2.1 q = f q}
        (fun _ => (1 : ℝ)) ω) = Set.indicator E (fun _ => (1 : ℝ)) := by
    funext ω
    rw [prod_indicator_setOf s
      (fun q => {ω' : Data d | U ω' k q.1 ≤ q.2 ∧ ω'.2.1 q = f q}) ω]
    congr 1
    ext x
    constructor
    · intro h
      exact ⟨fun q hq => (h q hq).1, fun q hq => (h q hq).2⟩
    · rintro ⟨h1, h2⟩ q hq
      exact ⟨h1 q hq, h2 q hq⟩
  have hGeq : (fun ω : Data d =>
      (∏ q ∈ s, Set.indicator {ω' : Data d | U ω' k q.1 ≤ q.2} (fun _ => (1 : ℝ)) ω) * C)
      = fun ω : Data d => Set.indicator (unreadSet d k s) (fun _ => (1 : ℝ)) ω * C := by
    funext ω
    rw [prod_indicator_setOf s (fun q => {ω' : Data d | U ω' k q.1 ≤ q.2}) ω]
    rfl
  rw [hFeq, hGeq]
  refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hle
    (integrable_indicator_one hEmeas) ?_ ?_ ?_).symm
  · intro S _ _
    exact ((integrable_indicator_one (measurableSet_unreadSet k s)).mul_const C).integrableOn
  · intro S hS _
    have hSamb : MeasurableSet S := hle S hS
    have h1 : ∀ ω : Data d, Set.indicator S
        (fun ω' : Data d => Set.indicator (unreadSet d k s) (fun _ => (1 : ℝ)) ω' * C) ω
        = Set.indicator (S ∩ unreadSet d k s) (fun _ => (1 : ℝ)) ω * C := by
      intro ω
      by_cases h : ω ∈ S
      · rw [Set.indicator_of_mem h]
        by_cases h' : ω ∈ unreadSet d k s
        · rw [Set.indicator_of_mem h', Set.indicator_of_mem (Set.mem_inter h h')]
        · rw [Set.indicator_of_notMem h',
            Set.indicator_of_notMem (fun hcon => h' hcon.2)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hcon => h hcon.1)]
        ring
    have h2 : Set.indicator S (Set.indicator E (fun _ => (1 : ℝ)))
        = Set.indicator (prescribedSet d s f ∩ (S ∩ unreadSet d k s)) (fun _ => (1 : ℝ)) := by
      rw [Set.indicator_indicator]
      congr 1
      ext x
      simp only [hE, Set.mem_inter_iff]
      tauto
    rw [← integral_indicator hSamb, ← integral_indicator hSamb,
      integral_congr_ae (Filter.Eventually.of_forall h1), h2,
      exposure_core hd ν k s f hS, integral_mul_const]
    ring
  · have h0 : Measurable[expFiltration d k] (fun _ : Data d => (1 : ℝ)) := measurable_const
    have h1 : Measurable[expFiltration d k]
        (Set.indicator (unreadSet d k s) (fun _ : Data d => (1 : ℝ))) :=
      h0.indicator (measurableSet_unreadSet_expFiltration k s)
    have hmeas : Measurable[expFiltration d k]
        fun ω : Data d => Set.indicator (unreadSet d k s) (fun _ => (1 : ℝ)) ω * C :=
      h1.mul_const C
    exact hmeas.aestronglyMeasurable

end Parking

end
