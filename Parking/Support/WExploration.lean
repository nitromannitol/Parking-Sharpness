/-
The exploration of `lem:w-martingale`: the instructions are revealed round by
round, and inside a round in the order the block lists them.

The order has to be adaptive.  A fixed enumeration of the pairs cannot be used:
the conditional law of an instruction first read in round `s` is prescribed only
given the instructions of the earlier rounds, so the rounds must be completed
one at a time, and a round holds infinitely many pairs unless the pairs it
actually reads are listed, which depends on the realization.  `blockPrefix`
lists exactly those pairs, and the two facts that make it an exploration are
`Parking.blockAt_disjoint`, so that no instruction is read twice, and
`Parking.blockAt_agree_of_notMem`, so that the list up to any step is decided by
the instructions the exploration has already read.

The instructions are read through `Parking.nbrProj`, which forces every one of
them to be a neighbour of its site and is the identity almost surely; the
exploration parks the steps past the end of the list at a site no block reaches,
so that they are fresh as well.
-/
import Parking.Support.WMartingale
import Parking.Support.Agree
import Parking.Support.Exposure
import LatticeProb.Prob.Exploration

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### The site the exploration parks at -/

def padSite (d n : ℕ) : Site d := fun _ => (blockRad n 1 : ℤ) + 1

theorem padSite_notMem_box (hd : 1 ≤ d) (n R : ℕ) (h : R ≤ blockRad n 1) :
    padSite d n ∉ boxFinset (0 : Site d) R := by
  intro hc
  have := mem_boxFinset_iff.mp hc ⟨0, hd⟩
  simp only [padSite, Pi.zero_apply, sub_zero] at this
  have h' : ((blockRad n 1 : ℤ) + 1) ≤ (R : ℤ) := le_trans (le_abs_self _) this
  omega

theorem site_mem_box_of_mem_blockPrefix {ω : Data d} {n k : ℕ} {q : Site d × ℕ}
    (h : q ∈ blockPrefix ω n k) : q.1 ∈ boxFinset (0 : Site d) (blockRad n 1) := by
  obtain ⟨s, h1, -, hq⟩ := mem_blockPrefix.mp h
  exact boxFinset_mono (blockRad_antitone h1) (mem_blockAt.mp hq).1

def explIdx (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (n : ℕ)
    (i : ℕ) (σ : Site d × ℕ → Site d) : Site d × ℕ :=
  (blockPrefix ((η, nbrProj i₀ σ, ρ) : Data d) n (n - 1)).getD i (padSite d n, i)

theorem explIdx_of_lt {i₀ : Fin d} {η ρ n i σ}
    (h : i < (blockPrefix ((η, nbrProj i₀ σ, ρ) : Data d) n (n - 1)).length) :
    explIdx i₀ η ρ n i σ ∈ blockPrefix ((η, nbrProj i₀ σ, ρ) : Data d) n (n - 1) := by
  rw [explIdx, List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem explIdx_of_le {i₀ : Fin d} {η ρ n i σ}
    (h : (blockPrefix ((η, nbrProj i₀ σ, ρ) : Data d) n (n - 1)).length ≤ i) :
    explIdx i₀ η ρ n i σ = (padSite d n, i) := by
  rw [explIdx, List.getD_eq_default _ _ h]

theorem explIdx_eq_prefix {i₀ : Fin d} {η ρ n} {σ} {k m : ℕ} (hk : k ≤ n - 1)
    (hm : m < (blockPrefix ((η, nbrProj i₀ σ, ρ) : Data d) n k).length) :
    explIdx i₀ η ρ n m σ
      = (blockPrefix ((η, nbrProj i₀ σ, ρ) : Data d) n k).getD m (padSite d n, m) := by
  rw [explIdx, blockPrefix_append _ n hk, List.getD_append _ _ _ _ hm]

/-! ### The exploration never reads an instruction twice -/

theorem explIdx_fresh (hd : 1 ≤ d) (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (n : ℕ) (i : ℕ) (σ : Site d × ℕ → Site d) :
    ∀ k, k < i → explIdx i₀ η ρ n k σ ≠ explIdx i₀ η ρ n i σ := by
  classical
  intro k hk
  set L := blockPrefix ((η, nbrProj i₀ σ, ρ) : Data d) n (n - 1) with hL
  by_cases hi : i < L.length
  · have hklt : k < L.length := lt_trans hk hi
    rw [explIdx, explIdx, List.getD_eq_getElem _ _ hklt, List.getD_eq_getElem _ _ hi]
    intro hcon
    have := (List.nodup_iff_injective_getElem.mp (nodup_blockPrefix
      ((η, nbrProj i₀ σ, ρ) : Data d) n (n - 1))) (a₁ := ⟨k, hklt⟩) (a₂ := ⟨i, hi⟩) hcon
    have hval : k = i := by simpa using congrArg Fin.val this
    omega
  · rw [explIdx_of_le (Nat.le_of_not_lt hi)]
    by_cases hkl : k < L.length
    · rw [explIdx, List.getD_eq_getElem _ _ hkl]
      intro hcon
      have hmem : L[k] ∈ L := List.getElem_mem hkl
      have hbox := site_mem_box_of_mem_blockPrefix hmem
      rw [hcon] at hbox
      exact padSite_notMem_box hd n (blockRad n 1) le_rfl hbox
    · rw [explIdx_of_le (Nat.le_of_not_lt hkl)]
      intro hcon
      exact absurd (congrArg Prod.snd hcon) (by omega)

/-! ### The exploration chooses its next instruction from the ones it has read -/

/-- Every instruction of a prefix that ends before position `i` is read by the
exploration before step `i`. -/
theorem exists_explIdx_of_mem_blockPrefix {i₀ : Fin d} {η ρ n} {σ} {k i : ℕ}
    (hk : k ≤ n - 1)
    (hlen : (blockPrefix ((η, nbrProj i₀ σ, ρ) : Data d) n k).length ≤ i)
    {q : Site d × ℕ} (hq : q ∈ blockPrefix ((η, nbrProj i₀ σ, ρ) : Data d) n k) :
    ∃ m, m < i ∧ explIdx i₀ η ρ n m σ = q := by
  obtain ⟨m, hm, hval⟩ := List.mem_iff_getElem.mp hq
  refine ⟨m, lt_of_lt_of_le hm hlen, ?_⟩
  rw [explIdx_eq_prefix hk hm, List.getD_eq_getElem _ _ hm, hval]

/-- **The exploration chooses its next instruction from the ones it has already
read.**  This is the predictability clause of `LatticeProb.IsExploration`. -/
theorem explIdx_pred (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (n i : ℕ) (σ : Site d × ℕ → Site d) (j : Site d × ℕ) (c : Site d)
    (hfresh : ∀ k, k < i → explIdx i₀ η ρ n k σ ≠ j) :
    explIdx i₀ η ρ n i (Function.update σ j c) = explIdx i₀ η ρ n i σ := by
  classical
  set c' : Site d := if c ∈ nbrFinset j.1 then c else j.1 + unit i₀ with hc'
  have hupd : nbrProj i₀ (Function.update σ j c) = Function.update (nbrProj i₀ σ) j c' :=
    nbrProj_update' i₀ σ j c
  set ω : Data d := ((η, nbrProj i₀ σ, ρ) : Data d) with hω
  set ω' : Data d := ((η, Function.update (nbrProj i₀ σ) j c', ρ) : Data d) with hω'
  have hrw : ((η, nbrProj i₀ (Function.update σ j c), ρ) : Data d) = ω' := by
    rw [hω', hupd]
  have hs : StepsToNeighbour (toDriver ω) :=
    stepsToNeighbour_of_mem fun q => nbrProj_mem i₀ σ q
  have heta : ω.1 = ω'.1 := rfl
  have hrank : ω.2.2 = ω'.2.2 := rfl
  have hstack : ∀ q : Site d × ℕ, q ≠ j → ω.2.1 q = ω'.2.1 q := by
    intro q hq
    show nbrProj i₀ σ q = Function.update (nbrProj i₀ σ) j c' q
    rw [Function.update_of_ne hq]
  have hkey : ∀ k, k ≤ n - 1 →
      (∀ s, 1 ≤ s → s < k → j ∉ blockAt ω (blockRad n s) s) →
      blockPrefix ω n k = blockPrefix ω' n k := by
    intro k hk hnot
    refine blockPrefix_congr ?_
    exact blockAt_agree_of_notMem hs heta hrank j hstack n k (by omega) hnot
  by_cases hi : i < (blockPrefix ω n (n - 1)).length
  · have hex : ∃ k, i < (blockPrefix ω n k).length := ⟨n - 1, hi⟩
    set K := Nat.find hex with hK
    have hKlt : i < (blockPrefix ω n K).length := Nat.find_spec hex
    have hKle : K ≤ n - 1 := Nat.find_min' hex hi
    have hK1 : 1 ≤ K := by
      rcases Nat.eq_zero_or_pos K with h | h
      · exfalso
        rw [h] at hKlt
        simp [blockPrefix] at hKlt
      · exact h
    have hKmin : (blockPrefix ω n (K - 1)).length ≤ i := by
      by_contra hc
      exact Nat.find_min hex (m := K - 1) (by omega) (Nat.lt_of_not_le hc)
    have hnot : ∀ s, 1 ≤ s → s < K → j ∉ blockAt ω (blockRad n s) s := by
      intro s h1 h2 hmem
      have hjmem : j ∈ blockPrefix ω n (K - 1) := mem_blockPrefix.mpr ⟨s, h1, by omega, hmem⟩
      obtain ⟨m, hm, hval⟩ :=
        exists_explIdx_of_mem_blockPrefix (by omega) hKmin hjmem
      exact hfresh m hm hval
    have heq := hkey K hKle hnot
    have hKlt' : i < (blockPrefix ω' n K).length := by rw [← heq]; exact hKlt
    rw [explIdx, explIdx, hrw, blockPrefix_append ω' n hKle, blockPrefix_append ω n hKle,
      List.getD_append _ _ _ _ hKlt', List.getD_append _ _ _ _ hKlt, heq]
  · have hlen : (blockPrefix ω n (n - 1)).length ≤ i := Nat.le_of_not_lt hi
    have hnot : ∀ s, 1 ≤ s → s < n - 1 → j ∉ blockAt ω (blockRad n s) s := by
      intro s h1 h2 hmem
      have hjmem : j ∈ blockPrefix ω n (n - 1) := mem_blockPrefix.mpr ⟨s, h1, by omega, hmem⟩
      obtain ⟨m, hm, hval⟩ := exists_explIdx_of_mem_blockPrefix le_rfl hlen hjmem
      exact hfresh m hm hval
    have heq := hkey (n - 1) le_rfl hnot
    rw [explIdx, explIdx, hrw, heq]

/-! ### The exploration is measurable -/

/-- A map determined by a measurable observable with countably many values is
measurable. -/
theorem measurable_of_determined {α β γ : Type*} [Nonempty α] [MeasurableSpace α]
    [MeasurableSpace β] [Countable γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (r : α → γ) (hr : Measurable r) (f : α → β)
    (h : ∀ a a', r a = r a' → f a = f a') : Measurable f := by
  classical
  refine measurable_of_countable_partition r hr f
    (fun c _ => if hc : ∃ a, r a = c then f hc.choose else f (Classical.arbitrary α))
    (fun _ => measurable_const) fun a => ?_
  have hc : ∃ a', r a' = r a := ⟨a, rfl⟩
  rw [dif_pos hc]
  exact (h _ _ hc.choose_spec).symm

/-- A block is determined by the odometers of its two rounds inside its box. -/
theorem blockAt_eq_of_U_eq {ω ω' : Data d} {R s : ℕ}
    (h : ∀ y ∈ boxFinset (0 : Site d) R, U ω (s - 1) y = U ω' (s - 1) y ∧ U ω s y = U ω' s y) :
    blockAt ω R s = blockAt ω' R s := by
  classical
  ext q
  rw [mem_blockAt, mem_blockAt]
  constructor
  · rintro ⟨hq, h1, h2⟩
    obtain ⟨e1, e2⟩ := h q.1 hq
    exact ⟨hq, e1 ▸ h1, e2 ▸ h2⟩
  · rintro ⟨hq, h1, h2⟩
    obtain ⟨e1, e2⟩ := h q.1 hq
    exact ⟨hq, e1 ▸ h1, e2 ▸ h2⟩

theorem measurable_U_of_stack (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (t : ℕ) (y : Site d) :
    Measurable fun σ : Site d × ℕ → Site d => U ((η, nbrProj i₀ σ, ρ) : Data d) t y :=
  (measurable_U t y).comp
    (measurable_const.prodMk ((measurable_nbrProj i₀).prodMk measurable_const))

/-- The odometers the exploration reads: the two rounds of every block, inside
the largest of the boxes. -/
def explObs (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (n : ℕ)
    (σ : Site d × ℕ → Site d) :
    Fin n → {y : Site d // y ∈ boxFinset (0 : Site d) (blockRad n 1)} → ℕ :=
  fun s y => U ((η, nbrProj i₀ σ, ρ) : Data d) s.val y.val

theorem measurable_explObs (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (n : ℕ) :
    Measurable (explObs i₀ η ρ n) :=
  measurable_pi_lambda _ fun s => measurable_pi_lambda _ fun y =>
    measurable_U_of_stack i₀ η ρ s.val y.val

theorem measurable_explIdx (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (n i : ℕ) :
    Measurable (explIdx i₀ η ρ n i) := by
  classical
  refine measurable_of_determined (explObs i₀ η ρ n) (measurable_explObs i₀ η ρ n) _ ?_
  intro σ σ' hobs
  have hblock : ∀ s, 1 ≤ s → s ≤ n - 1 →
      blockAt ((η, nbrProj i₀ σ, ρ) : Data d) (blockRad n s) s
        = blockAt ((η, nbrProj i₀ σ', ρ) : Data d) (blockRad n s) s := by
    intro s h1 h2
    have hsn : s < n := by omega
    refine blockAt_eq_of_U_eq fun y hy => ?_
    have hybig : y ∈ boxFinset (0 : Site d) (blockRad n 1) :=
      boxFinset_mono (blockRad_antitone h1) hy
    constructor
    · exact congrFun (congrFun hobs ⟨s - 1, by omega⟩) ⟨y, hybig⟩
    · exact congrFun (congrFun hobs ⟨s, hsn⟩) ⟨y, hybig⟩
  rw [explIdx, explIdx, blockPrefix_congr hblock]

/-! ### The revealed displacements -/

/-- The displacement an instruction records, read through the projection that
forces it to be a neighbour of its site. -/
def wG (i₀ : Fin d) (q : Site d × ℕ) : Site d → Site d := expG i₀ (Sum.inl q)

theorem measurable_wG (i₀ : Fin d) (q : Site d × ℕ) : Measurable (wG i₀ q) :=
  measurable_expG i₀ (Sum.inl q)

theorem instructionLaw_map_wG (i₀ : Fin d) (q : Site d × ℕ) :
    (instructionLaw q.1).map (wG i₀ q) = LatticeProb.displacementLaw d :=
  expLaw_map_expG i₀ (Sum.inl q)

/-- **The order in which `lem:w-martingale` reveals the instructions is an
exploration.** -/
theorem isExploration_explIdx (hd : 1 ≤ d) (i₀ : Fin d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (n : ℕ) :
    LatticeProb.IsExploration (X := fun _ : Site d × ℕ => Site d) (explIdx i₀ η ρ n) := by
  classical
  exact ⟨fun i => measurable_explIdx i₀ η ρ n i,
    fun i σ k hk => explIdx_fresh hd i₀ η ρ n i σ k hk,
    fun i σ j c hfresh => explIdx_pred i₀ η ρ n i σ j c hfresh⟩

/-- **The revealed displacements are independent draws from the one-step law**,
whatever the configuration and the uniform variables are. -/
theorem map_revealed_explIdx (hd : 1 ≤ d) (i₀ : Fin d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (n : ℕ) :
    (LatticeProb.stackLaw d).map (LatticeProb.revealed (explIdx i₀ η ρ n) (wG i₀))
      = Measure.infinitePi fun _ : ℕ => LatticeProb.displacementLaw d := by
  classical
  haveI : ∀ q : Site d × ℕ, IsProbabilityMeasure (instructionLaw (d := d) q.1) :=
    fun q => LatticeProb.instructionLaw_isProbability hd q.1
  exact LatticeProb.map_revealed (X := fun _ : Site d × ℕ => Site d)
    (fun q : Site d × ℕ => instructionLaw q.1) (isExploration_explIdx hd i₀ η ρ n)
    (measurable_wG i₀) (instructionLaw_map_wG i₀)

/-! ### The joint law of the configuration, the ranks and the displacements -/

/-- The configuration and the uniform variables, in one coordinate. -/
abbrev ConfRank (d : ℕ) : Type := (Site d → ℤ) × (Label d × ℕ → ℝ)

/-- The instruction the exploration reads at step `i`, as a function of the
whole realization. -/
def wExplIdx (i₀ : Fin d) (n i : ℕ) (p : ConfRank d × (Site d × ℕ → Site d)) : Site d × ℕ :=
  explIdx i₀ p.1.1 p.1.2 n i p.2

theorem measurable_wExplIdx (i₀ : Fin d) (n i : ℕ) : Measurable (wExplIdx i₀ n i) := by
  classical
  refine measurable_of_determined
    (fun p : ConfRank d × (Site d × ℕ → Site d) =>
      fun (s : Fin n) (y : {y : Site d // y ∈ boxFinset (0 : Site d) (blockRad n 1)}) =>
        U ((p.1.1, nbrProj i₀ p.2, p.1.2) : Data d) s.val y.val)
    (measurable_pi_lambda _ fun s => measurable_pi_lambda _ fun y =>
      (measurable_U s.val y.val).comp
        ((measurable_fst.comp measurable_fst).prodMk
          (((measurable_nbrProj i₀).comp measurable_snd).prodMk
            (measurable_snd.comp measurable_fst)))) _ ?_
  intro p p' hobs
  have hblock : ∀ s, 1 ≤ s → s ≤ n - 1 →
      blockAt ((p.1.1, nbrProj i₀ p.2, p.1.2) : Data d) (blockRad n s) s
        = blockAt ((p'.1.1, nbrProj i₀ p'.2, p'.1.2) : Data d) (blockRad n s) s := by
    intro s h1 h2
    have hsn : s < n := by omega
    refine blockAt_eq_of_U_eq fun y hy => ?_
    have hybig : y ∈ boxFinset (0 : Site d) (blockRad n 1) :=
      boxFinset_mono (blockRad_antitone h1) hy
    exact ⟨congrFun (congrFun hobs ⟨s - 1, by omega⟩) ⟨y, hybig⟩,
      congrFun (congrFun hobs ⟨s, hsn⟩) ⟨y, hybig⟩⟩
  show explIdx i₀ p.1.1 p.1.2 n i p.2 = explIdx i₀ p'.1.1 p'.1.2 n i p'.2
  rw [explIdx, explIdx, blockPrefix_congr hblock]

theorem measurable_wRevealed (i₀ : Fin d) (n : ℕ) :
    Measurable fun p : ConfRank d × (Site d × ℕ → Site d) =>
      LatticeProb.revealed (explIdx i₀ p.1.1 p.1.2 n) (wG i₀) p.2 := by
  classical
  refine measurable_pi_lambda _ fun i => ?_
  refine measurable_of_countable_partition (wExplIdx i₀ n i) (measurable_wExplIdx i₀ n i) _
    (fun q p => wG i₀ q (p.2 q))
    (fun q => (measurable_wG i₀ q).comp ((measurable_pi_apply q).comp measurable_snd))
    fun p => rfl

/-- The configuration, the uniform variables, and the displacements the
exploration reveals. -/
def wData (i₀ : Fin d) (n : ℕ) (ω : Data d) : ConfRank d × (ℕ → Site d) :=
  ((ω.1, ω.2.2), LatticeProb.revealed (explIdx i₀ ω.1 ω.2.2 n) (wG i₀) ω.2.1)

theorem measurable_wData (i₀ : Fin d) (n : ℕ) : Measurable (wData i₀ n) := by
  have hemb : Measurable fun ω : Data d =>
      (((ω.1, ω.2.2), ω.2.1) : ConfRank d × (Site d × ℕ → Site d)) :=
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk
      (measurable_fst.comp measurable_snd)
  have hfun : (fun ω : Data d =>
        LatticeProb.revealed (explIdx i₀ ω.1 ω.2.2 n) (wG i₀) ω.2.1)
      = (fun p : ConfRank d × (Site d × ℕ → Site d) =>
          LatticeProb.revealed (explIdx i₀ p.1.1 p.1.2 n) (wG i₀) p.2)
        ∘ (fun ω : Data d => (((ω.1, ω.2.2), ω.2.1) : ConfRank d × (Site d × ℕ → Site d))) :=
    rfl
  have h2 : Measurable fun ω : Data d =>
      LatticeProb.revealed (explIdx i₀ ω.1 ω.2.2 n) (wG i₀) ω.2.1 := by
    rw [hfun]
    exact (measurable_wRevealed i₀ n).comp hemb
  exact (measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk h2

/-- **The configuration, the uniform variables and the revealed displacements
are independent**, the displacements being independent draws from the one-step
law.  This is the exploration of `lem:w-martingale` in the form the martingale
uses. -/
theorem map_wData (hd : 1 ≤ d) (i₀ : Fin d) (n : ℕ) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] :
    (law d ν).map (wData i₀ n)
      = ((LatticeProb.iidLaw d ν).prod (LatticeProb.rankLaw d)).prod
        (Measure.infinitePi fun _ : ℕ => LatticeProb.displacementLaw d) := by
  classical
  haveI : ∀ q : Site d × ℕ, IsProbabilityMeasure (instructionLaw (d := d) q.1) :=
    fun q => LatticeProb.instructionLaw_isProbability hd q.1
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  haveI : IsProbabilityMeasure (LatticeProb.stackLaw d) := by
    unfold LatticeProb.stackLaw; infer_instance
  haveI : IsProbabilityMeasure ((LatticeProb.iidLaw d ν).prod (LatticeProb.rankLaw d)) :=
    inferInstance
  have hreshuf : Measurable fun x : ConfRank d × (Site d × ℕ → Site d) =>
      ((x.1.1, (x.2, x.1.2)) : Data d) :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hres : ((((LatticeProb.iidLaw d ν).prod (LatticeProb.rankLaw d)).prod
        (LatticeProb.stackLaw d)).map fun x => ((x.1.1, (x.2, x.1.2)) : Data d))
      = law d ν :=
    map_reshuffle (LatticeProb.iidLaw d ν) (LatticeProb.rankLaw d) (LatticeProb.stackLaw d)
  have hcomp : ∀ x : ConfRank d × (Site d × ℕ → Site d),
      wData i₀ n ((x.1.1, (x.2, x.1.2)) : Data d)
        = (x.1, LatticeProb.revealed (explIdx i₀ x.1.1 x.1.2 n) (wG i₀) x.2) := fun _ => rfl
  calc (law d ν).map (wData i₀ n)
      = ((((LatticeProb.iidLaw d ν).prod (LatticeProb.rankLaw d)).prod
            (LatticeProb.stackLaw d)).map fun x => ((x.1.1, (x.2, x.1.2)) : Data d)).map
          (wData i₀ n) := by rw [hres]
    _ = (((LatticeProb.iidLaw d ν).prod (LatticeProb.rankLaw d)).prod
            (LatticeProb.stackLaw d)).map
          (fun x => wData i₀ n ((x.1.1, (x.2, x.1.2)) : Data d)) := by
        rw [Measure.map_map (measurable_wData i₀ n) hreshuf]; rfl
    _ = (((LatticeProb.iidLaw d ν).prod (LatticeProb.rankLaw d)).prod
            (LatticeProb.stackLaw d)).map
          (fun p : ConfRank d × (Site d × ℕ → Site d) =>
            (p.1, LatticeProb.revealed (explIdx i₀ p.1.1 p.1.2 n) (wG i₀) p.2)) := by
        exact congrArg (fun f => Measure.map f _) (funext hcomp)
    _ = ((LatticeProb.iidLaw d ν).prod (LatticeProb.rankLaw d)).prod
          (Measure.infinitePi fun _ : ℕ => LatticeProb.displacementLaw d) :=
        LatticeProb.map_prod_pair_of_forall_map
          (F := fun (y : ConfRank d) (σ : Site d × ℕ → Site d) =>
            LatticeProb.revealed (explIdx i₀ y.1 y.2 n) (wG i₀) σ)
          ((LatticeProb.iidLaw d ν).prod (LatticeProb.rankLaw d)) (LatticeProb.stackLaw d)
          (measurable_wRevealed i₀ n) fun y => map_revealed_explIdx hd i₀ y.1 y.2 n

/-- The sum over the list the exploration reads is the sum over the blocks. -/
theorem sum_map_blockPrefix (ω : Data d) (n k : ℕ) (f : Site d × ℕ → ℝ) :
    ((blockPrefix ω n k).map f).sum
      = ∑ s ∈ Finset.Icc 1 k, ∑ q ∈ blockAt ω (blockRad n s) s, f q := by
  classical
  induction k with
  | zero => simp [blockPrefix]
  | succ k ih =>
      rw [blockPrefix_append ω n (Nat.le_succ k)]
      have hrange : List.range' (1 + k) (k + 1 - k) = [1 + k] := by
        have : k + 1 - k = 1 := by omega
        rw [this]
        rfl
      rw [hrange]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append,
        List.sum_append, ih]
      have hone : ((blockList ω n (1 + k)).map f).sum
          = ∑ q ∈ blockAt ω (blockRad n (k + 1)) (k + 1), f q := by
        have hk : 1 + k = k + 1 := by omega
        rw [hk, blockList]
        exact Finset.sum_map_toList _ f
      rw [hone, Finset.sum_Icc_succ_top (by omega)]

/-! ### The increment at one instruction -/

/-- The round in which an instruction is first read. -/
def roundOf (ω : Data d) (q : Site d × ℕ) : ℕ := sInf {r : ℕ | q.2 < U ω r q.1}

theorem roundOf_eq_of_mem_blockAt {ω : Data d} {R s : ℕ} {q : Site d × ℕ} (hs : 1 ≤ s)
    (hq : q ∈ blockAt ω R s) : roundOf ω q = s := by
  obtain ⟨-, h1, h2⟩ := mem_blockAt.mp hq
  have hmem : s ∈ {r : ℕ | q.2 < U ω r q.1} := h2
  refine le_antisymm (Nat.sInf_le hmem) ?_
  by_contra hlt
  have hlt' : sInf {r : ℕ | q.2 < U ω r q.1} < s := Nat.lt_of_not_le hlt
  have hin : sInf {r : ℕ | q.2 < U ω r q.1} ∈ {r : ℕ | q.2 < U ω r q.1} :=
    Nat.sInf_mem ⟨s, hmem⟩
  have hle : U ω (sInf {r : ℕ | q.2 < U ω r q.1}) q.1 ≤ U ω (s - 1) q.1 :=
    particleOdometer_mono (toDriver ω) q.1 (by omega)
  have : q.2 < U ω (s - 1) q.1 := lt_of_lt_of_le hin hle
  omega

/-- The increment the martingale of `lem:w-martingale` carries at one
instruction: the discrepancy between the truncated Green function at the site
the instruction points to and its average over the neighbours. -/
def wInc (ω : Data d) (n : ℕ) (q : Site d × ℕ) : ℝ :=
  green d (n - roundOf ω q) (ω.2.1 q) - walkOp (green d (n - roundOf ω q)) q.1

theorem sum_wInc_blockAt (ω : Data d) (n : ℕ) {R s : ℕ} (hs : 1 ≤ s) :
    ∑ q ∈ blockAt ω R s, wInc ω n q
      = ∑ q ∈ blockAt ω R s, (green d (n - s) (ω.2.1 q) - walkOp (green d (n - s)) q.1) :=
  Finset.sum_congr rfl fun q hq => by rw [wInc, roundOf_eq_of_mem_blockAt hs hq]

/-- **The error at the origin is the sum of the increments along the list the
exploration reads.**  This is the first display of `lem:w-martingale`, with the
sum written over the order in which the instructions are revealed. -/
theorem wErr_zero_eq_sum_list (hd : 1 ≤ d) (ω : Data d)
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) (n : ℕ) :
    wErr ω n 0 = ((blockPrefix ω n (n - 1)).map (wInc ω n)).sum := by
  rw [sum_map_blockPrefix ω n (n - 1) (wInc ω n), wErr_zero_eq_blockRad hd ω hstep n]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [sum_wInc_blockAt ω n (Finset.mem_Icc.mp hs).1]

/-! ### The increments of the martingale -/

/-- The realization with its instructions projected onto the neighbours of
their site: the identity almost surely, and what makes the bound on the
increments hold for every realization. -/
def wProj (i₀ : Fin d) (ω : Data d) : Data d := (ω.1, nbrProj i₀ ω.2.1, ω.2.2)

theorem wProj_stepsToNeighbour (i₀ : Fin d) (ω : Data d) (q : Site d × ℕ) :
    (wProj i₀ ω).2.1 q ∈ nbrFinset q.1 := nbrProj_mem i₀ ω.2.1 q

/-- The increment of `lem:w-martingale` at step `i`. -/
def wXi (i₀ : Fin d) (n i : ℕ) (ω : Data d) : ℝ :=
  ((blockPrefix (wProj i₀ ω) n (n - 1)).map (wInc (wProj i₀ ω) n)).getD i 0

theorem wXi_eq_zero_of_le {i₀ : Fin d} {n i : ℕ} {ω : Data d}
    (h : (blockPrefix (wProj i₀ ω) n (n - 1)).length ≤ i) : wXi i₀ n i ω = 0 := by
  rw [wXi, List.getD_eq_default]
  simpa using h

/-- Only finitely many increments are nonzero, for every realization. -/
theorem wXi_eventually_zero (i₀ : Fin d) (n : ℕ) (ω : Data d) :
    ∀ i, (blockPrefix (wProj i₀ ω) n (n - 1)).length ≤ i → wXi i₀ n i ω = 0 :=
  fun _ h => wXi_eq_zero_of_le h

/-- **The increments are bounded by the increment of the truncated Green
function**, for every realization. -/
theorem abs_wXi_le (hd : 1 ≤ d) (i₀ : Fin d) (n : ℕ) (hn : 1 ≤ n) (i : ℕ) (ω : Data d) :
    |wXi i₀ n i ω| ≤ greenIncrement d n := by
  classical
  set ω' := wProj i₀ ω with hω'
  set L := blockPrefix ω' n (n - 1) with hL
  have hzero : (0 : ℝ) ≤ greenIncrement d n := by
    have h := le_greenIncrement (d := d) hd (n := n) (m := 0) (by omega)
      (y := 0) (z := 0 + unit ⟨0, hd⟩) (mem_nbrFinset_add 0 ⟨0, hd⟩)
    refine le_trans ?_ h
    exact abs_nonneg _
  by_cases hi : i < L.length
  · have hmaplen : i < (L.map (wInc ω' n)).length := by simpa using hi
    have hmem : L[i] ∈ L := List.getElem_mem hi
    obtain ⟨s, h1, h2, hq⟩ := mem_blockPrefix.mp hmem
    have hround : roundOf ω' L[i] = s := roundOf_eq_of_mem_blockAt h1 hq
    have hval : wXi i₀ n i ω = wInc ω' n L[i] := by
      rw [wXi, List.getD_eq_getElem _ _ hmaplen, List.getElem_map]
    rw [hval, wInc, hround]
    exact le_greenIncrement hd (by omega) (wProj_stepsToNeighbour i₀ ω L[i])
  · rw [wXi_eq_zero_of_le (Nat.le_of_not_lt hi), abs_zero]
    exact hzero

theorem sum_range_getD (l : List ℝ) : ∑ i ∈ Finset.range l.length, l.getD i 0 = l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [ih, List.sum_cons]
      ring

theorem tsum_getD_eq_sum (l : List ℝ) : ∑' i : ℕ, l.getD i 0 = l.sum := by
  rw [tsum_eq_sum (s := Finset.range l.length) fun i hi => ?_, sum_range_getD]
  exact List.getD_eq_default _ _ (by simpa using hi)


/-- **The error at the origin is the sum of the increments**, almost surely.
The identity is pathwise on the realizations whose instructions are neighbours
of their site, which is a full-measure event. -/
theorem wErr_ae_eq_tsum_wXi (hd : 1 ≤ d) (i₀ : Fin d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] (n : ℕ) :
    ∀ᵐ ω ∂(law d ν), wErr ω n 0 = ∑' i : ℕ, wXi i₀ n i ω := by
  refine (ae_stack_nbr_law hd ν).mono fun ω hω => ?_
  have hstack : nbrProj i₀ ω.2.1 = ω.2.1 := by
    funext q
    rw [nbrProj, if_pos (hω q)]
  have hproj : wProj i₀ ω = ω := by
    show ((ω.1, nbrProj i₀ ω.2.1, ω.2.2) : Data d) = ω
    rw [hstack]
  have hxi : ∀ i, wXi i₀ n i ω = ((blockPrefix ω n (n - 1)).map (wInc ω n)).getD i 0 := by
    intro i
    rw [wXi, hproj]
  simp only [hxi]
  rw [tsum_getD_eq_sum]
  exact wErr_zero_eq_sum_list hd ω hω n

/-! ### The increments are measurable and integrable -/

/-- The instruction the exploration reads at step `i`, as a function of the
whole realization of the data. -/
def wPair (i₀ : Fin d) (n i : ℕ) (ω : Data d) : Site d × ℕ :=
  explIdx i₀ ω.1 ω.2.2 n i ω.2.1

theorem measurable_wPair (i₀ : Fin d) (n i : ℕ) : Measurable (wPair i₀ n i) := by
  have hemb : Measurable fun ω : Data d =>
      (((ω.1, ω.2.2), ω.2.1) : ConfRank d × (Site d × ℕ → Site d)) :=
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk
      (measurable_fst.comp measurable_snd)
  have hfun : wPair i₀ n i = (wExplIdx i₀ n i) ∘
      (fun ω : Data d => (((ω.1, ω.2.2), ω.2.1) : ConfRank d × (Site d × ℕ → Site d))) := rfl
  rw [hfun]
  exact (measurable_wExplIdx i₀ n i).comp hemb

/-- The observables that decide the increment at step `i`: the odometers of
every round inside the largest box, the instruction the exploration reads, and
the site that instruction points to. -/
def wIncObs (i₀ : Fin d) (n i : ℕ) (ω : Data d) :
    (Fin n → {y : Site d // y ∈ boxFinset (0 : Site d) (blockRad n 1)} → ℕ) ×
      (Site d × ℕ) × Site d :=
  (fun s y => U (wProj i₀ ω) s.val y.val, wPair i₀ n i ω,
    (wProj i₀ ω).2.1 (wPair i₀ n i ω))

theorem measurable_wIncObs (i₀ : Fin d) (n i : ℕ) : Measurable (wIncObs i₀ n i) := by
  classical
  have hproj : Measurable (wProj i₀ (d := d)) :=
    measurable_fst.prodMk
      (((measurable_nbrProj i₀).comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  refine (measurable_pi_lambda _ fun s : Fin n => measurable_pi_lambda _
    fun y : {y : Site d // y ∈ boxFinset (0 : Site d) (blockRad n 1)} =>
      (measurable_U s.val y.val).comp hproj).prodMk
    ((measurable_wPair i₀ n i).prodMk ?_)
  refine measurable_of_countable_partition (wPair i₀ n i) (measurable_wPair i₀ n i) _
    (fun q ω => (wProj i₀ ω).2.1 q)
    (fun q => (measurable_pi_apply q).comp
      (measurable_fst.comp (measurable_snd.comp hproj))) fun _ => rfl

theorem measurable_wXi (i₀ : Fin d) (n i : ℕ) : Measurable (wXi i₀ n i) := by
  classical
  refine measurable_of_determined (wIncObs i₀ n i) (measurable_wIncObs i₀ n i) _ ?_
  intro ω ω2 hobs
  have htable : (fun (s : Fin n) (y : {y : Site d // y ∈ boxFinset (0 : Site d) (blockRad n 1)})
      => U (wProj i₀ ω) s.val y.val)
      = fun s y => U (wProj i₀ ω2) s.val y.val := congrArg Prod.fst hobs
  have hpair : wPair i₀ n i ω = wPair i₀ n i ω2 :=
    congrArg Prod.fst (congrArg Prod.snd hobs)
  have hval : (wProj i₀ ω).2.1 (wPair i₀ n i ω) = (wProj i₀ ω2).2.1 (wPair i₀ n i ω2) :=
    congrArg Prod.snd (congrArg Prod.snd hobs)
  have hblock : ∀ s, 1 ≤ s → s ≤ n - 1 →
      blockAt (wProj i₀ ω) (blockRad n s) s = blockAt (wProj i₀ ω2) (blockRad n s) s := by
    intro s h1 h2
    refine blockAt_eq_of_U_eq fun y hy => ?_
    have hybig : y ∈ boxFinset (0 : Site d) (blockRad n 1) :=
      boxFinset_mono (blockRad_antitone h1) hy
    exact ⟨congrFun (congrFun htable ⟨s - 1, by omega⟩) ⟨y, hybig⟩,
      congrFun (congrFun htable ⟨s, by omega⟩) ⟨y, hybig⟩⟩
  have hL : blockPrefix (wProj i₀ ω) n (n - 1) = blockPrefix (wProj i₀ ω2) n (n - 1) :=
    blockPrefix_congr hblock
  set L := blockPrefix (wProj i₀ ω) n (n - 1) with hLdef
  by_cases hi : i < L.length
  · have hi' : i < (blockPrefix (wProj i₀ ω2) n (n - 1)).length := by rw [← hL]; exact hi
    have hmaplen : i < (L.map (wInc (wProj i₀ ω) n)).length := by simpa using hi
    have hmaplen' : i < ((blockPrefix (wProj i₀ ω2) n (n - 1)).map
        (wInc (wProj i₀ ω2) n)).length := by simpa using hi'
    have hq : L[i] ∈ L := List.getElem_mem hi
    obtain ⟨s, h1, h2, hqs⟩ := mem_blockPrefix.mp hq
    have hround : roundOf (wProj i₀ ω) L[i] = s := roundOf_eq_of_mem_blockAt h1 hqs
    have hqs' : L[i] ∈ blockAt (wProj i₀ ω2) (blockRad n s) s := by
      rw [← hblock s h1 h2]; exact hqs
    have hround' : roundOf (wProj i₀ ω2) L[i] = s := roundOf_eq_of_mem_blockAt h1 hqs'
    have hpairL : wPair i₀ n i ω = L[i] := by
      show (blockPrefix (wProj i₀ ω) n (n - 1)).getD i (padSite d n, i) = L[i]
      exact List.getD_eq_getElem _ _ hi
    have hgetL : (blockPrefix (wProj i₀ ω2) n (n - 1))[i]'hi' = L[i] :=
      (List.getElem_of_eq hL hi).symm
    rw [wXi, wXi, List.getD_eq_getElem _ _ hmaplen, List.getD_eq_getElem _ _ hmaplen',
      List.getElem_map, List.getElem_map, hgetL, wInc, wInc, hround, hround']
    congr 1
    have h1' : (wProj i₀ ω).2.1 L[i] = (wProj i₀ ω).2.1 (wPair i₀ n i ω) := by rw [hpairL]
    have h2' : (wProj i₀ ω2).2.1 (wPair i₀ n i ω2) = (wProj i₀ ω2).2.1 L[i] := by
      rw [← hpair, hpairL]
    rw [h1', hval, h2']
  · have hi' : ¬ i < (blockPrefix (wProj i₀ ω2) n (n - 1)).length := by rw [← hL]; exact hi
    rw [wXi_eq_zero_of_le (Nat.le_of_not_lt hi), wXi_eq_zero_of_le (Nat.le_of_not_lt hi')]


/-- The increments are integrable: they are measurable and bounded. -/
theorem integrable_wXi (hd : 1 ≤ d) (i₀ : Fin d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (i : ℕ) : Integrable (wXi i₀ n i) (law d ν) := by
  haveI := stackLaw_isProbability (d := d) hd
  haveI := rankLaw_isProbability d
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (law d ν) := by unfold law; infer_instance
  refine (integrable_const (greenIncrement d n)).mono'
    (measurable_wXi i₀ n i).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact abs_wXi_le hd i₀ n hn i ω

/-! ### Changing many instructions at once -/

/-- **The odometers of two rounds inside a box read only the instructions near
it.**  This is the simultaneous form of `Parking.U_congr_of_far`: the drivers
need not differ at one instruction only, and the conclusion covers the two
rounds a block is built from. -/
theorem U_agree_of_agree_box {ω ω' : Data d} (hs : StepsToNeighbour (toDriver ω))
    (heta : ω.1 = ω'.1) (hrank : ω.2.2 = ω'.2.2) (R t : ℕ)
    (hstack : ∀ q : Site d × ℕ, q.1 ∈ boxFinset (0 : Site d) (R + t + 2 * t * t) →
      ω.2.1 q = ω'.2.1 q) (y : Site d) (hy : y ∈ boxFinset (0 : Site d) R) :
    U ω t y = U ω' t y ∧ U ω (t + 1) y = U ω' (t + 1) y := by
  classical
  have hA : AgreeOn (toDriver ω) (toDriver ω') (0 : Site d) ((R + t) + 2 * t * t) := by
    refine ⟨fun z _ => congrFun heta z, fun z hz i => hstack (z, i) ?_,
      fun p _ s => congrFun hrank (p, s)⟩
    exact boxFinset_mono (by omega) hz
  have hSt := state_agree_box (D := toDriver ω) (D' := toDriver ω') hs 0 t (R + t) hA
  have hybig : y ∈ boxFinset (0 : Site d) (R + t) := boxFinset_mono (by omega) hy
  have hU : U ω t y = U ω' t y := hSt.departures y hybig
  refine ⟨hU, ?_⟩
  have hcand : (candidates ω.1 y t) = (candidates ω'.1 y t) := by rw [heta]
  have hact : (activeAt (toDriver ω) (state (toDriver ω) t) t y).card
      = (activeAt (toDriver ω') (state (toDriver ω') t) t y).card := by
    show ((candidates ω.1 y t).filter fun p =>
        (state (toDriver ω) t).active p ∧ (state (toDriver ω) t).pos p = y).card
      = ((candidates ω'.1 y t).filter fun p =>
        (state (toDriver ω') t).active p ∧ (state (toDriver ω') t).pos p = y).card
    rw [← hcand]
    congr 1
    refine Finset.filter_congr fun p hp => ?_
    have hpbox : p.1 ∈ boxFinset (0 : Site d) (R + t) :=
      mem_boxFinset_of_mem_candidates hy hp
    rw [hSt.active p hpbox, hSt.pos p hpbox]
  show U ω t y + activeCount (toDriver ω) t y = U ω' t y + activeCount (toDriver ω') t y
  rw [hU]
  exact congrArg _ hact


/-- **The block of a round is decided by the instructions near its box.**  The
simultaneous form of `Parking.blockAt_congr_of_far`. -/
theorem blockAt_agree_of_agree_box {ω ω' : Data d} (hs : StepsToNeighbour (toDriver ω))
    (heta : ω.1 = ω'.1) (hrank : ω.2.2 = ω'.2.2) (n s : ℕ) (hs1 : 1 ≤ s)
    (hstack : ∀ q : Site d × ℕ,
      q.1 ∈ boxFinset (0 : Site d) (blockRad n s + 2 * s * s) → ω.2.1 q = ω'.2.1 q) :
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
        ω.2.1 q = ω'.2.1 q := fun q hq => hstack q (boxFinset_mono hrad hq)
  obtain ⟨h1, h2⟩ := U_agree_of_agree_box hs heta hrank (blockRad n s) (s - 1) hst y hy
  rw [Nat.sub_add_cancel hs1] at h2
  exact ⟨h1, h2⟩

end Parking

end
