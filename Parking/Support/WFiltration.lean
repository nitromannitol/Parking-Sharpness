/-
The filtration of `lem:w-martingale`.

The exploration reveals the instructions one at a time, and the sigma-algebra
of what it has revealed by step `i` is realized here as the comap of a self-map
of the space of realizations: `Parking.wTrunc i` erases every instruction the
exploration has not yet read, replacing it by a fixed neighbour of its own site.
Two facts make that the right object.  Erasing the unread instructions does not
change the first `i` steps of the exploration, because the exploration reads
only what it has revealed, so `wTrunc i` is idempotent and the comaps increase
with `i`.  And a set that is decided by the first `i` steps is its own preimage
under `wTrunc i`, so it lies in the comap without any factorization through the
revealed values; that is what makes the increments measurable for the next
sigma-algebra of the filtration.
-/
import Parking.Support.WReads

noncomputable section

open MeasureTheory

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### The increment at step `i` is decided by the first `i + 1` steps -/

/-- **The increment of the martingale is decided by the instructions the
exploration has read up to and including its own step.** -/
theorem wXi_congr_of_reads (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (n i : ℕ) {σ σ' : Site d × ℕ → Site d}
    (hread : ∀ k, k < i + 1 → explIdx i₀ η ρ n k σ = explIdx i₀ η ρ n k σ' ∧
      σ (explIdx i₀ η ρ n k σ) = σ' (explIdx i₀ η ρ n k σ)) :
    wXi i₀ n i ((η, σ, ρ) : Data d) = wXi i₀ n i ((η, σ', ρ) : Data d) := by
  classical
  set ω : Data d := ((η, nbrProj i₀ σ, ρ) : Data d) with hω
  set ω' : Data d := ((η, nbrProj i₀ σ', ρ) : Data d) with hω'
  have hwXi : wXi i₀ n i ((η, σ, ρ) : Data d)
      = ((blockPrefix ω n (n - 1)).map (wInc ω n)).getD i 0 := rfl
  have hwXi' : wXi i₀ n i ((η, σ', ρ) : Data d)
      = ((blockPrefix ω' n (n - 1)).map (wInc ω' n)).getD i 0 := rfl
  have hblocks : ∀ k, k ≤ n - 1 → (blockPrefix ω n (k - 1)).length ≤ i + 1 →
      ∀ s, 1 ≤ s → s ≤ k → blockAt ω (blockRad n s) s = blockAt ω' (blockRad n s) s :=
    blockAt_agree_of_readsPrefix i₀ η ρ n (i + 1) hread
  have hidx : explIdx i₀ η ρ n i σ = explIdx i₀ η ρ n i σ' :=
    readsOnlyRevealed_explIdx i₀ η ρ n i σ σ' fun k hk => hread k (by omega)
  have hvali : ω.2.1 (explIdx i₀ η ρ n i σ) = ω'.2.1 (explIdx i₀ η ρ n i σ) := by
    obtain ⟨-, hval⟩ := hread i (by omega)
    show nbrProj i₀ σ (explIdx i₀ η ρ n i σ) = nbrProj i₀ σ' (explIdx i₀ η ρ n i σ)
    simp only [nbrProj, hval]
  rw [hwXi, hwXi']
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
    have heq : blockPrefix ω n K = blockPrefix ω' n K :=
      blockPrefix_congr (hblocks K hKle (by omega))
    have hKlt' : i < (blockPrefix ω' n K).length := by rw [← heq]; exact hKlt
    have hi' : i < (blockPrefix ω' n (n - 1)).length :=
      lt_of_lt_of_le hKlt' (length_blockPrefix_mono ω' n hKle)
    -- the `i`-th entry of the two lists
    have hgetD : (blockPrefix ω n (n - 1)).getD i (padSite d n, i)
        = (blockPrefix ω n K).getD i (padSite d n, i) := by
      rw [blockPrefix_append ω n hKle, List.getD_append _ _ _ _ hKlt]
    have hgetD' : (blockPrefix ω' n (n - 1)).getD i (padSite d n, i)
        = (blockPrefix ω' n K).getD i (padSite d n, i) := by
      rw [blockPrefix_append ω' n hKle, List.getD_append _ _ _ _ hKlt']
    set q : Site d × ℕ := explIdx i₀ η ρ n i σ with hq
    have hqmem : q ∈ blockPrefix ω n K := by
      rw [hq, explIdx, hgetD, List.getD_eq_getElem _ _ hKlt]
      exact List.getElem_mem hKlt
    obtain ⟨r, hr1, hrK, hrq⟩ := mem_blockPrefix.mp hqmem
    have hrq' : q ∈ blockAt ω' (blockRad n r) r := by
      rw [← hblocks K hKle (by omega) r hr1 hrK]
      exact hrq
    have hround : roundOf ω q = r := roundOf_eq_of_mem_blockAt hr1 hrq
    have hround' : roundOf ω' q = r := roundOf_eq_of_mem_blockAt hr1 hrq'
    have hmap : ((blockPrefix ω n (n - 1)).map (wInc ω n)).getD i 0 = wInc ω n q := by
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
      congr 1
      rw [hq, explIdx, List.getD_eq_getElem _ _ hi]
    have hmap' : ((blockPrefix ω' n (n - 1)).map (wInc ω' n)).getD i 0 = wInc ω' n q := by
      rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map]
      congr 1
      have hq' : explIdx i₀ η ρ n i σ = (blockPrefix ω' n (n - 1))[i]'hi' := by
        rw [show explIdx i₀ η ρ n i σ = explIdx i₀ η ρ n i σ' from hidx, explIdx,
          List.getD_eq_getElem _ _ hi']
      exact hq'.symm
    rw [hmap, hmap', wInc, wInc, hround, hround', hvali]
  · have hlen : (blockPrefix ω n (n - 1)).length ≤ i := Nat.le_of_not_lt hi
    have hlen' : (blockPrefix ω n ((n - 1) - 1)).length ≤ i + 1 :=
      le_trans (le_trans (length_blockPrefix_mono ω n (by omega)) hlen) (by omega)
    have heq : blockPrefix ω n (n - 1) = blockPrefix ω' n (n - 1) :=
      blockPrefix_congr (hblocks (n - 1) le_rfl hlen')
    rw [List.getD_eq_default _ _ (by simpa using hlen),
      List.getD_eq_default _ _ (by rw [← heq]; simpa using hlen)]


/-! ### The realization with the unread instructions erased -/

open scoped Classical in
/-- The realization with every instruction the exploration has not read before
step `i` replaced by a fixed neighbour of its own site.  Its comap is the
sigma-algebra of what the exploration has revealed by step `i`. -/
def wTrunc (i₀ : Fin d) (n i : ℕ) (ω : Data d) : Data d :=
  (ω.1, fun q => if ∃ k, k < i ∧ wPair i₀ n k ω = q then ω.2.1 q else q.1 + unit i₀, ω.2.2)

theorem wTrunc_fst (i₀ : Fin d) (n i : ℕ) (ω : Data d) : (wTrunc i₀ n i ω).1 = ω.1 := rfl

theorem wTrunc_rank (i₀ : Fin d) (n i : ℕ) (ω : Data d) :
    (wTrunc i₀ n i ω).2.2 = ω.2.2 := rfl

open scoped Classical in
theorem wTrunc_stack_of_read (i₀ : Fin d) (n i : ℕ) (ω : Data d) {k : ℕ} (hk : k < i) :
    (wTrunc i₀ n i ω).2.1 (wPair i₀ n k ω) = ω.2.1 (wPair i₀ n k ω) := by
  show (if ∃ j, j < i ∧ wPair i₀ n j ω = wPair i₀ n k ω then _ else _) = _
  rw [if_pos ⟨k, hk, rfl⟩]

/-- **Erasing the unread instructions does not change the steps the exploration
has already taken.** -/
theorem wPair_wTrunc (i₀ : Fin d) (n i : ℕ) (ω : Data d) :
    ∀ k, k ≤ i → wPair i₀ n k (wTrunc i₀ n i ω) = wPair i₀ n k ω := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro hk
      have hstep : ∀ j, j < k →
          explIdx i₀ ω.1 ω.2.2 n j ω.2.1 = explIdx i₀ ω.1 ω.2.2 n j (wTrunc i₀ n i ω).2.1 ∧
            ω.2.1 (explIdx i₀ ω.1 ω.2.2 n j ω.2.1)
              = (wTrunc i₀ n i ω).2.1 (explIdx i₀ ω.1 ω.2.2 n j ω.2.1) := by
        intro j hj
        refine ⟨(ih j hj (by omega)).symm, (wTrunc_stack_of_read i₀ n i ω (by omega)).symm⟩
      exact (readsOnlyRevealed_explIdx i₀ ω.1 ω.2.2 n k _ _ hstep).symm

/-- **The erasure is idempotent**, and erasing more first changes nothing. -/
theorem wTrunc_wTrunc (i₀ : Fin d) (n : ℕ) {i j : ℕ} (hij : i ≤ j) (ω : Data d) :
    wTrunc i₀ n i (wTrunc i₀ n j ω) = wTrunc i₀ n i ω := by
  classical
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext q
  have hcond : (∃ k, k < i ∧ wPair i₀ n k (wTrunc i₀ n j ω) = q)
      ↔ ∃ k, k < i ∧ wPair i₀ n k ω = q := by
    constructor
    · rintro ⟨k, hk, hq⟩
      exact ⟨k, hk, by rwa [wPair_wTrunc i₀ n j ω k (by omega)] at hq⟩
    · rintro ⟨k, hk, hq⟩
      exact ⟨k, hk, by rwa [wPair_wTrunc i₀ n j ω k (by omega)]⟩
  show (if ∃ k, k < i ∧ wPair i₀ n k (wTrunc i₀ n j ω) = q then (wTrunc i₀ n j ω).2.1 q
      else q.1 + unit i₀) = if ∃ k, k < i ∧ wPair i₀ n k ω = q then ω.2.1 q else q.1 + unit i₀
  by_cases h : ∃ k, k < i ∧ wPair i₀ n k ω = q
  · obtain ⟨k, hk, rfl⟩ := h
    rw [if_pos (hcond.mpr ⟨k, hk, rfl⟩), if_pos ⟨k, hk, rfl⟩]
    exact wTrunc_stack_of_read i₀ n j ω (by omega)
  · rw [if_neg h, if_neg fun hc => h (hcond.mp hc)]

/-! ### The filtration -/

open scoped Classical in
theorem measurable_wTrunc (i₀ : Fin d) (n i : ℕ) : Measurable (wTrunc i₀ n i) := by
  classical
  refine measurable_fst.prodMk (Measurable.prodMk ?_ (measurable_snd.comp measurable_snd))
  refine measurable_pi_lambda _ fun q => ?_
  have hset : MeasurableSet {ω : Data d | ∃ k, k < i ∧ wPair i₀ n k ω = q} := by
    have : {ω : Data d | ∃ k, k < i ∧ wPair i₀ n k ω = q}
        = ⋃ k ∈ Finset.range i, (wPair i₀ n k) ⁻¹' {q} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
        Finset.mem_range, exists_prop]
    rw [this]
    exact MeasurableSet.biUnion (Finset.range i).countable_toSet
      fun k _ => (measurable_wPair i₀ n k) (measurableSet_singleton q)
  exact Measurable.ite hset
    ((measurable_pi_apply q).comp (measurable_fst.comp measurable_snd)) measurable_const

/-- The sigma-algebra of what the exploration has revealed by step `i`. -/
@[reducible] def wFiltration (i₀ : Fin d) (n i : ℕ) : MeasurableSpace (Data d) :=
  MeasurableSpace.comap (wTrunc i₀ n i) inferInstance

theorem wFiltration_le (i₀ : Fin d) (n i : ℕ) :
    wFiltration i₀ n i ≤ inferInstanceAs (MeasurableSpace (Data d)) :=
  (measurable_wTrunc i₀ n i).comap_le

theorem wFiltration_mono (i₀ : Fin d) (n : ℕ) : Monotone (wFiltration i₀ n) := by
  intro i j hij A hA
  obtain ⟨B, hB, rfl⟩ := hA
  refine ⟨wTrunc i₀ n i ⁻¹' B, (measurable_wTrunc i₀ n i) hB, ?_⟩
  ext ω
  simp only [Set.mem_preimage, wTrunc_wTrunc i₀ n hij ω]

/-! ### The increment at step `i` is measurable for the next sigma-algebra -/

/-- **The increment at step `i` does not see the instructions the exploration
has not read by step `i + 1`.** -/
theorem wXi_wTrunc (i₀ : Fin d) (n i : ℕ) (ω : Data d) :
    wXi i₀ n i (wTrunc i₀ n (i + 1) ω) = wXi i₀ n i ω := by
  have hread : ∀ k, k < i + 1 →
      explIdx i₀ ω.1 ω.2.2 n k ω.2.1 = explIdx i₀ ω.1 ω.2.2 n k (wTrunc i₀ n (i + 1) ω).2.1 ∧
        ω.2.1 (explIdx i₀ ω.1 ω.2.2 n k ω.2.1)
          = (wTrunc i₀ n (i + 1) ω).2.1 (explIdx i₀ ω.1 ω.2.2 n k ω.2.1) := by
    intro k hk
    exact ⟨(wPair_wTrunc i₀ n (i + 1) ω k (by omega)).symm,
      (wTrunc_stack_of_read i₀ n (i + 1) ω hk).symm⟩
  exact (wXi_congr_of_reads i₀ ω.1 ω.2.2 n i hread).symm

/-- **The increment at step `i` is measurable for the sigma-algebra of what the
exploration has revealed by step `i + 1`.** -/
theorem measurable_wXi_wFiltration (i₀ : Fin d) (n i : ℕ) :
    Measurable[wFiltration i₀ n (i + 1)] (wXi i₀ n i) := by
  have hself : Measurable[wFiltration i₀ n (i + 1),
      inferInstanceAs (MeasurableSpace (Data d))] (wTrunc i₀ n (i + 1)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hcomp : Measurable[wFiltration i₀ n (i + 1)]
      (fun ω => wXi i₀ n i (wTrunc i₀ n (i + 1) ω)) :=
    (measurable_wXi i₀ n i).comp hself
  simpa only [wXi_wTrunc] using hcomp

end Parking

end
