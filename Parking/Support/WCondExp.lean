/-
The conditional mean of the increments of `lem:w-martingale`.

The increment at step `i` is the discrepancy, at the instruction the exploration
reads there, between the truncated Green function at the site that instruction
points to and its average over the neighbours of the site the instruction sits
at.  Conditionally on what the exploration has revealed by step `i` the site is
known and the instruction is not, so the mean of the increment is the mean of the
discrepancy under the instruction law, which is zero by the definition of the
walk operator.

The argument is pathwise where it can be.  The pair the exploration reads at
step `i` and the round that pair belongs to are unchanged when the instructions
the exploration has not read are erased, so the events on which they take
prescribed values lie in the sigma-algebra of step `i`; and on such an event the
instruction at the prescribed pair has not been read, so overwriting it moves
nothing, and the library's one-coordinate factorization applies.
-/
import Parking.Support.WFiltration
import Parking.Support.CoordIntegral

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### The mean of a function under the instruction law -/

/-- **The integral against the instruction law is the walk average.** -/
theorem integral_instructionLaw (u : Site d → ℝ) (y : Site d) :
    ∫ z, u z ∂(instructionLaw y) = walkOp u y := by
  classical
  have hint : ∀ a : Site d, Integrable u (Measure.dirac a) := fun a =>
    integrable_dirac (by simp)
  rw [instructionLaw, integral_smul_measure,
    integral_finsetSum_measure (fun i _ => ((hint _).add_measure (hint _)))]
  have hterm : ∀ i : Fin d,
      ∫ z, u z ∂(Measure.dirac (y + unit i) + Measure.dirac (y - unit i))
        = u (y + unit i) + u (y - unit i) := by
    intro i
    rw [integral_add_measure (hint _) (hint _), integral_dirac, integral_dirac]
  simp only [hterm]
  have h2d : ((2 * (d : ℝ≥0∞))⁻¹).toReal = (2 * (d : ℝ))⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_mul]
    simp
  rw [h2d, walkOp, nbrSum, smul_eq_mul, div_eq_inv_mul]

/-- Projecting an instruction onto the neighbours of its site does not change
the walk average at that site. -/
theorem walkOp_nbrProjVal (i₀ : Fin d) (u : Site d → ℝ) (y : Site d) :
    walkOp (fun z => u (if z ∈ nbrFinset y then z else y + unit i₀)) y = walkOp u y := by
  simp only [walkOp, nbrSum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [if_pos (mem_nbrFinset_add y i), if_pos (mem_nbrFinset_sub y i)]


/-! ### The pair and the round the exploration reads at step `i` -/

/-- The round the instruction read at step `i` belongs to, and zero past the
end of the list the exploration reads. -/
def wRound (i₀ : Fin d) (n i : ℕ) (ω : Data d) : ℕ :=
  if i < (blockPrefix (wProj i₀ ω) n (n - 1)).length then
    roundOf (wProj i₀ ω) (wPair i₀ n i ω) else 0

/-- **The increment at step `i` is the discrepancy at the pair it reads**, for
every realization, including the steps past the end of the list, where the pair
is the parking site and both terms vanish. -/
theorem wXi_eq_disc (hd : 1 ≤ d) (i₀ : Fin d) (n i : ℕ) (ω : Data d) :
    wXi i₀ n i ω
      = green d (n - wRound i₀ n i ω) ((wProj i₀ ω).2.1 (wPair i₀ n i ω))
        - walkOp (green d (n - wRound i₀ n i ω)) (wPair i₀ n i ω).1 := by
  classical
  set ω' : Data d := wProj i₀ ω with hω'
  have hpair : wPair i₀ n i ω = (blockPrefix ω' n (n - 1)).getD i (padSite d n, i) := rfl
  by_cases hi : i < (blockPrefix ω' n (n - 1)).length
  · have hround : wRound i₀ n i ω = roundOf ω' (wPair i₀ n i ω) := if_pos hi
    have hmap : wXi i₀ n i ω = wInc ω' n (wPair i₀ n i ω) := by
      rw [wXi, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
      congr 1
      rw [hpair, List.getD_eq_getElem _ _ hi]
    rw [hmap, hround, wInc]
  · have hround : wRound i₀ n i ω = 0 := if_neg hi
    have hpad : wPair i₀ n i ω = (padSite d n, i) := by
      rw [hpair, List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    have hbox : padSite d n ∉ boxFinset (0 : Site d) n := by
      refine padSite_notMem_box hd n n ?_
      have h : n - 1 ≤ n := Nat.sub_le n 1
      simp only [blockRad]
      omega
    have hzero := green_block_eq_zero_of_far ω' (wProj_stepsToNeighbour i₀ ω) n hbox i
    rw [wXi_eq_zero_of_le (Nat.le_of_not_lt hi), hround, hpad, Nat.sub_zero]
    exact hzero.symm

/-- **The round the exploration reads at step `i` is decided by the
instructions it has read before that step.** -/
theorem wRound_congr_of_reads (i₀ : Fin d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (n i : ℕ) {σ σ' : Site d × ℕ → Site d}
    (hread : ∀ k, k < i → explIdx i₀ η ρ n k σ = explIdx i₀ η ρ n k σ' ∧
      σ (explIdx i₀ η ρ n k σ) = σ' (explIdx i₀ η ρ n k σ)) :
    wRound i₀ n i ((η, σ, ρ) : Data d) = wRound i₀ n i ((η, σ', ρ) : Data d) := by
  classical
  set ω : Data d := ((η, nbrProj i₀ σ, ρ) : Data d) with hω
  set ω' : Data d := ((η, nbrProj i₀ σ', ρ) : Data d) with hω'
  have hwR : wRound i₀ n i ((η, σ, ρ) : Data d)
      = if i < (blockPrefix ω n (n - 1)).length then roundOf ω (explIdx i₀ η ρ n i σ) else 0 :=
    rfl
  have hwR' : wRound i₀ n i ((η, σ', ρ) : Data d)
      = if i < (blockPrefix ω' n (n - 1)).length then roundOf ω' (explIdx i₀ η ρ n i σ')
        else 0 := rfl
  have hblocks : ∀ k, k ≤ n - 1 → (blockPrefix ω n (k - 1)).length ≤ i →
      ∀ s, 1 ≤ s → s ≤ k → blockAt ω (blockRad n s) s = blockAt ω' (blockRad n s) s :=
    blockAt_agree_of_readsPrefix i₀ η ρ n i hread
  have hidx : explIdx i₀ η ρ n i σ = explIdx i₀ η ρ n i σ' :=
    readsOnlyRevealed_explIdx i₀ η ρ n i σ σ' hread
  rw [hwR, hwR']
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
      blockPrefix_congr (hblocks K hKle hKmin)
    have hKlt' : i < (blockPrefix ω' n K).length := by rw [← heq]; exact hKlt
    have hi' : i < (blockPrefix ω' n (n - 1)).length :=
      lt_of_lt_of_le hKlt' (length_blockPrefix_mono ω' n hKle)
    have hgetD : (blockPrefix ω n (n - 1)).getD i (padSite d n, i)
        = (blockPrefix ω n K).getD i (padSite d n, i) := by
      rw [blockPrefix_append ω n hKle, List.getD_append _ _ _ _ hKlt]
    have hqmem : explIdx i₀ η ρ n i σ ∈ blockPrefix ω n K := by
      rw [explIdx, hgetD, List.getD_eq_getElem _ _ hKlt]
      exact List.getElem_mem hKlt
    obtain ⟨r, hr1, hrK, hrq⟩ := mem_blockPrefix.mp hqmem
    have hrq' : explIdx i₀ η ρ n i σ ∈ blockAt ω' (blockRad n r) r := by
      rw [← hblocks K hKle hKmin r hr1 hrK]
      exact hrq
    rw [if_pos hi, if_pos hi', ← hidx, roundOf_eq_of_mem_blockAt hr1 hrq,
      roundOf_eq_of_mem_blockAt hr1 hrq']
  · have hlen : (blockPrefix ω n (n - 1)).length ≤ i := Nat.le_of_not_lt hi
    have hlen' : (blockPrefix ω n ((n - 1) - 1)).length ≤ i :=
      le_trans (length_blockPrefix_mono ω n (by omega)) hlen
    have heq : blockPrefix ω n (n - 1) = blockPrefix ω' n (n - 1) :=
      blockPrefix_congr (hblocks (n - 1) le_rfl hlen')
    rw [if_neg hi, if_neg (by rw [← heq]; exact hi)]

theorem wRound_wTrunc (i₀ : Fin d) (n i : ℕ) (ω : Data d) :
    wRound i₀ n i (wTrunc i₀ n i ω) = wRound i₀ n i ω := by
  have hread : ∀ k, k < i →
      explIdx i₀ ω.1 ω.2.2 n k ω.2.1 = explIdx i₀ ω.1 ω.2.2 n k (wTrunc i₀ n i ω).2.1 ∧
        ω.2.1 (explIdx i₀ ω.1 ω.2.2 n k ω.2.1)
          = (wTrunc i₀ n i ω).2.1 (explIdx i₀ ω.1 ω.2.2 n k ω.2.1) := fun k hk =>
    ⟨(wPair_wTrunc i₀ n i ω k (by omega)).symm,
      (wTrunc_stack_of_read i₀ n i ω hk).symm⟩
  exact (wRound_congr_of_reads i₀ ω.1 ω.2.2 n i hread).symm

theorem wPair_wTrunc_self (i₀ : Fin d) (n i : ℕ) (ω : Data d) :
    wPair i₀ n i (wTrunc i₀ n i ω) = wPair i₀ n i ω :=
  wPair_wTrunc i₀ n i ω i le_rfl


/-! ### The pair and the round are measurable, and read only what is revealed -/

theorem measurable_wRound (i₀ : Fin d) (n i : ℕ) : Measurable (wRound i₀ n i) := by
  classical
  refine measurable_of_determined (wIncObs i₀ n i) (measurable_wIncObs i₀ n i) _ ?_
  intro ω ω2 hobs
  have htable : (fun (s : Fin n) (y : {y : Site d // y ∈ boxFinset (0 : Site d) (blockRad n 1)})
      => U (wProj i₀ ω) s.val y.val)
      = fun s y => U (wProj i₀ ω2) s.val y.val := congrArg Prod.fst hobs
  have hpair : wPair i₀ n i ω = wPair i₀ n i ω2 :=
    congrArg Prod.fst (congrArg Prod.snd hobs)
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
  by_cases hi : i < (blockPrefix (wProj i₀ ω) n (n - 1)).length
  · have hi' : i < (blockPrefix (wProj i₀ ω2) n (n - 1)).length := by rw [← hL]; exact hi
    have hqmem : wPair i₀ n i ω ∈ blockPrefix (wProj i₀ ω) n (n - 1) := by
      show (blockPrefix (wProj i₀ ω) n (n - 1)).getD i (padSite d n, i) ∈ _
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    obtain ⟨s, h1, h2, hqs⟩ := mem_blockPrefix.mp hqmem
    have hqs2 : wPair i₀ n i ω ∈ blockAt (wProj i₀ ω2) (blockRad n s) s := by
      rw [← hblock s h1 h2]; exact hqs
    rw [wRound, wRound, if_pos hi, if_pos hi', ← hpair,
      roundOf_eq_of_mem_blockAt h1 hqs, roundOf_eq_of_mem_blockAt h1 hqs2]
  · have hi' : ¬ i < (blockPrefix (wProj i₀ ω2) n (n - 1)).length := by rw [← hL]; exact hi
    rw [wRound, wRound, if_neg hi, if_neg hi']

theorem measurable_wPair_wFiltration (i₀ : Fin d) (n i : ℕ) :
    Measurable[wFiltration i₀ n i] (wPair i₀ n i) := by
  have hself : Measurable[wFiltration i₀ n i,
      inferInstanceAs (MeasurableSpace (Data d))] (wTrunc i₀ n i) :=
    measurable_iff_comap_le.mpr le_rfl
  have hcomp : Measurable[wFiltration i₀ n i]
      (fun ω => wPair i₀ n i (wTrunc i₀ n i ω)) :=
    (measurable_wPair i₀ n i).comp hself
  simpa only [wPair_wTrunc_self] using hcomp

theorem measurable_wRound_wFiltration (i₀ : Fin d) (n i : ℕ) :
    Measurable[wFiltration i₀ n i] (wRound i₀ n i) := by
  have hself : Measurable[wFiltration i₀ n i,
      inferInstanceAs (MeasurableSpace (Data d))] (wTrunc i₀ n i) :=
    measurable_iff_comap_le.mpr le_rfl
  have hcomp : Measurable[wFiltration i₀ n i]
      (fun ω => wRound i₀ n i (wTrunc i₀ n i ω)) :=
    (measurable_wRound i₀ n i).comp hself
  simpa only [wRound_wTrunc] using hcomp

/-! ### Overwriting an instruction the exploration has not read -/

/-- **Overwriting an instruction the exploration has not read before step `i`
leaves the revealed realization unchanged.** -/
theorem wTrunc_update (i₀ : Fin d) (n i : ℕ) (ω : Data d) (q : Site d × ℕ) (c : Site d)
    (hfresh : ∀ k, k < i → wPair i₀ n k ω ≠ q) :
    wTrunc i₀ n i ((ω.1, Function.update ω.2.1 q c, ω.2.2) : Data d) = wTrunc i₀ n i ω := by
  classical
  have hpair : ∀ k, k ≤ i →
      wPair i₀ n k ((ω.1, Function.update ω.2.1 q c, ω.2.2) : Data d) = wPair i₀ n k ω := by
    intro k hk
    exact explIdx_pred i₀ ω.1 ω.2.2 n k ω.2.1 q c fun k' hk' => hfresh k' (by omega)
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext z
  have hcond : (∃ k, k < i ∧
        wPair i₀ n k ((ω.1, Function.update ω.2.1 q c, ω.2.2) : Data d) = z)
      ↔ ∃ k, k < i ∧ wPair i₀ n k ω = z := by
    constructor
    · rintro ⟨k, hk, hz⟩
      exact ⟨k, hk, by rwa [hpair k (by omega)] at hz⟩
    · rintro ⟨k, hk, hz⟩
      exact ⟨k, hk, by rwa [hpair k (by omega)]⟩
  show (if ∃ k, k < i ∧ wPair i₀ n k ((ω.1, Function.update ω.2.1 q c, ω.2.2) : Data d) = z
      then Function.update ω.2.1 q c z else z.1 + unit i₀)
    = if ∃ k, k < i ∧ wPair i₀ n k ω = z then ω.2.1 z else z.1 + unit i₀
  by_cases h : ∃ k, k < i ∧ wPair i₀ n k ω = z
  · obtain ⟨k, hk, rfl⟩ := h
    rw [if_pos (hcond.mpr ⟨k, hk, rfl⟩), if_pos ⟨k, hk, rfl⟩]
    exact Function.update_of_ne (hfresh k hk) _ _
  · rw [if_neg h, if_neg fun hc => h (hcond.mp hc)]


/-! ### The conditional mean of the increments vanishes -/

/-- The realizations whose exploration reads the pair `q` at step `i`, in the
round `s`. -/
def wEvent (i₀ : Fin d) (n i : ℕ) (q : Site d × ℕ) (s : ℕ) : Set (Data d) :=
  {ω | wPair i₀ n i ω = q ∧ wRound i₀ n i ω = s}

theorem measurableSet_wEvent (i₀ : Fin d) (n i : ℕ) (q : Site d × ℕ) (s : ℕ) :
    MeasurableSet[wFiltration i₀ n i] (wEvent i₀ n i q s) :=
  ((measurable_wPair_wFiltration i₀ n i) (measurableSet_singleton q)).inter
    ((measurable_wRound_wFiltration i₀ n i) (measurableSet_singleton s))

/-- Overwriting the instruction the exploration reads at step `i` leaves the
revealed realization unchanged, in either direction. -/
theorem wTrunc_update_of_pair (hd : 1 ≤ d) (i₀ : Fin d) (n i : ℕ) (ω : Data d)
    (q : Site d × ℕ) (c : Site d) (hq : wPair i₀ n i ω = q) :
    wTrunc i₀ n i ((ω.1, Function.update ω.2.1 q c, ω.2.2) : Data d) = wTrunc i₀ n i ω :=
  wTrunc_update i₀ n i ω q c fun k hk => by
    rw [← hq]
    exact explIdx_fresh hd i₀ ω.1 ω.2.2 n i ω.2.1 k hk

/-- **The event that the exploration reads `q` at step `i` in the round `s`,
inside a set of the sigma-algebra of step `i`, does not read the instruction at
`q`.** -/
theorem wEvent_update_iff (hd : 1 ≤ d) (i₀ : Fin d) (n i : ℕ) (q : Site d × ℕ) (s : ℕ)
    (B : Set (Data d)) (ω : Data d) (c : Site d) :
    ((ω.1, Function.update ω.2.1 q c, ω.2.2) : Data d)
        ∈ (wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i q s
      ↔ ω ∈ (wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i q s := by
  classical
  set ω' : Data d := ((ω.1, Function.update ω.2.1 q c, ω.2.2) : Data d) with hω'
  have hback : ((ω'.1, Function.update ω'.2.1 q (ω.2.1 q), ω'.2.2) : Data d) = ω := by
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    show Function.update (Function.update ω.2.1 q c) q (ω.2.1 q) = ω.2.1
    rw [Function.update_idem, Function.update_eq_self]
  have htr : (wPair i₀ n i ω = q ∨ wPair i₀ n i ω' = q) → wTrunc i₀ n i ω' = wTrunc i₀ n i ω := by
    rintro (h | h)
    · exact wTrunc_update_of_pair hd i₀ n i ω q c h
    · have := wTrunc_update_of_pair hd i₀ n i ω' q (ω.2.1 q) h
      rw [hback] at this
      exact this.symm
  have htrans : ∀ hω : wTrunc i₀ n i ω' = wTrunc i₀ n i ω,
      (ω' ∈ (wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i q s
        ↔ ω ∈ (wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i q s) := by
    intro hω
    have h1 : wPair i₀ n i ω' = wPair i₀ n i ω := by
      rw [← wPair_wTrunc_self i₀ n i ω', ← wPair_wTrunc_self i₀ n i ω, hω]
    have h2 : wRound i₀ n i ω' = wRound i₀ n i ω := by
      rw [← wRound_wTrunc i₀ n i ω', ← wRound_wTrunc i₀ n i ω, hω]
    simp only [Set.mem_inter_iff, Set.mem_preimage, wEvent, Set.mem_setOf_eq, hω, h1, h2]
  constructor
  · intro h
    exact (htrans (htr (Or.inr h.2.1))).mp h
  · intro h
    exact (htrans (htr (Or.inl h.2.1))).mpr h

/-- The discrepancy read at a prescribed pair, as a function of the instruction
alone. -/
def wDisc (i₀ : Fin d) (n : ℕ) (q : Site d × ℕ) (s : ℕ) (z : Site d) : ℝ :=
  green d (n - s) (if z ∈ nbrFinset q.1 then z else q.1 + unit i₀)
    - walkOp (green d (n - s)) q.1

theorem walkOp_sub_const (hd : 1 ≤ d) (u : Site d → ℝ) (C : ℝ) (y : Site d) :
    walkOp (fun z => u z - C) y = walkOp u y - C := by
  have hne : (2 * (d : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have hsum : nbrSum (fun z => u z - C) y = nbrSum u y - 2 * (d : ℝ) * C := by
    simp only [nbrSum, sub_add_sub_comm, Finset.sum_sub_distrib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  rw [walkOp, walkOp, hsum, sub_div]
  have hne' : ((d : ℝ) * 2) ≠ 0 := by rw [mul_comm]; exact hne
  field_simp

/-- **The mean of the discrepancy under the instruction law is zero.** -/
theorem integral_wDisc (hd : 1 ≤ d) (i₀ : Fin d) (n : ℕ) (q : Site d × ℕ) (s : ℕ) :
    ∫ z, wDisc i₀ n q s z ∂(instructionLaw q.1) = 0 := by
  rw [integral_instructionLaw]
  show walkOp (fun z => green d (n - s) (if z ∈ nbrFinset q.1 then z else q.1 + unit i₀)
    - walkOp (green d (n - s)) q.1) q.1 = 0
  rw [walkOp_sub_const hd, walkOp_nbrProjVal i₀ (green d (n - s)) q.1, sub_self]

theorem measurable_wDisc (i₀ : Fin d) (n : ℕ) (q : Site d × ℕ) (s : ℕ) :
    Measurable (wDisc i₀ n q s) := Measurable.of_discrete

/-- On the event that the exploration reads `q` at step `i` in the round `s`,
the increment is the discrepancy at `q`. -/
theorem wXi_eq_wDisc (hd : 1 ≤ d) (i₀ : Fin d) (n i : ℕ) (q : Site d × ℕ) (s : ℕ)
    {ω : Data d} (hω : ω ∈ wEvent i₀ n i q s) :
    wXi i₀ n i ω = wDisc i₀ n q s (ω.2.1 q) := by
  obtain ⟨hq, hs⟩ := hω
  rw [wXi_eq_disc hd i₀ n i ω, hq, hs, wDisc]
  rfl


/-! ### The integral of an increment over one piece of the filtration -/

theorem abs_wDisc_le (hd : 1 ≤ d) (i₀ : Fin d) (n : ℕ) (q : Site d × ℕ) (s : ℕ) (z : Site d) :
    |wDisc i₀ n q s z| ≤ 2 * n := by
  have h1 : 0 ≤ green d (n - s) (if z ∈ nbrFinset q.1 then z else q.1 + unit i₀) :=
    green_nonneg _ _
  have h2 : green d (n - s) (if z ∈ nbrFinset q.1 then z else q.1 + unit i₀) ≤ (n - s : ℕ) :=
    green_le hd _ _
  have h3 : 0 ≤ walkOp (green d (n - s)) q.1 := walkOp_green_nonneg _ _
  have h4 : walkOp (green d (n - s)) q.1 ≤ (n - s : ℕ) := walkOp_green_le hd _ _
  have h5 : ((n - s : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n s
  rw [wDisc, abs_le]
  constructor <;> linarith

/-- **The integral of a function of the instruction at a prescribed pair, over a
piece of the sigma-algebra of step `i` on which the exploration reads that pair
in a prescribed round, factorizes**: the instruction has not been read, so it is
a fresh draw from the instruction law. -/
theorem setIntegral_eval_piece (hd : 1 ≤ d) (i₀ : Fin d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] (n i : ℕ) (q : Site d × ℕ) (s : ℕ)
    {B : Set (Data d)} (hB : MeasurableSet B)
    (g : Site d → ℝ) (K : ℝ) (hgb : ∀ z, ‖g z‖ ≤ K) :
    ∫ ω in (wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i q s, g (ω.2.1 q) ∂(law d ν)
      = ((law d ν) ((wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i q s)).toReal
        * ∫ z, g z ∂(instructionLaw q.1) := by
  classical
  haveI hinst : ∀ p : Site d × ℕ, IsProbabilityMeasure (instructionLaw (d := d) p.1) :=
    fun p => instructionLaw_isProbability hd p.1
  haveI := stackLaw_isProbability (d := d) hd
  haveI := rankLaw_isProbability d
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (law d ν) := by unfold law; infer_instance
  haveI : IsProbabilityMeasure (stackRankLaw d) := by unfold stackRankLaw; infer_instance
  set E : Set (Data d) := (wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i q s with hEdef
  have hE : MeasurableSet E := by
    refine MeasurableSet.inter ((measurable_wTrunc i₀ n i) hB) ?_
    exact wFiltration_le i₀ n i _ (measurableSet_wEvent i₀ n i q s)
  set χ : Data d → ℝ := E.indicator (fun _ => (1 : ℝ)) with hχ
  have hχm : Measurable χ := measurable_const.indicator hE
  have hχb : ∀ ω, ‖χ ω‖ ≤ 1 := by
    intro ω
    by_cases h : ω ∈ E
    · rw [hχ, Set.indicator_of_mem h, Real.norm_eq_abs]; norm_num
    · rw [hχ, Set.indicator_of_notMem h, Real.norm_eq_abs]; norm_num
  have hK : 0 ≤ K := le_trans (norm_nonneg _) (hgb (0 : Site d))
  set f : Data d → ℝ := fun ω => χ ω * g (ω.2.1 q) with hf
  have hfm : Measurable f :=
    hχm.mul ((Measurable.of_discrete : Measurable g).comp
      ((measurable_pi_apply q).comp (measurable_fst.comp measurable_snd)))
  have hfb : ∀ ω, ‖f ω‖ ≤ K := by
    intro ω
    rw [hf, norm_mul]
    have h1 := hχb ω
    have h2 := hgb (ω.2.1 q)
    have h3 : (0 : ℝ) ≤ ‖χ ω‖ := norm_nonneg _
    have h4 : (0 : ℝ) ≤ ‖g (ω.2.1 q)‖ := norm_nonneg _
    nlinarith
  have hfint : Integrable f (law d ν) :=
    (integrable_const K).mono' hfm.aestronglyMeasurable (Filter.Eventually.of_forall hfb)
  have hχint : Integrable χ (law d ν) :=
    (integrable_const (1 : ℝ)).mono' hχm.aestronglyMeasurable
      (Filter.Eventually.of_forall hχb)
  have hpt : ∀ ω : Data d, E.indicator (fun ω' => g (ω'.2.1 q)) ω = f ω := by
    intro ω
    by_cases h : ω ∈ E
    · rw [Set.indicator_of_mem h, hf]
      show g (ω.2.1 q) = χ ω * g (ω.2.1 q)
      rw [hχ, Set.indicator_of_mem h, one_mul]
    · rw [Set.indicator_of_notMem h, hf]
      show (0 : ℝ) = χ ω * g (ω.2.1 q)
      rw [hχ, Set.indicator_of_notMem h, zero_mul]
  have hinner : ∀ η : Site d → ℤ, ∫ p : Randomness d, f ((η, p) : Data d) ∂(stackRankLaw d)
      = (∫ p : Randomness d, χ ((η, p) : Data d) ∂(stackRankLaw d))
        * ∫ z, g z ∂(instructionLaw q.1) := by
    intro η
    have hFm : Measurable fun p : Randomness d => χ ((η, p) : Data d) :=
      hχm.comp (measurable_const.prodMk measurable_id)
    have hFinv : ∀ (σ : Site d × ℕ → Site d) (r : Label d × ℕ → ℝ),
        χ ((η, Function.update σ q (q.1 + unit i₀), r) : Data d) = χ ((η, σ, r) : Data d) := by
      intro σ r
      have hiff := wEvent_update_iff hd i₀ n i q s B ((η, σ, r) : Data d) (q.1 + unit i₀)
      by_cases h : ((η, σ, r) : Data d) ∈ E
      · rw [hχ, Set.indicator_of_mem (hiff.mpr h), Set.indicator_of_mem h]
      · rw [hχ, Set.indicator_of_notMem (fun hc => h (hiff.mp hc)),
          Set.indicator_of_notMem h]
    have hFbint : Integrable (fun p : Randomness d => χ ((η, p) : Data d)) (stackRankLaw d) := by
      refine (integrable_const (1 : ℝ)).mono' hFm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => ?_)
      exact hχb _
    have hFgint : Integrable (fun p : Randomness d =>
        χ ((η, p) : Data d) * g (p.1 q)) (stackRankLaw d) := by
      refine (integrable_const K).mono'
        (hfm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => ?_)
      exact hfb ((η, p) : Data d)
    have hlib := integral_mul_eval_prod
      (μ := fun p : Site d × ℕ => instructionLaw (d := d) p.1) (κ := rankLaw d)
      q (q.1 + unit i₀) (fun p : Randomness d => χ ((η, p.1, p.2) : Data d))
      hFm hFinv g Measurable.of_discrete hFbint hFgint
    exact hlib
  have hEmeas : ∫ ω, χ ω ∂(law d ν) = ((law d ν) E).toReal := by
    rw [hχ, integral_indicator hE, integral_const, measureReal_def, smul_eq_mul, mul_one,
      Measure.restrict_apply_univ]
  calc ∫ ω in E, g (ω.2.1 q) ∂(law d ν)
      = ∫ ω, E.indicator (fun ω' => g (ω'.2.1 q)) ω ∂(law d ν) := (integral_indicator hE).symm
    _ = ∫ ω, f ω ∂(law d ν) := integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ η, ∫ p : Randomness d, f ((η, p) : Data d) ∂(stackRankLaw d)
          ∂(LatticeProb.iidLaw d ν) := by
        rw [show law d ν = (LatticeProb.iidLaw d ν).prod (stackRankLaw d) from rfl] at hfint ⊢
        exact integral_prod f hfint
    _ = ∫ η, (∫ p : Randomness d, χ ((η, p) : Data d) ∂(stackRankLaw d))
          * (∫ z, g z ∂(instructionLaw q.1)) ∂(LatticeProb.iidLaw d ν) :=
        integral_congr_ae (Filter.Eventually.of_forall hinner)
    _ = (∫ η, ∫ p : Randomness d, χ ((η, p) : Data d) ∂(stackRankLaw d)
          ∂(LatticeProb.iidLaw d ν)) * ∫ z, g z ∂(instructionLaw q.1) := integral_mul_const _ _
    _ = (∫ ω, χ ω ∂(law d ν)) * ∫ z, g z ∂(instructionLaw q.1) := by
        congr 1
        rw [show law d ν = (LatticeProb.iidLaw d ν).prod (stackRankLaw d) from rfl] at hχint ⊢
        exact (integral_prod χ hχint).symm
    _ = ((law d ν) E).toReal * ∫ z, g z ∂(instructionLaw q.1) := by rw [hEmeas]

/-- **The integral of the increment over such a piece is zero.** -/
theorem setIntegral_wXi_piece (hd : 1 ≤ d) (i₀ : Fin d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] (n i : ℕ) (q : Site d × ℕ) (s : ℕ)
    {B : Set (Data d)} (hB : MeasurableSet B) :
    ∫ ω in (wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i q s, wXi i₀ n i ω ∂(law d ν) = 0 := by
  have hcongr : ∫ ω in (wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i q s, wXi i₀ n i ω ∂(law d ν)
      = ∫ ω in (wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i q s,
          wDisc i₀ n q s (ω.2.1 q) ∂(law d ν) := by
    refine setIntegral_congr_fun ?_ fun ω hω => wXi_eq_wDisc hd i₀ n i q s hω.2
    refine MeasurableSet.inter ((measurable_wTrunc i₀ n i) hB) ?_
    exact wFiltration_le i₀ n i _ (measurableSet_wEvent i₀ n i q s)
  rw [hcongr, setIntegral_eval_piece hd i₀ ν n i q s hB (wDisc i₀ n q s) (2 * n)
    (fun z => by rw [Real.norm_eq_abs]; exact abs_wDisc_le hd i₀ n q s z),
    integral_wDisc hd i₀ n q s, mul_zero]

/-! ### The conditional mean vanishes -/

/-- **The set integral of the increment over any set of the sigma-algebra of
step `i` is zero.** -/
theorem setIntegral_wXi_eq_zero (hd : 1 ≤ d) (i₀ : Fin d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] (n : ℕ) (hn : 1 ≤ n) (i : ℕ) {A : Set (Data d)}
    (hA : MeasurableSet[wFiltration i₀ n i] A) :
    ∫ ω in A, wXi i₀ n i ω ∂(law d ν) = 0 := by
  classical
  obtain ⟨B, hB, rfl⟩ := hA
  set κ : (Site d × ℕ) × ℕ → Set (Data d) := fun c =>
    (wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i c.1 c.2 with hκ
  have hmeas : ∀ c, MeasurableSet (κ c) := fun c => by
    refine MeasurableSet.inter ((measurable_wTrunc i₀ n i) hB) ?_
    exact wFiltration_le i₀ n i _ (measurableSet_wEvent i₀ n i c.1 c.2)
  have hdisj : Pairwise (Function.onFun Disjoint κ) := by
    intro c c' hcc
    refine Set.disjoint_left.mpr fun ω hω hω' => ?_
    have h1 : wPair i₀ n i ω = c.1 := hω.2.1
    have h2 : wRound i₀ n i ω = c.2 := hω.2.2
    have h1' : wPair i₀ n i ω = c'.1 := hω'.2.1
    have h2' : wRound i₀ n i ω = c'.2 := hω'.2.2
    exact hcc (Prod.ext (h1 ▸ h1') (h2 ▸ h2'))
  have hunion : ⋃ c, κ c = wTrunc i₀ n i ⁻¹' B := by
    refine Set.Subset.antisymm (Set.iUnion_subset fun c => Set.inter_subset_left) ?_
    intro ω hω
    exact Set.mem_iUnion.mpr
      ⟨(wPair i₀ n i ω, wRound i₀ n i ω), hω, rfl, rfl⟩
  have hint : IntegrableOn (wXi i₀ n i) (⋃ c, κ c) (law d ν) :=
    (integrable_wXi hd i₀ ν n hn i).integrableOn
  rw [← hunion, integral_iUnion hmeas hdisj hint]
  have hzero : ∀ c : (Site d × ℕ) × ℕ,
      ∫ x in (wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i c.1 c.2, wXi i₀ n i x ∂(law d ν) = 0 :=
    fun c => setIntegral_wXi_piece hd i₀ ν n i c.1 c.2 hB
  simp only [hκ, hzero, tsum_zero]

/-- **The increments have zero conditional mean**, the second clause of
`lem:w-martingale`. -/
theorem condExp_wXi (hd : 1 ≤ d) (i₀ : Fin d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (i : ℕ) :
    (law d ν)[wXi i₀ n i | wFiltration i₀ n i] =ᵐ[law d ν] 0 := by
  haveI := stackLaw_isProbability (d := d) hd
  haveI := rankLaw_isProbability d
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (law d ν) := by unfold law; infer_instance
  refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq (wFiltration_le i₀ n i)
    (integrable_wXi hd i₀ ν n hn i)
    (fun s _ _ => (integrable_zero _ _ _).integrableOn)
    (fun s hs _ => ?_) (stronglyMeasurable_const.aestronglyMeasurable)).symm
  rw [setIntegral_wXi_eq_zero hd i₀ ν n hn i hs]
  simp

end Parking

end
