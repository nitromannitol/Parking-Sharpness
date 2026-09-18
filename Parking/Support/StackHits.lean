/-
The stack at a site points at each of its neighbours infinitely often.

The remaining input of the last part of Step 2 of `prop:everyone-settles`
(`parking.tex:1526-1528`).  The instructions are independent and each of the
`2d` neighbours carries mass `(2d)^{-1}`, so the probability that none of the
instructions numbered `N, …, N+k-1` at `y` points at a neighbour `x` is
`(1 - (2d)^{-1})^k`, which tends to zero; the event that the stack at `y` points
at `x` only finitely often is the countable union over `N` of those, hence null.
Countability of the lattice carries the statement to every pair of neighbours at
once, and `Parking.Ulimit_top_of_exists` then propagates an infinite odometer
everywhere.
-/
import Parking.Support.Propagate
import Parking.Support.DeferredIntegral

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Filter Topology
open scoped ENNReal

variable {d : ℕ}

theorem instructionLaw_singleton_eq (y x : Site d) :
    instructionLaw y ({x} : Set (Site d))
      = (2 * (d : ℝ≥0∞))⁻¹ * (if x ∈ nbrFinset y then 1 else 0) := by
  simp only [instructionLaw, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    smul_eq_mul]
  rw [← sum_dirac_nbr y x]

theorem instructionLaw_compl_lt_one (hd : 1 ≤ d) {y x : Site d} (hx : x ∈ nbrFinset y) :
    instructionLaw y ({x} : Set (Site d))ᶜ < 1 := by
  haveI := instructionLaw_isProbability hd y
  have h2d : (2 * (d : ℝ≥0∞)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, Nat.cast_eq_zero, not_or]
    exact ⟨two_ne_zero, by omega⟩
  have h2d' : (2 * (d : ℝ≥0∞)) ≠ ⊤ := by simp [ENNReal.mul_eq_top]
  have hpos : 0 < instructionLaw y ({x} : Set (Site d)) := by
    rw [instructionLaw_singleton_eq, if_pos hx, mul_one]
    exact ENNReal.inv_pos.mpr h2d'
  have hcompl : instructionLaw y ({x} : Set (Site d))ᶜ
      = 1 - instructionLaw y ({x} : Set (Site d)) := by
    rw [prob_compl_eq_one_sub (measurableSet_singleton x)]
  rw [hcompl]
  exact ENNReal.sub_lt_self (by simp) (by simp) hpos.ne'


theorem stackLaw_pi_no_hit (hd : 1 ≤ d) (y x : Site d) (N k : ℕ) :
    stackLaw d ((↑(({y} : Finset (Site d)) ×ˢ Finset.Ico N (N + k)) : Set (Site d × ℕ)).pi
        (fun _ => ({x} : Set (Site d))ᶜ))
      = (instructionLaw y ({x} : Set (Site d))ᶜ) ^ k := by
  haveI : ∀ q : Site d × ℕ, IsProbabilityMeasure (instructionLaw (d := d) q.1) :=
    fun q => instructionLaw_isProbability hd q.1
  rw [stackLaw, Measure.infinitePi_pi _ (fun q _ => (measurableSet_singleton x).compl)]
  have hconst : ∀ q ∈ ({y} : Finset (Site d)) ×ˢ Finset.Ico N (N + k),
      instructionLaw q.1 ({x} : Set (Site d))ᶜ = instructionLaw y ({x} : Set (Site d))ᶜ := by
    intro q hq
    rw [Finset.mem_product, Finset.mem_singleton] at hq
    rw [hq.1]
  rw [Finset.prod_congr rfl hconst, Finset.prod_const]
  congr 1
  rw [Finset.card_product, Finset.card_singleton, Nat.card_Ico]
  omega

theorem stackLaw_no_hit_after (hd : 1 ≤ d) {y x : Site d} (hx : x ∈ nbrFinset y) (N : ℕ) :
    stackLaw d {σ : Site d × ℕ → Site d | ∀ j : ℕ, N ≤ j → σ (y, j) ≠ x} = 0 := by
  set q : ℝ≥0∞ := instructionLaw y ({x} : Set (Site d))ᶜ with hq
  have hq1 : q < 1 := instructionLaw_compl_lt_one hd hx
  have hsub : ∀ k : ℕ,
      {σ : Site d × ℕ → Site d | ∀ j : ℕ, N ≤ j → σ (y, j) ≠ x}
        ⊆ (↑(({y} : Finset (Site d)) ×ˢ Finset.Ico N (N + k)) : Set (Site d × ℕ)).pi
            (fun _ => ({x} : Set (Site d))ᶜ) := by
    intro k σ hσ
    rintro ⟨a, j⟩ hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_singleton,
      Finset.mem_Ico] at hp
    have h1 : a = y := hp.1
    have h2 : N ≤ j := hp.2.1
    subst h1
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hσ j h2
  have hle : ∀ k : ℕ,
      stackLaw d {σ : Site d × ℕ → Site d | ∀ j : ℕ, N ≤ j → σ (y, j) ≠ x} ≤ q ^ k := by
    intro k
    rw [← stackLaw_pi_no_hit hd y x N k]
    exact measure_mono (hsub k)
  have hlim : Tendsto (fun k : ℕ => q ^ k) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq1
  exact le_antisymm (ge_of_tendsto hlim (Filter.Eventually.of_forall hle)) bot_le


theorem ae_stackLaw_hits (hd : 1 ≤ d) :
    ∀ᵐ σ ∂(stackLaw d), ∀ y x : Site d, x ∈ nbrFinset y →
      {j : ℕ | σ (y, j) = x}.Infinite := by
  haveI := stackLaw_isProbability (d := d) hd
  rw [ae_all_iff]
  intro y
  rw [ae_all_iff]
  intro x
  by_cases hx : x ∈ nbrFinset y
  · have hnull : stackLaw d (⋃ N : ℕ,
        {σ : Site d × ℕ → Site d | ∀ j : ℕ, N ≤ j → σ (y, j) ≠ x}) = 0 :=
      measure_iUnion_null fun N => stackLaw_no_hit_after hd hx N
    have hae : ∀ᵐ σ ∂(stackLaw d), σ ∉ ⋃ N : ℕ,
        {σ : Site d × ℕ → Site d | ∀ j : ℕ, N ≤ j → σ (y, j) ≠ x} := by
      rw [ae_iff]
      have hset : {σ : Site d × ℕ → Site d | ¬ σ ∉ ⋃ N : ℕ,
          {σ : Site d × ℕ → Site d | ∀ j : ℕ, N ≤ j → σ (y, j) ≠ x}}
          = ⋃ N : ℕ, {σ : Site d × ℕ → Site d | ∀ j : ℕ, N ≤ j → σ (y, j) ≠ x} := by
        ext σ; simp
      rw [hset]; exact hnull
    filter_upwards [hae] with σ hσ
    intro _
    rw [Set.mem_iUnion] at hσ
    refine Set.infinite_of_forall_exists_gt fun a => ?_
    have h : ¬ (∀ j : ℕ, a + 1 ≤ j → σ (y, j) ≠ x) := fun hc => hσ ⟨a + 1, hc⟩
    simp only [not_forall, not_not] at h
    obtain ⟨j, hj1, hj2⟩ := h
    exact ⟨j, hj2, by omega⟩
  · exact Filter.Eventually.of_forall fun σ hc => absurd hc hx

theorem ae_law_stack_hits (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    ∀ᵐ ω ∂(law d ν), ∀ y x : Site d, x ∈ nbrFinset y →
      {j : ℕ | ω.2.1 (y, j) = x}.Infinite := by
  haveI := stackLaw_isProbability (d := d) hd
  haveI := rankLaw_isProbability d
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have h1 : ∀ᵐ s ∂(stackRankLaw d), ∀ y x : Site d, x ∈ nbrFinset y →
      {j : ℕ | s.1 (y, j) = x}.Infinite :=
    (Measure.quasiMeasurePreserving_fst).ae (ae_stackLaw_hits hd)
  exact (Measure.quasiMeasurePreserving_snd).ae h1


/-- **An infinite odometer somewhere makes every odometer infinite.** -/
theorem ae_Ulimit_top_of_exists (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    ∀ᵐ ω ∂(law d ν), (∃ y : Site d, Parking.Ulimit ω y = ⊤) →
      ∀ x : Site d, Parking.Ulimit ω x = ⊤ := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hstep : ∀ᵐ ω ∂(law d ν), ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1 :=
    ae_stack_nbr hd (LatticeProb.iidLaw d ν)
  filter_upwards [hstep, ae_law_stack_hits hd ν] with ω h1 h2 ⟨y, hy⟩ x
  exact Ulimit_top_of_exists h1 h2 hy x

end Parking
