/-
Finite cancellation counts for the discrepancy coupling. Every lost label has
an opposite partner born within twice the horizon. The jointly measurable
pair counts satisfy the conditional random-walk bound with the initial data
and priorities fixed.
-/
import Parking.Support.DiscrepancyFresh
import Parking.Support.DiscrepancyBalance

noncomputable section

open LatticeProb
open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- A label initially present that is absent by the horizon has a cancellation partner. -/
theorem Parking.exists_discrepancyCancelledBy (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (T : ℕ) (p : Label d)
    (ha : (Parking.discrepancyState c ρ σ 0).active p = true)
    (hd : (Parking.discrepancyState c ρ σ T).active p = false) :
    ∃ q, Parking.discrepancyCancelledBy c ρ σ T p q := by
  induction T with
  | zero => simp only [ha, Bool.true_eq_false] at hd
  | succ T ih =>
      by_cases hT : (Parking.discrepancyState c ρ σ T).active p = true
      · obtain ⟨q, hq, _⟩ := Parking.existsUnique_discrepancyCancelledAt c ρ σ T p hT hd
        exact ⟨q, T, Nat.lt_succ_self T, hq⟩
      · obtain ⟨q, s, hs, hq⟩ := ih (by simpa only [Bool.not_eq_true] using hT)
        exact ⟨q, s, by omega, hq⟩

theorem Parking.discrepancyCancelledBy_symm (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (T : ℕ) (p q : Label d)
    (hpq : Parking.discrepancyCancelledBy c ρ σ T p q) :
    Parking.discrepancyCancelledBy c ρ σ T q p := by
  obtain ⟨t, ht, h⟩ := hpq
  exact ⟨t, ht, Parking.discrepancyCancelledAt_symm c ρ σ t p q h⟩

/-- Both members of a cancellation pair are initial labels. -/
theorem Parking.discrepancyCancelledBy_initial (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (T : ℕ) (p q : Label d)
    (hpq : Parking.discrepancyCancelledBy c ρ σ T p q) :
    p.2 < (Parking.discrepancyConf c p.1).toNat ∧ q.2 < (Parking.discrepancyConf c q.1).toNat := by
  obtain ⟨t, _, h⟩ := hpq
  have ha := (Finset.mem_filter.mp (Finset.mem_filter.mp h.1).1).2.1
  have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp h.2.1).1).2.1
  constructor
  · simpa [Parking.discrepancyState, initial] using Parking.discrepancyState_active_le c ρ σ p t ha
  · simpa [Parking.discrepancyState, initial] using Parking.discrepancyState_active_le c ρ σ q t hb

theorem Parking.discrepancyCancelledBy_sign (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (T : ℕ) (p q : Label d)
    (hpq : Parking.discrepancyCancelledBy c ρ σ T p q) :
    Parking.discrepancySign c q = !Parking.discrepancySign c p := by
  obtain ⟨t, _, h⟩ := hpq
  exact Parking.discrepancyCancelledAt_sign c ρ σ t p q h

/-- Opposite labels cannot originate at the same site. -/
theorem Parking.discrepancyCancelledBy_ne_site (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (T : ℕ) (p q : Label d)
    (hpq : Parking.discrepancyCancelledBy c ρ σ T p q) : p.1 ≠ q.1 := by
  intro he
  have hs := Parking.discrepancyCancelledBy_sign c ρ σ T p q hpq
  have hsame : Parking.discrepancySign c p = Parking.discrepancySign c q := by
    unfold Parking.discrepancySign
    rw [he]
  rw [hsame] at hs
  cases Parking.discrepancySign c q <;> simp at hs

/-- Only labels born within twice the horizon can cancel together. -/
theorem Parking.discrepancyCancelledBy_mem_box (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (T : ℕ) (p q : Label d)
    (hpq : Parking.discrepancyCancelledBy c ρ σ T p q) : q.1 ∈ boxFinset p.1 (2 * T) := by
  obtain ⟨t, ht, h⟩ := hpq
  have he := Parking.discrepancyCancelledAt_positions c ρ σ t p q h
  apply mem_boxFinset_iff.mpr
  intro i
  have hp := Parking.abs_discrepancyPos_sub_start_le c ρ σ (t + 1) p i
  have hq := Parking.abs_discrepancyPos_sub_start_le c ρ σ (t + 1) q i
  rw [← he] at hq
  have htri := abs_sub_le (q.1 i) ((Parking.discrepancyState c ρ σ (t + 1)).pos p i) (p.1 i)
  have hq' := hq
  rw [abs_sub_comm] at hq'
  omega

section
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The cancellation-pair relation is jointly measurable in all its inputs. -/
theorem Parking.measurable_discrepancyCancelledAt (i₀ : Fin d)
    (c : Ω → Site d → ℤ × ℤ) (ρ : Ω → Label d × ℕ → ℝ) (σ : Ω → Parking.RoundNoise d)
    (hc : Measurable c) (hρ : Measurable ρ) (hσ : Measurable σ) (t : ℕ) (p q : Label d) :
    Measurable fun ω => Parking.discrepancyCancelledAt (c ω) (ρ ω) (σ ω) t p q := by
  classical
  let a := fun ω => Parking.matchedCount (Parking.coupledConf false (c ω)) (ρ ω) (σ ω) t
  let b := fun ω => Parking.matchedCount (Parking.coupledConf true (c ω)) (ρ ω) (σ ω) t
  let S := fun ω => Parking.discrepancyState (c ω) (ρ ω) (σ ω) t
  let τ := fun ω => σ ω t
  have ha : Measurable a := Parking.measurable_matchedCount i₀ _ ρ σ
    ((Parking.measurable_coupledConf false).comp hc) hρ hσ t
  have hb : Measurable b := Parking.measurable_matchedCount i₀ _ ρ σ
    ((Parking.measurable_coupledConf true).comp hc) hρ hσ t
  have hS : Parking.MeasurableState S := Parking.measurableState_discrepancyState i₀ c ρ σ hc hρ hσ t
  have hτ : Measurable τ := (measurable_pi_apply t).comp hσ
  have hn := (Parking.measurableState_discrepancyState i₀ c ρ σ hc hρ hσ (t + 1)).2.1 p
  have hs := Parking.measurable_discrepancySign c hc p
  let A : Ω → Finset (Label d) := fun ω => Parking.discrepancyArrivalsSign
    (c ω) (ρ ω) (a ω) (b ω) (τ ω) (S ω) t
    ((Parking.discrepancyState (c ω) (ρ ω) (σ ω) (t + 1)).pos p) (Parking.discrepancySign (c ω) p)
  let B : Ω → Finset (Label d) := fun ω => Parking.discrepancyArrivalsSign
    (c ω) (ρ ω) (a ω) (b ω) (τ ω) (S ω) t
    ((Parking.discrepancyState (c ω) (ρ ω) (σ ω) (t + 1)).pos p) (!Parking.discrepancySign (c ω) p)
  have hA : Measurable A := Parking.measurable_eval_var
    (fun ω => ((Parking.discrepancyState (c ω) (ρ ω) (σ ω) (t + 1)).pos p,
      Parking.discrepancySign (c ω) p)) (hn.prodMk hs)
    (fun ω z => Parking.discrepancyArrivalsSign (c ω) (ρ ω) (a ω) (b ω) (τ ω) (S ω) t z.1 z.2)
    (fun z => Parking.measurable_discrepancyArrivalsSign c ρ a b τ S hc hρ ha hb hτ hS t z.1 z.2)
  have hB : Measurable B := Parking.measurable_eval_var
    (fun ω => ((Parking.discrepancyState (c ω) (ρ ω) (σ ω) (t + 1)).pos p,
      !Parking.discrepancySign (c ω) p)) (hn.prodMk (by fun_prop))
    (fun ω z => Parking.discrepancyArrivalsSign (c ω) (ρ ω) (a ω) (b ω) (τ ω) (S ω) t z.1 z.2)
    (fun z => Parking.measurable_discrepancyArrivalsSign c ρ a b τ S hc hρ ha hb hτ hS t z.1 z.2)
  have hAp := (measurable_finset_mem p).comp hA
  have hBq := (measurable_finset_mem q).comp hB
  have hrp := Parking.measurable_priorityRank A ρ hA hρ 0 p
  have hrq := Parking.measurable_priorityRank B ρ hB hρ 0 q
  change Measurable fun ω => p ∈ A ω ∧ q ∈ B ω ∧
    rankIn (A ω) (Parking.matchKey (ρ ω) 0) p = rankIn (B ω) (Parking.matchKey (ρ ω) 0) q
  fun_prop

theorem Parking.measurable_discrepancyCancelledBy (i₀ : Fin d)
    (c : Ω → Site d → ℤ × ℤ) (ρ : Ω → Label d × ℕ → ℝ) (σ : Ω → Parking.RoundNoise d)
    (hc : Measurable c) (hρ : Measurable ρ) (hσ : Measurable σ) (T : ℕ) (p q : Label d) :
    Measurable fun ω => Parking.discrepancyCancelledBy (c ω) (ρ ω) (σ ω) T p q := by
  apply measurableSet_setOf.mp
  rw [show {ω | Parking.discrepancyCancelledBy (c ω) (ρ ω) (σ ω) T p q} =
    ⋃ t : ℕ, {ω | t < T ∧ Parking.discrepancyCancelledAt (c ω) (ρ ω) (σ ω) t p q} by
      ext ω
      simp only [Parking.discrepancyCancelledBy, Set.mem_setOf_eq, Set.mem_iUnion]]
  apply MeasurableSet.iUnion
  intro t
  by_cases ht : t < T
  · simpa only [ht, true_and] using measurableSet_setOf.mpr
      (Parking.measurable_discrepancyCancelledAt i₀ c ρ σ hc hρ hσ t p q)
  · simp only [ht, false_and, Set.setOf_false]
    exact MeasurableSet.empty


end

/-- The finite set of pairs cancelled between site `z` and the origin. -/
def Parking.discrepancyCancelledPairs (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (T : ℕ) (z : Site d) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (Parking.discrepancyConf c z).toNat).product
    (Finset.range (Parking.discrepancyConf c 0).toNat)).filter fun ji =>
      Parking.discrepancyCancelledBy c ρ σ T (z, ji.1) (0, ji.2)

/-- The origin labels that have disappeared by a horizon. -/
def Parking.discrepancyDead (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (T : ℕ) : Finset ℕ :=
  (Finset.range (Parking.discrepancyConf c 0).toNat).filter fun i =>
    (Parking.discrepancyState c ρ σ T).active (0, i) = false

/-- Every lost origin label is counted in the finite cancellation sum. -/
theorem Parking.card_discrepancyDead_le (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (T : ℕ) :
    (Parking.discrepancyDead c ρ σ T).card ≤
      ∑ z ∈ boxFinset (0 : Site d) (2 * T), (Parking.discrepancyCancelledPairs c ρ σ T z).card := by
  classical
  have hsub : Parking.discrepancyDead c ρ σ T ⊆
      (boxFinset (0 : Site d) (2 * T)).biUnion
        (fun z => (Parking.discrepancyCancelledPairs c ρ σ T z).image Prod.snd) := by
    intro i hi
    obtain ⟨hi, hd⟩ := Finset.mem_filter.mp hi
    have ha : (Parking.discrepancyState c ρ σ 0).active (0, i) = true := by
      simpa [Parking.discrepancyState, initial] using Finset.mem_range.mp hi
    obtain ⟨q, hq⟩ := Parking.exists_discrepancyCancelledBy c ρ σ T (0, i) ha hd
    have hidx := (Parking.discrepancyCancelledBy_initial c ρ σ T (0, i) q hq).2
    have hbox := Parking.discrepancyCancelledBy_mem_box c ρ σ T (0, i) q hq
    apply Finset.mem_biUnion.mpr
    refine ⟨q.1, hbox, Finset.mem_image.mpr ⟨(q.2, i), ?_, rfl⟩⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hidx, hi⟩,
      Parking.discrepancyCancelledBy_symm c ρ σ T (0, i) q hq⟩
  calc (Parking.discrepancyDead c ρ σ T).card
      ≤ ((boxFinset (0 : Site d) (2 * T)).biUnion
          (fun z => (Parking.discrepancyCancelledPairs c ρ σ T z).image Prod.snd)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ z ∈ boxFinset (0 : Site d) (2 * T),
        ((Parking.discrepancyCancelledPairs c ρ σ T z).image Prod.snd).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun z _ => Finset.card_image_le

/-- There are no cancellations between labels created at the origin. -/
theorem Parking.discrepancyCancelledPairs_zero (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (T : ℕ) : Parking.discrepancyCancelledPairs c ρ σ T 0 = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ji hji
  have h := (Finset.mem_filter.mp hji).2
  exact Parking.discrepancyCancelledBy_ne_site c ρ σ T (0, ji.1) (0, ji.2) h rfl

/-- The cancellation-pair sets are jointly measurable. -/
theorem Parking.measurable_discrepancyCancelledPairs {Ω : Type*} [MeasurableSpace Ω]
    (i₀ : Fin d) (c : Ω → Site d → ℤ × ℤ) (ρ : Ω → Label d × ℕ → ℝ)
    (σ : Ω → Parking.RoundNoise d) (hc : Measurable c) (hρ : Measurable ρ)
    (hσ : Measurable σ) (T : ℕ) (z : Site d) :
    Measurable fun ω => Parking.discrepancyCancelledPairs (c ω) (ρ ω) (σ ω) T z := by
  classical
  have hN : ∀ x : Site d, Measurable fun ω => (Parking.discrepancyConf (c ω) x).toNat := fun x =>
    (measurable_of_countable (fun k : ℤ => k.toNat)).comp
      ((measurable_pi_apply x).comp (Parking.measurable_discrepancyConf c hc))
  apply measurable_finset_iff.mpr
  intro ji
  simp only [Parking.discrepancyCancelledPairs, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
  have hcan := Parking.measurable_discrepancyCancelledBy i₀ c ρ σ hc hρ hσ T (z, ji.1) (0, ji.2)
  fun_prop

/-- The number of pairs of initial labels with opposite signs at two sites. -/
def Parking.discrepancyOppositePairs (c : Site d → ℤ × ℤ) (z : Site d) : ℕ :=
  if Parking.discrepancySign c (z, 0) = Parking.discrepancySign c (0, 0) then 0 else
    (Parking.discrepancyConf c z).toNat * (Parking.discrepancyConf c 0).toNat

theorem Parking.discrepancyCancelledPairs_empty_of_sign (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (T : ℕ) (z : Site d)
    (hs : Parking.discrepancySign c (z, 0) = Parking.discrepancySign c (0, 0)) :
    Parking.discrepancyCancelledPairs c ρ σ T z = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ji hji
  have hsign := Parking.discrepancyCancelledBy_sign c ρ σ T (z, ji.1) (0, ji.2)
    (Finset.mem_filter.mp hji).2
  have hs' : Parking.discrepancySign c (z, ji.1) = Parking.discrepancySign c (0, ji.2) := hs
  rw [hs'] at hsign
  cases Parking.discrepancySign c (0, ji.2) <;> simp at hsign

/-- With the initial data and priorities fixed, the expected number of
cancellation pairs is bounded by the number of initial opposite pairs times
the walk hitting probability. -/
theorem Parking.lintegral_discrepancyCancelledPairs_le (hd : 1 ≤ d)
    (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ) (T : ℕ) (z : Site d) (hz : z ≠ 0) :
    ∫⁻ σ, ((Parking.discrepancyCancelledPairs c ρ σ T z).card : ℝ≥0∞) ∂(Parking.roundNoiseLaw d) ≤
      (Parking.discrepancyOppositePairs c z : ℝ≥0∞) *
        (Parking.walkLaw d) {r | ∃ s ≤ 2 * T, Parking.walkPath z r s = 0} := by
  classical
  by_cases hs : Parking.discrepancySign c (z, 0) = Parking.discrepancySign c (0, 0)
  · simp only [Parking.discrepancyCancelledPairs_empty_of_sign c ρ _ T z hs,
      Finset.card_empty, Nat.cast_zero, lintegral_zero, Parking.discrepancyOppositePairs,
      if_pos hs, zero_mul, le_refl]
  · let I := (Finset.range (Parking.discrepancyConf c z).toNat).product
      (Finset.range (Parking.discrepancyConf c 0).toNat)
    let f : ℕ × ℕ → Parking.RoundNoise d → ℝ≥0∞ := fun ji σ =>
      if Parking.discrepancyCancelledBy c ρ σ T (z, ji.1) (0, ji.2) then 1 else 0
    have hm : ∀ ji, Measurable (f ji) := by
      intro ji
      have he := measurableSet_setOf.mpr
        (Parking.measurable_discrepancyCancelledBy ⟨0, hd⟩ (fun _ => c) (fun _ => ρ) id
          measurable_const measurable_const measurable_id T (z, ji.1) (0, ji.2))
      exact Measurable.ite he measurable_const measurable_const
    have heq : ∀ σ, ((Parking.discrepancyCancelledPairs c ρ σ T z).card : ℝ≥0∞) =
        ∑ ji ∈ I, f ji σ := by
      intro σ
      unfold Parking.discrepancyCancelledPairs
      rw [Finset.card_filter]
      simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      rfl
    have hb : ∀ ji, ∫⁻ σ, f ji σ ∂(Parking.roundNoiseLaw d) ≤
        (Parking.walkLaw d) {r | ∃ s ≤ 2 * T, Parking.walkPath z r s = 0} := by
      intro ji
      have hpq : (z, ji.1) ≠ ((0 : Site d), ji.2) := by
        intro he
        exact hz (congrArg Prod.fst he)
      calc ∫⁻ σ, f ji σ ∂(Parking.roundNoiseLaw d)
          ≤ (Parking.roundNoiseLaw d) {σ | Parking.discrepancyCancelledBy c ρ σ T (z, ji.1) (0, ji.2)} :=
            lintegral_indicator_one_le _
        _ ≤ _ := by
          simpa only [sub_zero] using Parking.discrepancy_cancel_prob_le hd c ρ (z, ji.1) (0, ji.2) hpq T
    simp_rw [heq]
    rw [lintegral_finsetSum I (fun ji _ => hm ji)]
    calc ∑ ji ∈ I, ∫⁻ σ, f ji σ ∂(Parking.roundNoiseLaw d)
        ≤ ∑ _ji ∈ I, (Parking.walkLaw d) {r | ∃ s ≤ 2 * T, Parking.walkPath z r s = 0} :=
          Finset.sum_le_sum fun ji _ => hb ji
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, I, Finset.product_eq_sprod, Finset.card_product, Finset.card_range,
          Parking.discrepancyOppositePairs, if_neg hs, Nat.cast_mul]

end
