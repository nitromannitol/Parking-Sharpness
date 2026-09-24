/-
Lemma 9.3 of `parking.tex`: two unfilled holes at distinct sites are rare.

The argument is a weight-changing injection on the configuration.  On the event
that `z` still carries an unfilled hole after round `t`, no particle has reached
`z`, so the hole there has taken no part in the evolution: erasing it, that is
raising `η(z)` from `-1` to `0`, changes nothing except the hole count at `z`
itself.  That is the pathwise half, `state_eraseAt` below, and it needs the
neighbour hypothesis, which holds almost surely under the law.

The measure half is the observation that the resulting event does not read the
configuration at `z` at all, so it is independent of `η(z)`.  Comparing the two
values `-1` and `0` of `η(z)`, whose probabilities are `p` and `1 - 2p`, turns
the two-hole probability into `p/(1-2p)` times the one-hole probability, which
is at most `2p` times it once `p ≤ 1/4`.
-/
import Parking.Support.MassTransport
import Parking.Support.Range
import Parking.Support.ThreePointLaw

noncomputable section

open MeasureTheory

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### Erasing a site the process never reaches -/

/-- Two drivers that differ only in the configuration at `z`, where neither
carries a particle. -/
structure UpdateAt (z : Site d) (D' D : Driver d) : Prop where
  eta : ∀ y, y ≠ z → D'.eta y = D.eta y
  etaz' : (D'.eta z).toNat = 0
  etaz : (D.eta z).toNat = 0
  stack : D'.stack = D.stack
  rank : D'.rank = D.rank

/-- Two states that agree except possibly in the hole count at `z`. -/
structure SameOffZ (z : Site d) (S' S : State d) : Prop where
  active : ∀ p, S'.active p = S.active p
  pos : ∀ p, S'.pos p = S.pos p
  holes : ∀ y, y ≠ z → S'.holes y = S.holes y
  departures : ∀ y, S'.departures y = S.departures y

variable {z : Site d} {D' D : Driver d}

theorem candidates_updateAt (h : UpdateAt z D' D) (y : Site d) (r : ℕ) :
    candidates D'.eta y r = candidates D.eta y r := by
  ext p
  simp only [mem_candidates_iff]
  by_cases hp : p.1 = z
  · rw [hp, h.etaz', h.etaz]
  · rw [h.eta p.1 hp]

theorem activeAt_updateAt (h : UpdateAt z D' D) {S' S : State d} (hS : SameOffZ z S' S)
    (t : ℕ) (y : Site d) : activeAt D' S' t y = activeAt D S t y := by
  unfold activeAt
  rw [candidates_updateAt h]
  refine Finset.filter_congr fun p _ => ?_
  rw [hS.active p, hS.pos p]

theorem instructionIndex_updateAt (h : UpdateAt z D' D) {S' S : State d}
    (hS : SameOffZ z S' S) (t : ℕ) (p : Label d) :
    instructionIndex D' S' t p = instructionIndex D S t p := by
  unfold instructionIndex
  rw [hS.pos p, hS.departures, activeAt_updateAt h hS]

theorem nextPos_updateAt (h : UpdateAt z D' D) {S' S : State d} (hS : SameOffZ z S' S)
    (t : ℕ) (p : Label d) : nextPos D' S' t p = nextPos D S t p := by
  unfold nextPos
  rw [hS.active p, hS.pos p, instructionIndex_updateAt h hS, h.stack]

theorem arrivalsAt_updateAt (h : UpdateAt z D' D) {S' S : State d} (hS : SameOffZ z S' S)
    (t : ℕ) (x : Site d) : arrivalsAt D' S' t x = arrivalsAt D S t x := by
  unfold arrivalsAt
  rw [candidates_updateAt h]
  refine Finset.filter_congr fun p _ => ?_
  rw [hS.active p, nextPos_updateAt h hS]

/-- The state of the erased realization agrees with the original one, except at
the hole count of the erased site, as long as no particle reaches that site. -/
theorem state_eraseAt (h : UpdateAt z D' D) (hstep : StepsToNeighbour D) :
    ∀ t : ℕ, (∀ s, s < t → arrivalsAt D (state D s) s z = ∅) →
      SameOffZ z (state D' t) (state D t) := by
  intro t
  induction t with
  | zero =>
      intro _
      refine ⟨fun p => ?_, fun _ => rfl, fun y hy => ?_, fun _ => rfl⟩
      · show decide (p.2 < (D'.eta p.1).toNat) = decide (p.2 < (D.eta p.1).toNat)
        by_cases hp : p.1 = z
        · rw [hp, h.etaz', h.etaz]
        · rw [h.eta p.1 hp]
      · show (-(D'.eta y)).toNat = (-(D.eta y)).toNat
        rw [h.eta y hy]
  | succ t ih =>
      intro hz
      have hS := ih fun s hs => hz s (Nat.lt_succ_of_lt hs)
      have hzt : arrivalsAt D (state D t) t z = ∅ := hz t (Nat.lt_succ_self t)
      have hsettle : ∀ p : Label d,
          settles D' (state D' t) t p = settles D (state D t) t p := by
        intro p
        by_cases hact : (state D t).active p = true
        · have hne : nextPos D (state D t) t p ≠ z := by
            intro hcontra
            have : p ∈ arrivalsAt D (state D t) t z :=
              (mem_arrivalsAt_iff hstep t z p).mpr ⟨hact, hcontra⟩
            rw [hzt] at this
            exact absurd this (Finset.notMem_empty p)
          unfold settles
          rw [hS.active p, nextPos_updateAt h hS, arrivalsAt_updateAt h hS,
            hS.holes _ hne, h.rank]
        · simp only [Bool.not_eq_true] at hact
          unfold settles
          rw [hS.active p, hact]
          simp
      refine ⟨fun p => ?_, fun p => ?_, fun y hy => ?_, fun y => ?_⟩
      · show (step D' (state D' t) t).active p = (step D (state D t) t).active p
        simp only [step]
        rw [hS.active p, hsettle p]
      · exact nextPos_updateAt h hS t p
      · show (state D' t).holes y - (arrivalsAt D' (state D' t) t y).card
            = (state D t).holes y - (arrivalsAt D (state D t) t y).card
        rw [hS.holes y hy, arrivalsAt_updateAt h hS]
      · show (state D' t).departures y + (activeAt D' (state D' t) t y).card
            = (state D t).departures y + (activeAt D (state D t) t y).card
        rw [hS.departures y, activeAt_updateAt h hS]

/-! ### The three-point law -/

theorem threePointLaw_univ {p : ℝ} (hp : 0 ≤ p) (hp2 : 2 * p ≤ 1) :
    threePointLaw p Set.univ = 1 := by
  simp only [threePointLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp hp, ← ENNReal.ofReal_add (by linarith) (by linarith)]
  rw [show p + p + (1 - 2 * p) = 1 by ring, ENNReal.ofReal_one]

theorem threePointLaw_isProbability {p : ℝ} (hp : 0 ≤ p) (hp2 : 2 * p ≤ 1) :
    IsProbabilityMeasure (threePointLaw p) :=
  ⟨threePointLaw_univ hp hp2⟩

theorem threePointLaw_singleton_neg {p : ℝ} :
    threePointLaw p {(-1 : ℤ)} = ENNReal.ofReal p := by
  simp only [threePointLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton (-1 : ℤ))]
  norm_num

theorem threePointLaw_singleton_zero {p : ℝ} :
    threePointLaw p {(0 : ℤ)} = ENNReal.ofReal (1 - 2 * p) := by
  simp only [threePointLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton (0 : ℤ))]
  norm_num

theorem threePointLaw_le_neg_two {p : ℝ} : threePointLaw p {k : ℤ | k ≤ -2} = 0 := by
  have hmeas : MeasurableSet {k : ℤ | k ≤ -2} := measurableSet_le measurable_id measurable_const
  simp only [threePointLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ hmeas]
  norm_num [Set.indicator_of_notMem]

/-! ### Erasing the configuration at a site -/

/-- The realization with the configuration at `z` set to zero. -/
def eraseAt (z : Site d) (ω : Data d) : Data d := (Function.update ω.1 z 0, ω.2)

theorem measurable_eraseAt (z : Site d) : Measurable (eraseAt (d := d) z) := by
  refine Measurable.prodMk ?_ measurable_snd
  refine measurable_pi_lambda _ fun y => ?_
  simp only [Function.update_apply]
  by_cases hy : y = z
  · simp only [hy]
    exact measurable_const
  · simp only [hy, if_false]
    exact (measurable_pi_apply y).comp measurable_fst

theorem eraseAt_idem (z : Site d) (ω : Data d) : eraseAt z (eraseAt z ω) = eraseAt z ω := by
  simp [eraseAt, Function.update_idem]

theorem eraseAt_of_zero {z : Site d} {ω : Data d} (h : ω.1 z = 0) : eraseAt z ω = ω := by
  simp [eraseAt, ← h]

/-- On the event that `z` still carries its unfilled hole, erasing the
configuration at `z` changes no hole count elsewhere. -/
theorem H_eraseAt {ω : Data d} {z : Site d} {t : ℕ}
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1)
    (hz : ω.1 z = -1) (ht : H ω t z = 1) (x : Site d) (hxz : x ≠ z) :
    H (eraseAt z ω) t x = H ω t x := by
  have hU : UpdateAt z (toDriver (eraseAt z ω)) (toDriver ω) := by
    refine ⟨fun y hy => ?_, ?_, ?_, rfl, rfl⟩
    · show Function.update ω.1 z 0 y = ω.1 y
      exact Function.update_of_ne hy _ _
    · show ((Function.update ω.1 z 0 z : ℤ)).toNat = 0
      rw [Function.update_self]
      rfl
    · show ((ω.1 z : ℤ)).toNat = 0
      rw [hz]
      rfl
  have hSteps : StepsToNeighbour (toDriver ω) := stepsToNeighbour_of_mem hstep
  have htot : totalArrivals (toDriver ω) t z = 0 := by
    have h := holeCount_eq (toDriver ω) t z
    have hval : ((toDriver ω).eta z) = -1 := hz
    rw [hval] at h
    have h1 : H ω t z = 1 - totalArrivals (toDriver ω) t z := by
      show holeCount (toDriver ω) t z = _
      rw [h]
      norm_num
    omega
  have hempty : ∀ s, s < t → arrivalsAt (toDriver ω) (state (toDriver ω) s) s z = ∅ := by
    intro s hs
    have hsum : ∑ u ∈ Finset.range t, (arrivalsAt (toDriver ω) (state (toDriver ω) u) u z).card = 0 :=
      htot
    have := (Finset.sum_eq_zero_iff.mp hsum) s (Finset.mem_range.mpr hs)
    exact Finset.card_eq_zero.mp this
  exact (state_eraseAt hU hSteps t hempty).holes x hxz

/-! ### The measure comparison -/

variable (d)

theorem measure_inter_eval (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {G : Set (Data d)} (hGm : MeasurableSet G) (z : Site d)
    (hinv : ∀ (η : Site d → ℤ) (y : Randomness d),
      ((Function.update η z 0, y) : Data d) ∈ G ↔ ((η, y) : Data d) ∈ G)
    {s : Set ℤ} (hs : MeasurableSet s) :
    ((law d ν) (G ∩ {ω : Data d | ω.1 z ∈ s})).toReal
      = (ν s).toReal * ((law d ν) G).toReal := by
  classical
  haveI := stackRankLaw_isProbability (d := d) hd
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => ν))
  haveI : IsProbabilityMeasure (law d ν) :=
    inferInstanceAs (IsProbabilityMeasure ((LatticeProb.iidLaw d ν).prod (stackRankLaw d)))
  set f : Data d → ℝ := Set.indicator G (fun _ => (1 : ℝ)) with hf
  have hfmeas : Measurable f := (measurable_const.indicator hGm)
  have hfint : Integrable f (law d ν) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hfmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [hf]
    by_cases hω : ω ∈ G <;> simp [hω]
  have hinvf : ∀ (η : Site d → ℤ) (y : Randomness d),
      f ((Function.update η z 0, y) : Data d) = f ((η, y) : Data d) := by
    intro η y
    rw [hf]
    by_cases hmem : ((η, y) : Data d) ∈ G
    · rw [Set.indicator_of_mem ((hinv η y).mpr hmem), Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem (fun hc => hmem ((hinv η y).mp hc)),
        Set.indicator_of_notMem hmem]
  have hmain := LatticeProb.integral_mul_indicator_eval_prod
    (μ := fun _ : Site d => ν) (stackRankLaw d) z (0 : ℤ) f hfmeas hfint hinvf hs
  have hprod : ∀ ω : Data d, f ω * Set.indicator s (fun _ => (1 : ℝ)) (ω.1 z)
      = Set.indicator (G ∩ {ω : Data d | ω.1 z ∈ s}) (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases h1 : ω ∈ G <;> by_cases h2 : ω.1 z ∈ s <;>
      simp [hf, h1, h2, Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_inter_iff]
  have hGs : MeasurableSet (G ∩ {ω : Data d | ω.1 z ∈ s}) :=
    hGm.inter (((measurable_pi_apply z).comp measurable_fst) hs)
  simp only [hprod] at hmain
  rw [integral_indicator_const (1 : ℝ) hGs, hf, integral_indicator_const (1 : ℝ) hGm] at hmain
  have hlaw : law d ν = (Measure.infinitePi fun _ : Site d => ν).prod (stackRankLaw d) := rfl
  rw [hlaw]
  simpa [MeasureTheory.measureReal_def] using hmain

variable {d}

/-- Lemma 9.3 of `parking.tex`. -/
theorem close_pair (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp4 : p ≤ 1 / 4)
    (t : ℕ) (x z : Site d) (hxz : x ≠ z) :
    ((law d (threePointLaw p)) {ω : Data d | H ω t x = 1 ∧ H ω t z = 1}).toReal
      ≤ 2 * p * holeProb d (threePointLaw p) t := by
  classical
  set ν := threePointLaw p with hνdef
  haveI hνp : IsProbabilityMeasure ν := threePointLaw_isProbability hp.le (by linarith)
  haveI := stackRankLaw_isProbability (d := d) hd
  haveI hiid : IsProbabilityMeasure (LatticeProb.iidLaw d ν) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => ν))
  haveI hPp : IsProbabilityMeasure (law d ν) :=
    inferInstanceAs (IsProbabilityMeasure ((LatticeProb.iidLaw d ν).prod (stackRankLaw d)))
  set F : Set (Data d) := {ω : Data d | H ω t x = 1} with hFdef
  have hFm : MeasurableSet F := (measurable_H t x) (measurableSet_singleton 1)
  set G : Set (Data d) := eraseAt z ⁻¹' F with hGdef
  have hGm : MeasurableSet G := (measurable_eraseAt z) hFm
  have hinv : ∀ (η : Site d → ℤ) (y : Randomness d),
      ((Function.update η z 0, y) : Data d) ∈ G ↔ ((η, y) : Data d) ∈ G := by
    intro η y
    simp only [hGdef, Set.mem_preimage, eraseAt, Function.update_idem]
  have hneg := measure_inter_eval d hd ν hGm z hinv (measurableSet_singleton (-1 : ℤ))
  have hzero := measure_inter_eval d hd ν hGm z hinv (measurableSet_singleton (0 : ℤ))
  -- the two null sets
  have hbad1 : (law d ν) {ω : Data d | ¬ ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1} = 0 :=
    ae_iff.mp (ae_stack_nbr (d := d) hd (LatticeProb.iidLaw d ν))
  have hmapfst : (law d ν).map (fun ω : Data d => ω.1 z) = ν := by
    have h1 : (fun ω : Data d => ω.1 z) = (fun η : Site d → ℤ => η z) ∘ Prod.fst := rfl
    have h2 : (law d ν).map Prod.fst = LatticeProb.iidLaw d ν :=
      dataLaw_map_fst hd (LatticeProb.iidLaw d ν)
    rw [h1, ← Measure.map_map (measurable_pi_apply z) measurable_fst, h2]
    exact Measure.infinitePi_map_eval _ z
  have hbad2 : (law d ν) {ω : Data d | ω.1 z ≤ -2} = 0 := by
    have hs : MeasurableSet {k : ℤ | k ≤ -2} := measurableSet_le measurable_id measurable_const
    have hfm : Measurable (fun ω : Data d => ω.1 z) :=
      (measurable_pi_apply z).comp measurable_fst
    have hap := Measure.map_apply (μ := law d ν) hfm hs
    rw [hmapfst] at hap
    have hpre : {ω : Data d | ω.1 z ≤ -2} = (fun ω : Data d => ω.1 z) ⁻¹' {k : ℤ | k ≤ -2} := rfl
    rw [hpre, ← hap, hνdef, threePointLaw_le_neg_two]
  -- the pathwise inclusion
  have hsub : {ω : Data d | H ω t x = 1 ∧ H ω t z = 1}
      ⊆ (G ∩ {ω : Data d | ω.1 z ∈ ({-1} : Set ℤ)})
        ∪ ({ω : Data d | ¬ ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1}
          ∪ {ω : Data d | ω.1 z ≤ -2}) := by
    intro ω hω
    by_cases hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1
    · by_cases hle : ω.1 z ≤ -2
      · exact Or.inr (Or.inr hle)
      · have hcount : H ω t z = (-(ω.1 z)).toNat - totalArrivals (toDriver ω) t z :=
          holeCount_eq (toDriver ω) t z
        have hz1 : ω.1 z = -1 := by
          have := hω.2
          omega
        refine Or.inl ⟨?_, hz1⟩
        show H (eraseAt z ω) t x = 1
        rw [H_eraseAt hstep hz1 hω.2 x hxz]
        exact hω.1
    · exact Or.inr (Or.inl hstep)
  have hE : (law d ν) {ω : Data d | H ω t x = 1 ∧ H ω t z = 1}
      ≤ (law d ν) (G ∩ {ω : Data d | ω.1 z ∈ ({-1} : Set ℤ)}) := by
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_union_le _ _) ?_
    have : (law d ν) ({ω : Data d | ¬ ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1}
        ∪ {ω : Data d | ω.1 z ≤ -2}) = 0 := measure_union_null hbad1 hbad2
    rw [this, add_zero]
  -- read the two evaluations off
  have hEr : ((law d ν) {ω : Data d | H ω t x = 1 ∧ H ω t z = 1}).toReal
      ≤ (ν {(-1 : ℤ)}).toReal * ((law d ν) G).toReal := by
    rw [← hneg]
    exact ENNReal.toReal_mono (measure_ne_top _ _) hE
  have hFr : (ν {(0 : ℤ)}).toReal * ((law d ν) G).toReal ≤ ((law d ν) F).toReal := by
    rw [← hzero]
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω => ?_)
    have h0 : ω.1 z = 0 := hω.2
    have hmem : eraseAt z ω ∈ F := hω.1
    rwa [eraseAt_of_zero h0] at hmem
  have hnu1 : (ν {(-1 : ℤ)}).toReal = p := by
    rw [hνdef, threePointLaw_singleton_neg, ENNReal.toReal_ofReal hp.le]
  have hnu0 : (ν {(0 : ℤ)}).toReal = 1 - 2 * p := by
    rw [hνdef, threePointLaw_singleton_zero, ENNReal.toReal_ofReal (by linarith)]
  -- the hole probability is translation invariant
  have htrans : ((law d ν) F).toReal = holeProb d ν t := by
    have hmap := law_map_shiftData hd ν x
    have hpre : (shiftData x) ⁻¹' {ω : Data d | H ω t 0 = 1} = F := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hFdef, H_shiftData, zero_add]
    have hmeas0 : MeasurableSet {ω : Data d | H ω t 0 = 1} :=
      (measurable_H t 0) (measurableSet_singleton 1)
    rw [holeProb, ← hmap, Measure.map_apply (measurable_shiftData x) hmeas0, hpre, hmap]
  rw [hnu1] at hEr
  rw [hnu0, htrans] at hFr
  have hg : (0 : ℝ) ≤ ((law d ν) G).toReal := ENNReal.toReal_nonneg
  have h12 : (1 : ℝ) / 2 ≤ 1 - 2 * p := by linarith
  have hhalf : (1 / 2 : ℝ) * ((law d ν) G).toReal ≤ (1 - 2 * p) * ((law d ν) G).toReal :=
    mul_le_mul_of_nonneg_right h12 hg
  have hg2 : ((law d ν) G).toReal ≤ 2 * holeProb d ν t := by linarith [hhalf, hFr]
  calc ((law d ν) {ω : Data d | H ω t x = 1 ∧ H ω t z = 1}).toReal
      ≤ p * ((law d ν) G).toReal := hEr
    _ ≤ p * (2 * holeProb d ν t) := mul_le_mul_of_nonneg_left hg2 hp.le
    _ = 2 * p * holeProb d ν t := by ring

end Parking

end
