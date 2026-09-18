/-
Comparing two configurations under a translation invariant coupling.

`lem:density-compare` has two halves and they use the two constructions.

The upper bound is the mass transport identity together with Lemma 3.6: the
expected survivor count at the origin is the expected activity there, which is
the mean of the configuration plus the expected number of unfilled holes.  The
hole counts are antitone in the configuration for FIXED instruction stacks
(`Parking.H_antitone`), so under the coupling, run with one family of stacks
and uniform variables, the hole term can only decrease.

The lower bound has no such pathwise form in the stack construction, because
the activity is a difference of odometers and raising the configuration shifts
which instruction every later departure reads.  In the particle-driven
construction it is `Parking.pSurvivorsFrom_mono`, and the two constructions
have the same law by `Parking.constructionsAgree_conf`, which is what carries
the inequality back.
-/
import Parking.Support.ConfMonotone
import Parking.Support.ActivityHoles
import Parking.Support.Monotone

noncomputable section

open MeasureTheory

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### The two data laws over one law of configurations -/

/-- The law of the particle-driven data built from a law of configurations. -/
def pLaw (d : ℕ) (μ : Measure (Site d → ℤ)) : Measure (LatticeProb.PData d) :=
  μ.prod ((LatticeProb.moveLaw d).prod (LatticeProb.rankLaw d))

/-- The survivor count at a site, read off the configuration and the activity
field alone.  Both constructions compute it from the observables the two
constructions share. -/
def survOf (t : ℕ) (y : Site d)
    (z : (Site d → ℤ) × ((ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) ×
      (ℕ × Label d → Bool))) : ℕ :=
  ((Finset.range (z.1 y).toNat).filter fun i => z.2.2.2.2 (t, (y, i))).card

theorem measurable_survOf (t : ℕ) (y : Site d) : Measurable (survOf (d := d) t y) := by
  classical
  refine measurable_of_countable_partition (fun z => z.1 y)
    ((measurable_pi_apply y).comp measurable_fst) _
    (fun N z => ((Finset.range N.toNat).filter fun i => z.2.2.2.2 (t, (y, i))).card)
    (fun N => ?_) (fun z => rfl)
  have hsum : ∀ z : (Site d → ℤ) × ((ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) × (ℕ × Site d → ℕ) ×
        (ℕ × Label d → Bool)),
      ((Finset.range N.toNat).filter fun i => z.2.2.2.2 (t, (y, i))).card
        = ∑ i ∈ Finset.range N.toNat, if z.2.2.2.2 (t, (y, i)) = true then 1 else 0 := by
    intro z
    rw [Finset.card_filter]
  simp only [hsum]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (measurable_from_countable' fun b : Bool => if b = true then 1 else 0).comp
    ((measurable_pi_apply (t, (y, i))).comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))

theorem measurable_survOf_real (t : ℕ) (y : Site d) :
    Measurable fun z => (survOf (d := d) t y z : ℝ) :=
  (measurable_from_countable' fun n : ℕ => (n : ℝ)).comp (measurable_survOf t y)

theorem survivorsFrom_eq_survOf (ω : Data d) (t : ℕ) (y : Site d) :
    LatticeProb.survivorsFrom (toDriver ω) t y
      = survOf t y (ω.1, LatticeProb.stackObservables ω) := rfl

theorem pSurvivorsFrom_eq_survOf (ω : LatticeProb.PData d) (t : ℕ) (y : Site d) :
    pSurvivorsFrom (LatticeProb.toPDriver ω) t y
      = survOf t y (ω.1, LatticeProb.pObservables ω) := rfl

/-- **The survivor count has the same law in the two constructions.** -/
theorem survivors_transfer (hd : 1 ≤ d) (μ : Measure (Site d → ℤ))
    [IsProbabilityMeasure μ] (t : ℕ) (y : Site d) :
    (Integrable (fun ω : Data d =>
        (LatticeProb.survivorsFrom (toDriver ω) t y : ℝ)) (dataLaw d μ)
      ↔ Integrable (fun ω : LatticeProb.PData d =>
        (pSurvivorsFrom (LatticeProb.toPDriver ω) t y : ℝ)) (pLaw d μ)) ∧
    ∫ ω, (LatticeProb.survivorsFrom (toDriver ω) t y : ℝ) ∂(dataLaw d μ)
      = ∫ ω, (pSurvivorsFrom (LatticeProb.toPDriver ω) t y : ℝ) ∂(pLaw d μ) := by
  have hGs : Measurable fun ω : Data d => (ω.1, LatticeProb.stackObservables ω) :=
    measurable_fst.prodMk measurable_stackObservables
  have hGp : Measurable fun ω : LatticeProb.PData d => (ω.1, LatticeProb.pObservables ω) :=
    measurable_fst.prodMk measurable_pObservables
  have hkey : (dataLaw d μ).map (fun ω : Data d => (ω.1, LatticeProb.stackObservables ω))
      = (pLaw d μ).map (fun ω : LatticeProb.PData d => (ω.1, LatticeProb.pObservables ω)) :=
    constructionsAgree_conf d hd μ
  have hf : AEStronglyMeasurable (fun z => (survOf (d := d) t y z : ℝ))
      ((dataLaw d μ).map fun ω : Data d => (ω.1, LatticeProb.stackObservables ω)) :=
    (measurable_survOf_real t y).aestronglyMeasurable
  have hf' : AEStronglyMeasurable (fun z => (survOf (d := d) t y z : ℝ))
      ((pLaw d μ).map fun ω : LatticeProb.PData d => (ω.1, LatticeProb.pObservables ω)) := by
    rw [← hkey]; exact hf
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · have h1 : Integrable (fun z => (survOf (d := d) t y z : ℝ))
        ((dataLaw d μ).map fun ω : Data d => (ω.1, LatticeProb.stackObservables ω)) :=
      (integrable_map_measure hf hGs.aemeasurable).mpr h
    rw [hkey] at h1
    exact (integrable_map_measure hf' hGp.aemeasurable).mp h1
  · have h1 : Integrable (fun z => (survOf (d := d) t y z : ℝ))
        ((pLaw d μ).map fun ω : LatticeProb.PData d => (ω.1, LatticeProb.pObservables ω)) :=
      (integrable_map_measure hf' hGp.aemeasurable).mpr h
    rw [← hkey] at h1
    exact (integrable_map_measure hf hGs.aemeasurable).mp h1
  · calc ∫ ω, (LatticeProb.survivorsFrom (toDriver ω) t y : ℝ) ∂(dataLaw d μ)
        = ∫ z, (survOf (d := d) t y z : ℝ)
            ∂((dataLaw d μ).map fun ω : Data d => (ω.1, LatticeProb.stackObservables ω)) :=
          (integral_map hGs.aemeasurable hf).symm
      _ = ∫ z, (survOf (d := d) t y z : ℝ)
            ∂((pLaw d μ).map fun ω : LatticeProb.PData d =>
              (ω.1, LatticeProb.pObservables ω)) := by rw [hkey]
      _ = ∫ ω, (pSurvivorsFrom (LatticeProb.toPDriver ω) t y : ℝ) ∂(pLaw d μ) :=
          integral_map hGp.aemeasurable hf'

/-! ### Transporting a coupling to the two data laws -/

variable {R : Type*} [MeasurableSpace R]

theorem map_coupling_fst (Q : Measure ((Site d → ℤ) × (Site d → ℤ)))
    [IsProbabilityMeasure Q] (RL : Measure R) [IsProbabilityMeasure RL]
    {μ : Measure (Site d → ℤ)} (hfst : Q.map Prod.fst = μ) :
    (Q.prod RL).map (fun p => (p.1.1, p.2)) = μ.prod RL := by
  have hrw : (fun p : ((Site d → ℤ) × (Site d → ℤ)) × R => (p.1.1, p.2))
      = Prod.map Prod.fst id := rfl
  rw [hrw, ← Measure.map_prod_map _ _ measurable_fst measurable_id, hfst, Measure.map_id]

theorem map_coupling_snd (Q : Measure ((Site d → ℤ) × (Site d → ℤ)))
    [IsProbabilityMeasure Q] (RL : Measure R) [IsProbabilityMeasure RL]
    {μ' : Measure (Site d → ℤ)} (hsnd : Q.map Prod.snd = μ') :
    (Q.prod RL).map (fun p => (p.1.2, p.2)) = μ'.prod RL := by
  have hrw : (fun p : ((Site d → ℤ) × (Site d → ℤ)) × R => (p.1.2, p.2))
      = Prod.map Prod.snd id := rfl
  rw [hrw, ← Measure.map_prod_map _ _ measurable_snd measurable_id, hsnd, Measure.map_id]

/-- A translation invariant coupling has translation invariant marginals. -/
theorem translationInvariant_of_coupling {Q : Measure ((Site d → ℤ) × (Site d → ℤ))}
    {μ : Measure (Site d → ℤ)} (hfst : Q.map Prod.fst = μ)
    (hQti : ∀ v : Site d, Q.map (fun c => (shiftConf v c.1, shiftConf v c.2)) = Q) :
    TranslationInvariant μ := by
  intro v
  have hm : Measurable fun c : (Site d → ℤ) × (Site d → ℤ) =>
      (shiftConf v c.1, shiftConf v c.2) :=
    ((measurable_shiftConf v).comp measurable_fst).prodMk
      ((measurable_shiftConf v).comp measurable_snd)
  calc μ.map (shiftConf v)
      = (Q.map Prod.fst).map (shiftConf v) := by rw [hfst]
    _ = Q.map (fun c => shiftConf v c.1) := by
        rw [Measure.map_map (measurable_shiftConf v) measurable_fst]; rfl
    _ = (Q.map fun c => (shiftConf v c.1, shiftConf v c.2)).map Prod.fst := by
        rw [Measure.map_map measurable_fst hm]; rfl
    _ = μ := by rw [hQti v, hfst]

theorem translationInvariant_of_coupling' {Q : Measure ((Site d → ℤ) × (Site d → ℤ))}
    {μ' : Measure (Site d → ℤ)} (hsnd : Q.map Prod.snd = μ')
    (hQti : ∀ v : Site d, Q.map (fun c => (shiftConf v c.1, shiftConf v c.2)) = Q) :
    TranslationInvariant μ' := by
  intro v
  have hm : Measurable fun c : (Site d → ℤ) × (Site d → ℤ) =>
      (shiftConf v c.1, shiftConf v c.2) :=
    ((measurable_shiftConf v).comp measurable_fst).prodMk
      ((measurable_shiftConf v).comp measurable_snd)
  calc μ'.map (shiftConf v)
      = (Q.map Prod.snd).map (shiftConf v) := by rw [hsnd]
    _ = Q.map (fun c => shiftConf v c.2) := by
        rw [Measure.map_map (measurable_shiftConf v) measurable_snd]; rfl
    _ = (Q.map fun c => (shiftConf v c.1, shiftConf v c.2)).map Prod.snd := by
        rw [Measure.map_map measurable_snd hm]; rfl
    _ = μ' := by rw [hQti v, hsnd]

/-! ### The two comparisons -/

theorem S_mono_of_coupling (hd : 1 ≤ d) {μ μ' : Measure (Site d → ℤ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {Q : Measure ((Site d → ℤ) × (Site d → ℤ))} [IsProbabilityMeasure Q]
    (hfst : Q.map Prod.fst = μ) (hsnd : Q.map Prod.snd = μ')
    (hmono : ∀ᵐ c ∂Q, ∀ x, c.1 x ≤ c.2 x) (t : ℕ)
    (hI : Integrable (fun ω : Data d =>
      (LatticeProb.survivorsFrom (toDriver ω) t 0 : ℝ)) (dataLaw d μ))
    (hI' : Integrable (fun ω : Data d =>
      (LatticeProb.survivorsFrom (toDriver ω) t 0 : ℝ)) (dataLaw d μ')) :
    S (dataLaw d μ) t ≤ S (dataLaw d μ') t := by
  haveI : IsProbabilityMeasure (LatticeProb.displacementLaw d) :=
    LatticeProb.instructionLaw_isProbability hd 0
  haveI : IsProbabilityMeasure (LatticeProb.moveLaw d) := by
    unfold LatticeProb.moveLaw; infer_instance
  haveI : IsProbabilityMeasure (LatticeProb.rankLaw d) := LatticeProb.rankLaw_isProbability d
  set RL : Measure ((Label d × ℕ → Site d) × (Label d × ℕ → ℝ)) :=
    (LatticeProb.moveLaw d).prod (LatticeProb.rankLaw d) with hRL
  haveI : IsProbabilityMeasure RL := by rw [hRL]; infer_instance
  have hcomp : (fun ω : LatticeProb.PData d =>
        (pSurvivorsFrom (LatticeProb.toPDriver ω) t 0 : ℝ))
      = (fun z => (survOf (d := d) t 0 z : ℝ))
        ∘ (fun ω : LatticeProb.PData d => (ω.1, LatticeProb.pObservables ω)) := by
    funext ω
    exact congrArg (fun n : ℕ => (n : ℝ)) (pSurvivorsFrom_eq_survOf ω t 0)
  have hg : Measurable fun ω : LatticeProb.PData d =>
      (pSurvivorsFrom (LatticeProb.toPDriver ω) t 0 : ℝ) := by
    rw [hcomp]
    exact (measurable_survOf_real t 0).comp
      (measurable_fst.prodMk (measurable_pObservables (d := d)))
  have hk1 : Measurable fun p : ((Site d → ℤ) × (Site d → ℤ)) × _ =>
      ((p.1.1, p.2) : LatticeProb.PData d) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hk2 : Measurable fun p : ((Site d → ℤ) × (Site d → ℤ)) × _ =>
      ((p.1.2, p.2) : LatticeProb.PData d) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hm1 : (Q.prod RL).map (fun p => ((p.1.1, p.2) : LatticeProb.PData d)) = pLaw d μ :=
    map_coupling_fst Q RL hfst
  have hm2 : (Q.prod RL).map (fun p => ((p.1.2, p.2) : LatticeProb.PData d)) = pLaw d μ' :=
    map_coupling_snd Q RL hsnd
  have hIp : Integrable (fun ω : LatticeProb.PData d =>
      (pSurvivorsFrom (LatticeProb.toPDriver ω) t 0 : ℝ)) (pLaw d μ) :=
    (survivors_transfer hd μ t 0).1.mp hI
  have hIp' : Integrable (fun ω : LatticeProb.PData d =>
      (pSurvivorsFrom (LatticeProb.toPDriver ω) t 0 : ℝ)) (pLaw d μ') :=
    (survivors_transfer hd μ' t 0).1.mp hI'
  have hIΘ : Integrable (fun p => (pSurvivorsFrom
      (LatticeProb.toPDriver ((p.1.1, p.2) : LatticeProb.PData d)) t 0 : ℝ)) (Q.prod RL) := by
    refine (integrable_map_measure
      (g := fun ω : LatticeProb.PData d => (pSurvivorsFrom (LatticeProb.toPDriver ω) t 0 : ℝ))
      (f := fun p => ((p.1.1, p.2) : LatticeProb.PData d)) (μ := Q.prod RL)
      ?_ hk1.aemeasurable).mp ?_
    · rw [hm1]; exact hg.aestronglyMeasurable
    · rw [hm1]; exact hIp
  have hIΘ' : Integrable (fun p => (pSurvivorsFrom
      (LatticeProb.toPDriver ((p.1.2, p.2) : LatticeProb.PData d)) t 0 : ℝ)) (Q.prod RL) := by
    refine (integrable_map_measure
      (g := fun ω : LatticeProb.PData d => (pSurvivorsFrom (LatticeProb.toPDriver ω) t 0 : ℝ))
      (f := fun p => ((p.1.2, p.2) : LatticeProb.PData d)) (μ := Q.prod RL)
      ?_ hk2.aemeasurable).mp ?_
    · rw [hm2]; exact hg.aestronglyMeasurable
    · rw [hm2]; exact hIp'
  have hae : ∀ᵐ p ∂(Q.prod RL), ∀ x, p.1.1 x ≤ p.1.2 x :=
    (Measure.quasiMeasurePreserving_fst).ae hmono
  show ∫ ω, (LatticeProb.survivorsFrom (toDriver ω) t 0 : ℝ) ∂(dataLaw d μ)
      ≤ ∫ ω, (LatticeProb.survivorsFrom (toDriver ω) t 0 : ℝ) ∂(dataLaw d μ')
  rw [(survivors_transfer hd μ t 0).2, (survivors_transfer hd μ' t 0).2,
    ← hm1, ← hm2, integral_map hk1.aemeasurable (by rw [hm1]; exact hg.aestronglyMeasurable),
    integral_map hk2.aemeasurable (by rw [hm2]; exact hg.aestronglyMeasurable)]
  refine integral_mono_ae hIΘ hIΘ' ?_
  filter_upwards [hae] with p hp
  have hle := pSurvivorsFrom_mono
    (D := LatticeProb.toPDriver ((p.1.1, p.2) : LatticeProb.PData d))
    (D' := LatticeProb.toPDriver ((p.1.2, p.2) : LatticeProb.PData d)) rfl rfl hp t 0
  exact (Nat.cast_le (α := ℝ)).mpr hle

theorem H_mean_mono_of_coupling (hd : 1 ≤ d) {μ μ' : Measure (Site d → ℤ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {Q : Measure ((Site d → ℤ) × (Site d → ℤ))} [IsProbabilityMeasure Q]
    (hfst : Q.map Prod.fst = μ) (hsnd : Q.map Prod.snd = μ')
    (hmono : ∀ᵐ c ∂Q, ∀ x, c.1 x ≤ c.2 x) (t : ℕ)
    (hI : Integrable (fun ω : Data d => (H ω t 0 : ℝ)) (dataLaw d μ))
    (hI' : Integrable (fun ω : Data d => (H ω t 0 : ℝ)) (dataLaw d μ')) :
    ∫ ω, (H ω t 0 : ℝ) ∂(dataLaw d μ') ≤ ∫ ω, (H ω t 0 : ℝ) ∂(dataLaw d μ) := by
  haveI := stackRankLaw_isProbability (d := d) hd
  have hg : Measurable fun ω : Data d => (H ω t 0 : ℝ) :=
    (measurable_from_countable' fun n : ℕ => (n : ℝ)).comp (measurable_H t 0)
  have hk1 : Measurable fun p : ((Site d → ℤ) × (Site d → ℤ)) × Randomness d =>
      ((p.1.1, p.2) : Data d) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hk2 : Measurable fun p : ((Site d → ℤ) × (Site d → ℤ)) × Randomness d =>
      ((p.1.2, p.2) : Data d) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hm1 : (Q.prod (stackRankLaw d)).map (fun p => ((p.1.1, p.2) : Data d)) = dataLaw d μ :=
    map_coupling_fst Q (stackRankLaw d) hfst
  have hm2 : (Q.prod (stackRankLaw d)).map (fun p => ((p.1.2, p.2) : Data d)) = dataLaw d μ' :=
    map_coupling_snd Q (stackRankLaw d) hsnd
  have hIΘ : Integrable (fun p => (H ((p.1.1, p.2) : Data d) t 0 : ℝ))
      (Q.prod (stackRankLaw d)) := by
    refine (integrable_map_measure (g := fun ω : Data d => (H ω t 0 : ℝ))
      (f := fun p => ((p.1.1, p.2) : Data d)) (μ := Q.prod (stackRankLaw d))
      ?_ hk1.aemeasurable).mp ?_
    · rw [hm1]; exact hg.aestronglyMeasurable
    · rw [hm1]; exact hI
  have hIΘ' : Integrable (fun p => (H ((p.1.2, p.2) : Data d) t 0 : ℝ))
      (Q.prod (stackRankLaw d)) := by
    refine (integrable_map_measure (g := fun ω : Data d => (H ω t 0 : ℝ))
      (f := fun p => ((p.1.2, p.2) : Data d)) (μ := Q.prod (stackRankLaw d))
      ?_ hk2.aemeasurable).mp ?_
    · rw [hm2]; exact hg.aestronglyMeasurable
    · rw [hm2]; exact hI'
  have haeconf : ∀ᵐ p ∂(Q.prod (stackRankLaw d)), ∀ x, p.1.1 x ≤ p.1.2 x :=
    (Measure.quasiMeasurePreserving_fst).ae hmono
  haveI := LatticeProb.stackLaw_isProbability (d := d) hd
  haveI := LatticeProb.rankLaw_isProbability d
  have haestack : ∀ᵐ p ∂(Q.prod (stackRankLaw d)), ∀ q : Site d × ℕ, p.2.1 q ∈ nbrFinset q.1 :=
    (Measure.quasiMeasurePreserving_snd).ae
      ((Measure.quasiMeasurePreserving_fst).ae (stackLaw_ae_nbr hd))
  rw [← hm1, ← hm2, integral_map hk1.aemeasurable (by rw [hm1]; exact hg.aestronglyMeasurable),
    integral_map hk2.aemeasurable (by rw [hm2]; exact hg.aestronglyMeasurable)]
  refine integral_mono_ae hIΘ' hIΘ ?_
  filter_upwards [haeconf, haestack] with p hp hs
  have hle := H_antitone (ω := ((p.1.1, p.2) : Data d)) (ω' := ((p.1.2, p.2) : Data d))
    rfl hs hp t 0
  exact (Nat.cast_le (α := ℝ)).mpr hle

end Parking

end
