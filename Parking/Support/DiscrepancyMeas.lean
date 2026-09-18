/-
Joint measurability of the discrepancy labels and their priority rules. Every
finite selection is measurable in the configurations, priorities, instruction
tables and the preceding state, so induction proves measurability of the full
label process.
-/
import Parking.Support.DiscrepancyLabels

noncomputable section

open MeasureTheory LatticeProb

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem Parking.measurable_priorityRank (A : Ω → Finset (Label d))
    (ρ : Ω → Label d × ℕ → ℝ) (hA : Measurable A) (hρ : Measurable ρ) (t : ℕ) (p : Label d) :
    Measurable fun ω => rankIn (A ω) (Parking.matchKey (ρ ω) t) p := by
  classical
  have hfilter : Measurable fun ω => (A ω).filter
      (fun q => Parking.matchKey (ρ ω) t q < Parking.matchKey (ρ ω) t p) := by
    apply measurable_finset_iff.mpr
    intro q
    simp only [Finset.mem_filter, Parking.matchKey, Prod.Lex.toLex_lt_toLex]
    have hmem := (measurable_finset_mem q).comp hA
    fun_prop
  exact (measurable_of_countable (Finset.card (α := Label d))).comp hfilter

theorem Parking.measurable_rankSurvivors (A B : Ω → Finset (Label d))
    (ρ : Ω → Label d × ℕ → ℝ) (hA : Measurable A) (hB : Measurable B) (hρ : Measurable ρ)
    (t : ℕ) : Measurable fun ω => Parking.rankSurvivors (A ω) (B ω) (Parking.matchKey (ρ ω) t) := by
  classical
  apply measurable_finset_iff.mpr
  intro p
  simp only [Parking.rankSurvivors, Finset.mem_filter]
  have hmem := (measurable_finset_mem p).comp hA
  have hcard := (measurable_of_countable (Finset.card (α := Label d))).comp hB
  have hrank := Parking.measurable_priorityRank A ρ hA hρ t p
  fun_prop

theorem Parking.measurable_discrepancyConf (c : Ω → Site d → ℤ × ℤ) (hc : Measurable c) :
    Measurable fun ω => Parking.discrepancyConf (c ω) := by
  fun_prop [Parking.discrepancyConf]

theorem Parking.measurable_discrepancySign (c : Ω → Site d → ℤ × ℤ) (hc : Measurable c)
    (p : Label d) : Measurable fun ω => Parking.discrepancySign (c ω) p := by
  exact (measurable_of_countable (fun z : ℤ × ℤ => decide (0 < z.2 - z.1))).comp
    ((measurable_pi_apply p.1).comp hc)

theorem Parking.measurable_discrepancyAt (c : Ω → Site d → ℤ × ℤ) (S : Ω → State d)
    (hc : Measurable c) (hS : Parking.MeasurableState S) (t : ℕ) (x : Site d) :
    Measurable fun ω => Parking.discrepancyAt (c ω) (S ω) t x :=
  Parking.measurable_matchActive _ S (Parking.measurable_discrepancyConf c hc) hS t x

theorem Parking.measurable_discrepancyMoving (c : Ω → Site d → ℤ × ℤ)
    (ρ : Ω → Label d × ℕ → ℝ) (a b : Ω → Site d → ℕ) (S : Ω → State d)
    (hc : Measurable c) (hρ : Measurable ρ) (ha : Measurable a) (hb : Measurable b)
    (hS : Parking.MeasurableState S) (t : ℕ) (p : Label d) :
    Measurable fun ω => Parking.discrepancyMoving (c ω) (ρ ω) (a ω) (b ω) (S ω) t p := by
  have hA : Measurable fun ω => Parking.discrepancyAt (c ω) (S ω) t ((S ω).pos p) :=
    Parking.measurable_eval_var _ (hS.2.1 p) _ (Parking.measurable_discrepancyAt c S hc hS t)
  have hmem := (measurable_finset_mem p).comp hA
  have hrank := Parking.measurable_priorityRank _ ρ hA hρ 0 p
  have ha' : Measurable fun ω => a ω ((S ω).pos p) :=
    Parking.measurable_eval_var _ (hS.2.1 p) a (fun x => (measurable_pi_apply x).comp ha)
  have hb' : Measurable fun ω => b ω ((S ω).pos p) :=
    Parking.measurable_eval_var _ (hS.2.1 p) b (fun x => (measurable_pi_apply x).comp hb)
  unfold Parking.discrepancyMoving Parking.discrepancyMoveCount
  exact measurableSet_setOf.mp ((measurableSet_setOf.mpr hmem).inter
    (measurableSet_lt hrank ((ha'.sub hb').add (hb'.sub ha'))))

theorem Parking.measurable_discrepancySlot (c : Ω → Site d → ℤ × ℤ)
    (ρ : Ω → Label d × ℕ → ℝ) (a b : Ω → Site d → ℕ) (S : Ω → State d)
    (hc : Measurable c) (hρ : Measurable ρ) (ha : Measurable a) (hb : Measurable b)
    (hS : Parking.MeasurableState S) (t : ℕ) (p : Label d) :
    Measurable fun ω => Parking.discrepancySlot (c ω) (ρ ω) (a ω) (b ω) (S ω) t p := by
  have hA : Measurable fun ω => Parking.discrepancyAt (c ω) (S ω) t ((S ω).pos p) :=
    Parking.measurable_eval_var _ (hS.2.1 p) _ (Parking.measurable_discrepancyAt c S hc hS t)
  have hrank := Parking.measurable_priorityRank _ ρ hA hρ 0 p
  have ha' : Measurable fun ω => a ω ((S ω).pos p) :=
    Parking.measurable_eval_var _ (hS.2.1 p) a (fun x => (measurable_pi_apply x).comp ha)
  have hb' : Measurable fun ω => b ω ((S ω).pos p) :=
    Parking.measurable_eval_var _ (hS.2.1 p) b (fun x => (measurable_pi_apply x).comp hb)
  have hmov := Parking.measurable_discrepancyMoving c ρ a b S hc hρ ha hb hS t p
  unfold Parking.discrepancySlot
  exact Measurable.ite (measurableSet_setOf.mpr hmov)
    (measurable_inl.comp ((hS.2.1 p).prodMk ((ha'.min hb').add hrank))) measurable_const

theorem Parking.measurable_discrepancyNextPos (c : Ω → Site d → ℤ × ℤ)
    (ρ : Ω → Label d × ℕ → ℝ) (a b : Ω → Site d → ℕ)
    (τ : Ω → Parking.RoundSlot d → Fin d × Bool) (S : Ω → State d)
    (hc : Measurable c) (hρ : Measurable ρ) (ha : Measurable a) (hb : Measurable b)
    (hτ : Measurable τ) (hS : Parking.MeasurableState S) (t : ℕ) (p : Label d) :
    Measurable fun ω => Parking.discrepancyNextPos (c ω) (ρ ω) (a ω) (b ω) (τ ω) (S ω) t p := by
  have hmov := Parking.measurable_discrepancyMoving c ρ a b S hc hρ ha hb hS t p
  have hslot := Parking.measurable_discrepancySlot c ρ a b S hc hρ ha hb hS t p
  have hentry : Measurable fun ω => τ ω (Parking.discrepancySlot (c ω) (ρ ω) (a ω) (b ω) (S ω) t p) :=
    Parking.measurable_eval_var _ hslot τ (fun q => (measurable_pi_apply q).comp hτ)
  unfold Parking.discrepancyNextPos
  exact Measurable.ite (measurableSet_setOf.mpr hmov)
    ((hS.2.1 p).add ((measurable_of_countable Parking.stepVec).comp hentry)) (hS.2.1 p)

theorem Parking.measurable_discrepancyArrivalsSign (c : Ω → Site d → ℤ × ℤ)
    (ρ : Ω → Label d × ℕ → ℝ) (a b : Ω → Site d → ℕ)
    (τ : Ω → Parking.RoundSlot d → Fin d × Bool) (S : Ω → State d)
    (hc : Measurable c) (hρ : Measurable ρ) (ha : Measurable a) (hb : Measurable b)
    (hτ : Measurable τ) (hS : Parking.MeasurableState S) (t : ℕ) (x : Site d) (sgn : Bool) :
    Measurable fun ω => Parking.discrepancyArrivalsSign (c ω) (ρ ω) (a ω) (b ω) (τ ω) (S ω) t x sgn := by
  have hn := Parking.measurable_discrepancyNextPos c ρ a b τ S hc hρ ha hb hτ hS t
  let S' : Ω → State d := fun ω =>
    ⟨(S ω).active, (fun p => Parking.discrepancyNextPos (c ω) (ρ ω) (a ω) (b ω) (τ ω) (S ω) t p),
      fun _ => 0, fun _ => 0⟩
  have hS' : Parking.MeasurableState S' :=
    ⟨hS.1, hn, fun _ => measurable_const, fun _ => measurable_const⟩
  have hArr : Measurable fun ω => Parking.discrepancyArrivals (c ω) (ρ ω) (a ω) (b ω) (τ ω) (S ω) t x :=
    Parking.measurable_matchActive _ S' (Parking.measurable_discrepancyConf c hc) hS' (t + 1) x
  apply measurable_finset_iff.mpr
  intro p
  simp only [Parking.discrepancyArrivalsSign, Finset.mem_filter]
  have hmem := (measurable_finset_mem p).comp hArr
  have hsign := Parking.measurable_discrepancySign c hc p
  fun_prop

theorem Parking.measurableState_discrepancyStep (c : Ω → Site d → ℤ × ℤ)
    (ρ : Ω → Label d × ℕ → ℝ) (a b : Ω → Site d → ℕ)
    (τ : Ω → Parking.RoundSlot d → Fin d × Bool) (S : Ω → State d)
    (hc : Measurable c) (hρ : Measurable ρ) (ha : Measurable a) (hb : Measurable b)
    (hτ : Measurable τ) (hS : Parking.MeasurableState S) (t : ℕ) :
    Parking.MeasurableState fun ω => Parking.discrepancyStep (c ω) (ρ ω) (a ω) (b ω) (τ ω) (S ω) t := by
  classical
  have hn := Parking.measurable_discrepancyNextPos c ρ a b τ S hc hρ ha hb hτ hS t
  refine ⟨fun p => ?_, hn, fun _ => measurable_const, fun _ => measurable_const⟩
  have hsign := Parking.measurable_discrepancySign c hc p
  let A : Ω → Finset (Label d) := fun ω => Parking.discrepancyArrivalsSign
    (c ω) (ρ ω) (a ω) (b ω) (τ ω) (S ω) t
    (Parking.discrepancyNextPos (c ω) (ρ ω) (a ω) (b ω) (τ ω) (S ω) t p)
    (Parking.discrepancySign (c ω) p)
  let B : Ω → Finset (Label d) := fun ω => Parking.discrepancyArrivalsSign
    (c ω) (ρ ω) (a ω) (b ω) (τ ω) (S ω) t
    (Parking.discrepancyNextPos (c ω) (ρ ω) (a ω) (b ω) (τ ω) (S ω) t p)
    (!Parking.discrepancySign (c ω) p)
  have hA : Measurable A := Parking.measurable_eval_var
    (fun ω => (Parking.discrepancyNextPos (c ω) (ρ ω) (a ω) (b ω) (τ ω) (S ω) t p,
      Parking.discrepancySign (c ω) p)) ((hn p).prodMk hsign)
    (fun ω q => Parking.discrepancyArrivalsSign (c ω) (ρ ω) (a ω) (b ω) (τ ω) (S ω) t q.1 q.2)
    (fun q => Parking.measurable_discrepancyArrivalsSign c ρ a b τ S hc hρ ha hb hτ hS t q.1 q.2)
  have hB : Measurable B := Parking.measurable_eval_var
    (fun ω => (Parking.discrepancyNextPos (c ω) (ρ ω) (a ω) (b ω) (τ ω) (S ω) t p,
      !Parking.discrepancySign (c ω) p)) ((hn p).prodMk (by fun_prop))
    (fun ω q => Parking.discrepancyArrivalsSign (c ω) (ρ ω) (a ω) (b ω) (τ ω) (S ω) t q.1 q.2)
    (fun q => Parking.measurable_discrepancyArrivalsSign c ρ a b τ S hc hρ ha hb hτ hS t q.1 q.2)
  exact (measurable_of_countable (fun Z : Finset (Label d) => decide (p ∈ Z))).comp
    (Parking.measurable_rankSurvivors A B ρ hA hB hρ 0)

theorem Parking.measurable_matchedCount (i₀ : Fin d) (e : Ω → Site d → ℤ)
    (ρ : Ω → Label d × ℕ → ℝ) (σ : Ω → Parking.RoundNoise d)
    (he : Measurable e) (hρ : Measurable ρ) (hσ : Measurable σ) (t : ℕ) :
    Measurable fun ω => Parking.matchedCount (e ω) (ρ ω) (σ ω) t := by
  refine measurable_pi_lambda _ fun x => ?_
  exact (measurable_of_countable (Finset.card (α := Label d))).comp
    (Parking.measurable_matchActive e _ he
      (Parking.measurableState_matchedState i₀ e ρ σ he hρ hσ t) t x)

/-- The label process is measurable jointly in its initial pair of
configurations, fixed priorities and fresh instruction tables. -/
theorem Parking.measurableState_discrepancyState (i₀ : Fin d) (c : Ω → Site d → ℤ × ℤ)
    (ρ : Ω → Label d × ℕ → ℝ) (σ : Ω → Parking.RoundNoise d)
    (hc : Measurable c) (hρ : Measurable ρ) (hσ : Measurable σ) (t : ℕ) :
    Parking.MeasurableState fun ω => Parking.discrepancyState (c ω) (ρ ω) (σ ω) t := by
  induction t with
  | zero =>
      have he := Parking.measurable_discrepancyConf c hc
      refine ⟨fun p => ?_, fun _ => measurable_const, fun x => ?_, fun _ => measurable_const⟩
      · exact (measurable_of_countable (fun z : ℤ => decide (p.2 < z.toNat))).comp
          ((measurable_pi_apply p.1).comp he)
      · exact (measurable_of_countable (fun z : ℤ => (-z).toNat)).comp
          ((measurable_pi_apply x).comp he)
  | succ t ih =>
      exact Parking.measurableState_discrepancyStep c ρ
        (fun ω => Parking.matchedCount (Parking.coupledConf false (c ω)) (ρ ω) (σ ω) t)
        (fun ω => Parking.matchedCount (Parking.coupledConf true (c ω)) (ρ ω) (σ ω) t)
        (fun ω => σ ω t) _ hc hρ
        (Parking.measurable_matchedCount i₀ _ ρ σ
          ((Parking.measurable_coupledConf false).comp hc) hρ hσ t)
        (Parking.measurable_matchedCount i₀ _ ρ σ
          ((Parking.measurable_coupledConf true).comp hc) hρ hσ t)
        ((measurable_pi_apply t).comp hσ) ih t

end
