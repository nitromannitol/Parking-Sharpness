/-
Translations of the lattice act ergodically on the law of the driving data.

The law of the data is a product of three infinite products over three
different index sets, and the translation is not a coordinate shift: on the
stacks it moves the VALUE as well as the index, because an instruction is a
site and not an increment.  Both obstacles disappear at once by flattening.

Write the instruction at `(y, n)` as the increment `stack (y, n) - y`, whose
law is the uniform choice of a signed unit vector at every site, and put the
three families side by side over the disjoint union

    Slot d = Site d ⊕ (Site d × ℕ) ⊕ (Label d × ℕ)

with values in `Cell d = ℤ ⊕ Site d ⊕ ℝ`.  The law of the flattened data is
then a genuine infinite product of identical one-coordinate laws, the
translation is the plain coordinate shift along `slotShift v`, and the map back
to the data is measure preserving and intertwines the two.  Ergodicity of a
coordinate shift along an injective reindexing whose iterates push finite sets
off themselves is `LatticeProb.ergodic_coordShift_infinitePi`, and ergodicity
passes to the image of a measure preserving intertwining map.
-/
import Parking.Support.Invariance
import LatticeProb.Prob.PiSum
import LatticeProb.Prob.Translation

noncomputable section

open MeasureTheory

namespace Parking

open LatticeProb

variable {d : ℕ}

/-! ### Ergodicity passes to an intertwined image -/

/-- If `T` is ergodic and `Φ` intertwines `T` with `S`, then `S` is ergodic for
the image measure. -/
theorem ergodic_map_of_semiconj {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} {S : Ω' → Ω'} {Φ : Ω → Ω'}
    (hT : Ergodic T μ) (hΦ : Measurable Φ)
    (hS : MeasurePreserving S (μ.map Φ) (μ.map Φ))
    (hcomm : ∀ ω, Φ (T ω) = S (Φ ω)) : Ergodic S (μ.map Φ) := by
  haveI : IsProbabilityMeasure (μ.map Φ) := Measure.isProbabilityMeasure_map hΦ.aemeasurable
  refine ⟨hS, LatticeProb.preErgodic_of_prob_eq_zero_or_one ?_⟩
  intro A hA hinv
  have hpre : T ⁻¹' (Φ ⁻¹' A) = Φ ⁻¹' A := by
    ext ω
    simp only [Set.mem_preimage, hcomm ω]
    rw [← Set.mem_preimage, hinv]
  rcases hT.ae_empty_or_univ (hΦ hA) hpre with h | h
  · left
    rw [Measure.map_apply hΦ hA, measure_congr h, measure_empty]
  · right
    rw [Measure.map_apply hΦ hA, measure_congr h, measure_univ]

/-- Translating a uniform signed unit vector to the site `y` is a uniform choice
of a neighbour of `y`. -/
theorem instructionLaw_map_add (y : Site d) :
    (instructionLaw (0 : Site d)).map (fun z : Site d => z + y) = instructionLaw y := by
  have hmeas : Measurable (fun z : Site d => z + y) := measurable_id.add measurable_const
  simp only [instructionLaw]
  rw [Measure.map_smul, Measure.map_finset_sum' hmeas.aemeasurable]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.map_add _ _ hmeas, Measure.map_dirac' hmeas, Measure.map_dirac' hmeas,
    show (0 : Site d) + unit i + y = y + unit i by abel,
    show (0 : Site d) - unit i + y = y - unit i by abel]

/-! ### The flattened data -/

/-- The value carried by one coordinate of the flattened driving data: a count,
an instruction increment, or a uniform variable. -/
abbrev Cell (d : ℕ) : Type := ℤ ⊕ Site d ⊕ ℝ

/-- One coordinate of the flattened driving data. -/
abbrev Slot (d : ℕ) : Type := Site d ⊕ (Site d × ℕ) ⊕ (Label d × ℕ)

/-- The count read off a cell. -/
def cellInt : Cell d → ℤ := Sum.elim id fun _ => 0

/-- The instruction increment read off a cell. -/
def cellSite : Cell d → Site d := Sum.elim (fun _ => 0) (Sum.elim id fun _ => 0)

/-- The uniform variable read off a cell. -/
def cellReal : Cell d → ℝ := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) id)

theorem measurable_cellInt : Measurable (cellInt (d := d)) :=
  Measurable.sumElim measurable_id measurable_const

theorem measurable_cellSite : Measurable (cellSite (d := d)) :=
  Measurable.sumElim measurable_const (Measurable.sumElim measurable_id measurable_const)

theorem measurable_cellReal : Measurable (cellReal (d := d)) :=
  Measurable.sumElim measurable_const (Measurable.sumElim measurable_const measurable_id)

/-- The law of one coordinate of the flattened data. -/
def cellLaw (ν : Measure ℤ) : Slot d → Measure (Cell d) :=
  Sum.elim (fun _ => ν.map Sum.inl)
    (Sum.elim (fun _ => (instructionLaw (0 : Site d)).map (Sum.inr ∘ Sum.inl))
      fun _ => (volume.restrict (Set.Icc (0 : ℝ) 1)).map (Sum.inr ∘ Sum.inr))

/-- The translation of the coordinates of the flattened data. -/
def slotShift (v : Site d) : Slot d → Slot d :=
  Sum.elim (fun x => Sum.inl (x + v))
    (Sum.elim (fun q : Site d × ℕ => Sum.inr (Sum.inl (q.1 + v, q.2)))
      fun p : Label d × ℕ => Sum.inr (Sum.inr (shiftLabel v p.1, p.2)))

/-- The driving data read off a flattened realization: the increments are added
back to their base site, so that an instruction is again a neighbour of the
site carrying it. -/
def unflatten (ω : Slot d → Cell d) : Data d :=
  (fun x => cellInt (ω (Sum.inl x)),
    fun q => cellSite (ω (Sum.inr (Sum.inl q))) + q.1,
    fun p => cellReal (ω (Sum.inr (Sum.inr p))))

theorem measurable_unflatten : Measurable (unflatten (d := d)) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_lambda _ fun x => measurable_cellInt.comp (measurable_pi_apply _)
  · exact measurable_pi_lambda _ fun q =>
      (measurable_cellSite.comp
        (measurable_pi_apply (Sum.inr (Sum.inl q) : Slot d))).add_const q.1
  · exact measurable_pi_lambda _ fun p => measurable_cellReal.comp (measurable_pi_apply _)

theorem slotShift_injective (v : Site d) : Function.Injective (slotShift (d := d) v) := by
  rintro (x | q | p) (y | r | s) h <;>
    simp only [slotShift, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq,
      Prod.mk.injEq, reduceCtorEq] at h ⊢
  · exact add_right_cancel h
  · exact Prod.ext (add_right_cancel h.1) h.2
  · exact Prod.ext (shiftLabel_injective v h.1) h.2

theorem cellLaw_slotShift (ν : Measure ℤ) (v : Site d) (i : Slot d) :
    cellLaw (d := d) ν (slotShift v i) = cellLaw ν i := by
  rcases i with x | q | p <;> rfl

/-- The site carrying a coordinate of the flattened data. -/
def slotBase : Slot d → Site d :=
  Sum.elim id (Sum.elim (fun q : Site d × ℕ => q.1) fun p : Label d × ℕ => p.1.1)

theorem slotBase_slotShift (v : Site d) (i : Slot d) :
    slotBase (slotShift v i) = slotBase i + v := by
  rcases i with x | q | p <;> rfl

theorem slotBase_slotShift_iterate (v : Site d) (n : ℕ) (i : Slot d) :
    slotBase ((slotShift (d := d) v)^[n] i) = slotBase i + n • v := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, slotBase_slotShift, succ_nsmul]
      abel

theorem exists_slotShift_iterate_notMem {v : Site d} (hv : v ≠ 0) (s : Finset (Slot d)) :
    ∃ n : ℕ, ∀ i ∈ s, (slotShift (d := d) v)^[n] i ∉ s := by
  classical
  obtain ⟨n, hn⟩ := LatticeProb.exists_add_nsmul_notMem hv (s.image slotBase)
  refine ⟨n, fun i hi hmem => ?_⟩
  refine hn (slotBase i) (Finset.mem_image_of_mem slotBase hi) ?_
  rw [← slotBase_slotShift_iterate v n i]
  exact Finset.mem_image_of_mem slotBase hmem

/-- The coordinate shift of the flattened data is the translation of the data. -/
theorem unflatten_coordShift (v : Site d) (ω : Slot d → Cell d) :
    unflatten (LatticeProb.coordShift (slotShift v) ω) = shiftData v (unflatten ω) := by
  refine Prod.ext rfl (Prod.ext (funext fun q => ?_) rfl)
  show cellSite (ω (Sum.inr (Sum.inl (q.1 + v, q.2)))) + q.1
      = cellSite (ω (Sum.inr (Sum.inl (q.1 + v, q.2)))) + (q.1 + v) - v
  abel

/-- The three families of the flattened data, side by side. -/
def splitSlots (ω : Slot d → Cell d) :
    (Site d → Cell d) × ((Site d × ℕ → Cell d) × (Label d × ℕ → Cell d)) :=
  (fun x => ω (Sum.inl x), fun q => ω (Sum.inr (Sum.inl q)), fun p => ω (Sum.inr (Sum.inr p)))

/-- The driving data read off the three families. -/
def gatherCells
    (c : (Site d → Cell d) × ((Site d × ℕ → Cell d) × (Label d × ℕ → Cell d))) : Data d :=
  (fun x => cellInt (c.1 x), fun q => cellSite (c.2.1 q) + q.1, fun p => cellReal (c.2.2 p))

theorem unflatten_eq_comp : unflatten (d := d) = gatherCells ∘ splitSlots := rfl

theorem measurable_splitSlots : Measurable (splitSlots (d := d)) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_lambda _ fun x => measurable_pi_apply (Sum.inl x : Slot d)
  · exact measurable_pi_lambda _ fun q => measurable_pi_apply (Sum.inr (Sum.inl q) : Slot d)
  · exact measurable_pi_lambda _ fun p => measurable_pi_apply (Sum.inr (Sum.inr p) : Slot d)

theorem measurable_gatherCells : Measurable (gatherCells (d := d)) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_lambda _ fun x =>
      measurable_cellInt.comp ((measurable_pi_apply x).comp measurable_fst)
  · exact measurable_pi_lambda _ fun q =>
      (measurable_cellSite.comp
        ((measurable_pi_apply q).comp (measurable_fst.comp measurable_snd))).add_const q.1
  · exact measurable_pi_lambda _ fun p =>
      measurable_cellReal.comp ((measurable_pi_apply p).comp (measurable_snd.comp measurable_snd))

/-! ### The law of the flattened data -/

section

variable [hd1 : Fact (1 ≤ d)]

instance instructionLaw_zero_isProb : IsProbabilityMeasure (instructionLaw (0 : Site d)) :=
  instructionLaw_isProbability hd1.out 0

instance cellLaw_isProb (ν : Measure ℤ) [IsProbabilityMeasure ν] (i : Slot d) :
    IsProbabilityMeasure (cellLaw ν i) := by
  haveI := uniformUnit_isProbability
  rcases i with x | q | p
  · exact Measure.isProbabilityMeasure_map measurable_inl.aemeasurable
  · exact Measure.isProbabilityMeasure_map (measurable_inr.comp measurable_inl).aemeasurable
  · exact Measure.isProbabilityMeasure_map (measurable_inr.comp measurable_inr).aemeasurable

/-- The law of the flattened driving data. -/
def flatLaw (d : ℕ) [Fact (1 ≤ d)] (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    Measure (Slot d → Cell d) :=
  Measure.infinitePi (cellLaw (d := d) ν)

instance flatLaw_isProb (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (flatLaw d ν) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (cellLaw (d := d) ν)))

theorem flatLaw_map_splitSlots (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    (flatLaw d ν).map splitSlots
      = (Measure.infinitePi fun x : Site d => cellLaw (d := d) ν (Sum.inl x)).prod
          ((Measure.infinitePi fun q : Site d × ℕ => cellLaw (d := d) ν (Sum.inr (Sum.inl q))).prod
            (Measure.infinitePi fun p : Label d × ℕ =>
              cellLaw (d := d) ν (Sum.inr (Sum.inr p)))) := by
  have h1 := LatticeProb.infinitePi_sum (ι := Site d) (ι' := (Site d × ℕ) ⊕ (Label d × ℕ))
    (X := fun _ => Cell d) (cellLaw (d := d) ν)
  have h2 := LatticeProb.infinitePi_sum (ι := Site d × ℕ) (ι' := Label d × ℕ)
    (X := fun _ => Cell d) fun j => cellLaw (d := d) ν (Sum.inr j)
  have hm2 : Measurable (fun ω : ((Site d × ℕ) ⊕ (Label d × ℕ)) → Cell d =>
      ((fun q : Site d × ℕ => ω (Sum.inl q)), fun p : Label d × ℕ => ω (Sum.inr p))) :=
    (MeasurableEquiv.sumPiEquivProdPi fun _ : (Site d × ℕ) ⊕ (Label d × ℕ) => Cell d).measurable
  have hm1 : Measurable (fun ω : Slot d → Cell d =>
      ((fun x : Site d => ω (Sum.inl x)),
        fun j : (Site d × ℕ) ⊕ (Label d × ℕ) => ω (Sum.inr j))) :=
    (MeasurableEquiv.sumPiEquivProdPi fun _ : Slot d => Cell d).measurable
  have hstep : (flatLaw d ν).map splitSlots
      = ((flatLaw d ν).map fun ω : Slot d → Cell d =>
          ((fun x : Site d => ω (Sum.inl x)),
            fun j : (Site d × ℕ) ⊕ (Label d × ℕ) => ω (Sum.inr j))).map
          (Prod.map id fun ω : ((Site d × ℕ) ⊕ (Label d × ℕ)) → Cell d =>
            ((fun q : Site d × ℕ => ω (Sum.inl q)), fun p : Label d × ℕ => ω (Sum.inr p))) := by
    rw [Measure.map_map (measurable_id.prodMap hm2) hm1]
    rfl
  rw [hstep, flatLaw, h1, ← Measure.map_prod_map _ _ (measurable_id (α := Site d → Cell d)) hm2,
    Measure.map_id, h2]

theorem prodCellLaw_map_gatherCells (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    ((Measure.infinitePi fun x : Site d => cellLaw (d := d) ν (Sum.inl x)).prod
        ((Measure.infinitePi fun q : Site d × ℕ => cellLaw (d := d) ν (Sum.inr (Sum.inl q))).prod
          (Measure.infinitePi fun p : Label d × ℕ =>
            cellLaw (d := d) ν (Sum.inr (Sum.inr p))))).map gatherCells = law d ν := by
  haveI := uniformUnit_isProbability
  have hg1 : (Measure.infinitePi fun x : Site d => cellLaw (d := d) ν (Sum.inl x)).map
      (fun a : Site d → Cell d => fun x : Site d => cellInt (a x))
      = LatticeProb.iidLaw d ν := by
    rw [Measure.infinitePi_map_pi _ fun _ : Site d => measurable_cellInt]
    have hone : ∀ _x : Site d, (cellLaw (d := d) ν (Sum.inl _x)).map cellInt = ν := by
      intro _x
      show ((ν.map Sum.inl).map cellInt) = ν
      rw [Measure.map_map measurable_cellInt measurable_inl]
      exact Measure.map_id
    simp only [hone]
    rfl
  have hg3 : (Measure.infinitePi fun p : Label d × ℕ => cellLaw (d := d) ν (Sum.inr (Sum.inr p))).map
      (fun c : Label d × ℕ → Cell d => fun p : Label d × ℕ => cellReal (c p))
      = LatticeProb.rankLaw d := by
    rw [Measure.infinitePi_map_pi _ fun _ : Label d × ℕ => measurable_cellReal]
    have hone : ∀ _p : Label d × ℕ,
        (cellLaw (d := d) ν (Sum.inr (Sum.inr _p))).map cellReal
          = volume.restrict (Set.Icc (0 : ℝ) 1) := by
      intro _p
      show (((volume.restrict (Set.Icc (0 : ℝ) 1)).map (Sum.inr ∘ Sum.inr)).map cellReal)
        = volume.restrict (Set.Icc (0 : ℝ) 1)
      rw [Measure.map_map measurable_cellReal (measurable_inr.comp measurable_inr)]
      exact Measure.map_id
    simp only [hone]
    rfl
  have hg2 : (Measure.infinitePi fun q : Site d × ℕ =>
        cellLaw (d := d) ν (Sum.inr (Sum.inl q))).map
      (fun b : Site d × ℕ → Cell d => fun q : Site d × ℕ => cellSite (b q) + q.1)
      = LatticeProb.stackLaw d := by
    rw [Measure.infinitePi_map_pi _ fun q : Site d × ℕ =>
      measurable_cellSite.add_const q.1]
    have hone : ∀ q : Site d × ℕ,
        (cellLaw (d := d) ν (Sum.inr (Sum.inl q))).map (fun z : Cell d => cellSite z + q.1)
          = instructionLaw q.1 := by
      intro q
      show (((instructionLaw (0 : Site d)).map (Sum.inr ∘ Sum.inl)).map
        fun z : Cell d => cellSite z + q.1) = instructionLaw q.1
      rw [Measure.map_map (measurable_cellSite.add_const q.1)
        (measurable_inr.comp measurable_inl)]
      exact instructionLaw_map_add q.1
    simp only [hone]
    rfl
  have hgm2 : Measurable (fun b : Site d × ℕ → Cell d => fun q : Site d × ℕ =>
      cellSite (b q) + q.1) :=
    measurable_pi_lambda _ fun q =>
      (measurable_cellSite.comp (measurable_pi_apply q)).add_const q.1
  have hgm3 : Measurable (fun c : Label d × ℕ → Cell d => fun p : Label d × ℕ =>
      cellReal (c p)) :=
    measurable_pi_lambda _ fun p => measurable_cellReal.comp (measurable_pi_apply p)
  have hgm1 : Measurable (fun a : Site d → Cell d => fun x : Site d => cellInt (a x)) :=
    measurable_pi_lambda _ fun x => measurable_cellInt.comp (measurable_pi_apply x)
  rw [show (gatherCells (d := d))
      = Prod.map (fun a : Site d → Cell d => fun x : Site d => cellInt (a x))
          (Prod.map (fun b : Site d × ℕ → Cell d => fun q : Site d × ℕ => cellSite (b q) + q.1)
            (fun c : Label d × ℕ → Cell d => fun p : Label d × ℕ => cellReal (c p))) from rfl,
    ← Measure.map_prod_map _ _ hgm1 (hgm2.prodMap hgm3),
    ← Measure.map_prod_map _ _ hgm2 hgm3, hg1, hg2, hg3]
  rfl

theorem flatLaw_map_unflatten (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    (flatLaw d ν).map unflatten = law d ν := by
  rw [unflatten_eq_comp, ← Measure.map_map measurable_gatherCells measurable_splitSlots,
    flatLaw_map_splitSlots, prodCellLaw_map_gatherCells]

theorem ergodic_coordShift_flatLaw (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {v : Site d} (hv : v ≠ 0) :
    Ergodic (LatticeProb.coordShift (X := Cell d) (slotShift v)) (flatLaw d ν) :=
  LatticeProb.ergodic_coordShift_infinitePi (cellLaw ν) (slotShift_injective v)
    (fun i => cellLaw_slotShift ν v i) fun s => exists_slotShift_iterate_notMem hv s

end

/-- **The translations act ergodically on the law of the driving data.**  An
event invariant under a single nonzero translation has probability `0` or `1`. -/
theorem ergodic_shiftData (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {v : Site d} (hv : v ≠ 0) :
    Ergodic (shiftData (d := d) v) (law d ν) := by
  haveI : Fact (1 ≤ d) := ⟨hd⟩
  have hmp : MeasurePreserving (shiftData (d := d) v) (law d ν) (law d ν) :=
    ⟨measurable_shiftData v, law_map_shiftData hd ν v⟩
  have h := ergodic_map_of_semiconj (μ := flatLaw d ν)
    (ergodic_coordShift_flatLaw ν hv) measurable_unflatten
    (by rw [flatLaw_map_unflatten]; exact hmp) fun ω => unflatten_coordShift v ω
  rwa [flatLaw_map_unflatten] at h

end Parking

end
