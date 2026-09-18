/-
The law of the driving data is translation invariant.

The three factors are invariant for three different reasons.  The i.i.d.
configuration is invariant because translation is an injective reindexing of
the sites that preserves the one-site law.  The uniform variables are invariant
for the same reason, along the reindexing of the labels.  The stacks are the
one factor whose one-site laws are not all equal: the instruction law at `y`
lives on the neighbours of `y`.  Translating the data reads the stack of
`y + v` and translates its instructions back, and translating a uniform choice
of a neighbour of `y + v` by `-v` is a uniform choice of a neighbour of `y`, so
that factor is invariant too.
-/
import Parking.Support.Equivariance

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### The three factors -/

theorem stackLaw_isProbability (hd : 1 ≤ d) : IsProbabilityMeasure (LatticeProb.stackLaw d) := by
  haveI : ∀ y : Site d, IsProbabilityMeasure (instructionLaw y) := fun y =>
    instructionLaw_isProbability hd y
  exact inferInstanceAs
    (IsProbabilityMeasure (Measure.infinitePi fun p : Site d × ℕ => instructionLaw p.1))

theorem uniformUnit_isProbability : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  constructor
  simp

theorem rankLaw_isProbability (d : ℕ) : IsProbabilityMeasure (LatticeProb.rankLaw d) := by
  haveI := uniformUnit_isProbability
  exact inferInstanceAs (IsProbabilityMeasure
    (Measure.infinitePi fun _ : Label d × ℕ => volume.restrict (Set.Icc (0 : ℝ) 1)))

theorem stackRankLaw_isProbability (hd : 1 ≤ d) : IsProbabilityMeasure (stackRankLaw d) := by
  haveI := stackLaw_isProbability hd
  haveI := rankLaw_isProbability d
  exact inferInstanceAs
    (IsProbabilityMeasure ((LatticeProb.stackLaw d).prod (LatticeProb.rankLaw d)))

/-- Translating a uniform neighbour of `y + v` back by `v` is a uniform
neighbour of `y`. -/
theorem instructionLaw_map_sub (v y : Site d) :
    (instructionLaw (y + v)).map (fun z : Site d => z - v) = instructionLaw y := by
  have hmeas : Measurable (fun z : Site d => z - v) := measurable_id.sub measurable_const
  simp only [instructionLaw]
  rw [Measure.map_smul, Measure.map_finset_sum' hmeas.aemeasurable]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.map_add _ _ hmeas, Measure.map_dirac' hmeas, Measure.map_dirac' hmeas,
    show y + v + unit i - v = y + unit i by abel, show y + v - unit i - v = y - unit i by abel]

theorem measurable_shiftConf (v : Site d) : Measurable (shiftConf (d := d) v) :=
  measurable_pi_lambda _ fun x => measurable_pi_apply (x + v)

theorem measurable_shiftStack (v : Site d) : Measurable (shiftStack (d := d) v) := by
  show Measurable fun σ : Site d × ℕ → Site d => fun q : Site d × ℕ => σ (q.1 + v, q.2) - v
  exact measurable_pi_lambda _ fun q => (measurable_pi_apply (q.1 + v, q.2)).sub measurable_const

theorem measurable_shiftRank (v : Site d) : Measurable (shiftRank (d := d) v) := by
  show Measurable fun r : Label d × ℕ → ℝ => fun q : Label d × ℕ => r (shiftLabel v q.1, q.2)
  exact measurable_pi_lambda _ fun q => measurable_pi_apply (shiftLabel v q.1, q.2)

theorem measurable_shiftData (v : Site d) : Measurable (shiftData (d := d) v) :=
  (measurable_shiftConf v).comp measurable_fst |>.prodMk
    ((((measurable_shiftStack v).comp (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_shiftRank v).comp (measurable_snd.comp measurable_snd))))

/-- The i.i.d. configuration law is translation invariant. -/
theorem iidLaw_map_shiftConf {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (v : Site d) :
    (LatticeProb.iidLaw d ν).map (fun η : Site d → α => fun x => η (x + v))
      = LatticeProb.iidLaw d ν :=
  (LatticeProb.measurePreserving_coordShift (fun _ : Site d => ν)
    (g := fun x : Site d => x + v) (fun _ _ h => add_right_cancel h) fun _ => rfl).map_eq

theorem iidLaw_map_shiftConf' (ν : Measure ℤ) [IsProbabilityMeasure ν] (v : Site d) :
    (LatticeProb.iidLaw d ν).map (shiftConf v) = LatticeProb.iidLaw d ν :=
  iidLaw_map_shiftConf ν v

/-- The stack law is translation invariant. -/
theorem stackLaw_map_shiftStack (hd : 1 ≤ d) (v : Site d) :
    (LatticeProb.stackLaw d).map (shiftStack v) = LatticeProb.stackLaw d := by
  haveI : ∀ y : Site d, IsProbabilityMeasure (instructionLaw y) := fun y =>
    instructionLaw_isProbability hd y
  have hinj : Function.Injective fun q : Site d × ℕ => (q.1 + v, q.2) := by
    rintro ⟨x, i⟩ ⟨y, j⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (add_right_cancel h.1) h.2
  have h1 : (LatticeProb.stackLaw d).map
      (fun σ : Site d × ℕ → Site d => fun q : Site d × ℕ => σ (q.1 + v, q.2))
      = Measure.infinitePi fun q : Site d × ℕ => instructionLaw (q.1 + v) :=
    Measure.map_infinitePi_infinitePi_of_inj (P := fun p : Site d × ℕ => instructionLaw p.1) hinj
  have hmeas : Measurable (fun z : Site d => z - v) := measurable_id.sub measurable_const
  have h2 : (Measure.infinitePi fun q : Site d × ℕ => instructionLaw (q.1 + v)).map
      (fun τ : Site d × ℕ → Site d => fun q : Site d × ℕ => τ q - v)
      = Measure.infinitePi fun q : Site d × ℕ =>
          (instructionLaw (q.1 + v)).map (fun z : Site d => z - v) :=
    Measure.infinitePi_map_pi _ (f := fun _ : Site d × ℕ => fun z : Site d => z - v)
      fun _ => hmeas
  have h3 : (Measure.infinitePi fun q : Site d × ℕ =>
      (instructionLaw (q.1 + v)).map (fun z : Site d => z - v)) = LatticeProb.stackLaw d := by
    rw [LatticeProb.stackLaw]
    congr 1
    funext q
    exact instructionLaw_map_sub v q.1
  have hcomp : shiftStack (d := d) v
      = (fun τ : Site d × ℕ → Site d => fun q : Site d × ℕ => τ q - v) ∘
        (fun σ : Site d × ℕ → Site d => fun q : Site d × ℕ => σ (q.1 + v, q.2)) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1, h2, h3]

/-- The law of the uniform variables is translation invariant. -/
theorem rankLaw_map_shiftRank (v : Site d) :
    (LatticeProb.rankLaw d).map (shiftRank v) = LatticeProb.rankLaw d := by
  haveI := uniformUnit_isProbability
  have hinj : Function.Injective fun q : Label d × ℕ => (shiftLabel v q.1, q.2) := by
    rintro ⟨p, i⟩ ⟨q, j⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (shiftLabel_injective v h.1) h.2
  exact (LatticeProb.measurePreserving_coordShift
    (fun _ : Label d × ℕ => volume.restrict (Set.Icc (0 : ℝ) 1)) hinj fun _ => rfl).map_eq

/-! ### The law of the data -/

theorem stackRankLaw_map (hd : 1 ≤ d) (v : Site d) :
    (stackRankLaw d).map (Prod.map (shiftStack v) (shiftRank v)) = stackRankLaw d := by
  haveI := stackLaw_isProbability hd
  haveI := rankLaw_isProbability d
  rw [stackRankLaw, ← Measure.map_prod_map _ _ (measurable_shiftStack v) (measurable_shiftRank v),
    stackLaw_map_shiftStack hd v, rankLaw_map_shiftRank v]

/-- The law of the data built from a translation invariant configuration law is
translation invariant. -/
theorem dataLaw_map_shiftData (hd : 1 ≤ d) {μ : Measure (Site d → ℤ)}
    [IsProbabilityMeasure μ] (hti : TranslationInvariant μ) (v : Site d) :
    (dataLaw d μ).map (shiftData v) = dataLaw d μ := by
  haveI := stackRankLaw_isProbability hd
  rw [dataLaw, shiftData_eq_prodMap,
    ← Measure.map_prod_map _ _ (measurable_shiftConf v)
      ((measurable_shiftStack v).prodMap (measurable_shiftRank v)),
    hti v, stackRankLaw_map hd v]

/-- The i.i.d. law of the data is translation invariant. -/
theorem law_map_shiftData (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] (v : Site d) :
    (law d ν).map (shiftData v) = law d ν := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => ν))
  have hti : TranslationInvariant (LatticeProb.iidLaw d ν) := fun w =>
    iidLaw_map_shiftConf' ν w
  have := dataLaw_map_shiftData (μ := LatticeProb.iidLaw d ν) hd hti v
  simpa [dataLaw, law, stackRankLaw] using this

end Parking

end
