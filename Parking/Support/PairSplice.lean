/-
Splicing a PAIR of independent fields.

The randomness of the particle-driven construction is a pair: the walks of the
particles and their uniform variables.  Revealing part of it means splicing BOTH
fields along the same set of labels, and the martingale decomposition of
`Support/SpliceAvg.lean` asks for that operation to be measure preserving for two
independent copies of the pair.  It is, because the shuffle that pairs the two
copies of the first field and the two copies of the second is measure preserving
for the four-fold product; the shuffle is checked on the measurable rectangles of
the target, where it is the product of two slice computations.
-/
import Mathlib

open MeasureTheory

noncomputable section

namespace Parking

/-- **The shuffle of a pair of pairs.**  Pairing the two first components and the
two second components is measure preserving. -/
theorem measurePreserving_shuffle {B C : Type*} [MeasurableSpace B] [MeasurableSpace C]
    (μB : Measure B) (μC : Measure C) [IsProbabilityMeasure μB] [IsProbabilityMeasure μC] :
    MeasurePreserving (fun p : (B × C) × (B × C) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((μB.prod μC).prod (μB.prod μC)) ((μB.prod μB).prod (μC.prod μC)) := by
  have hmeas : Measurable
      (fun p : (B × C) × (B × C) => ((p.1.1, p.2.1), (p.1.2, p.2.2))) := by fun_prop
  refine ⟨hmeas, (Measure.prod_eq ?_).symm⟩
  intro s t hs ht
  rw [Measure.map_apply hmeas (hs.prod ht)]
  have hE : MeasurableSet
      ((fun p : (B × C) × (B × C) => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ⁻¹' (s ×ˢ t)) :=
    hmeas (hs.prod ht)
  rw [Measure.prod_apply hE]
  have hslice : ∀ ω : B × C,
      (Prod.mk ω ⁻¹' ((fun p : (B × C) × (B × C) => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ⁻¹'
        (s ×ˢ t)))
        = (Prod.mk ω.1 ⁻¹' s) ×ˢ (Prod.mk ω.2 ⁻¹' t) := by
    intro ω
    ext q
    simp [Set.mem_prod]
  simp only [hslice]
  have hprod : ∀ ω : B × C,
      (μB.prod μC) ((Prod.mk ω.1 ⁻¹' s) ×ˢ (Prod.mk ω.2 ⁻¹' t))
        = μB (Prod.mk ω.1 ⁻¹' s) * μC (Prod.mk ω.2 ⁻¹' t) := by
    intro ω
    exact Measure.prod_prod _ _
  simp only [hprod]
  have hf : AEMeasurable (fun b : B => μB (Prod.mk b ⁻¹' s)) μB :=
    (measurable_measure_prodMk_left hs).aemeasurable
  have hg : AEMeasurable (fun c : C => μC (Prod.mk c ⁻¹' t)) μC :=
    (measurable_measure_prodMk_left ht).aemeasurable
  rw [lintegral_prod_mul (f := fun b : B => μB (Prod.mk b ⁻¹' s))
    (g := fun c : C => μC (Prod.mk c ⁻¹' t)) hf hg]
  rw [Measure.prod_apply hs, Measure.prod_apply ht]

/-- **Splicing a pair of independent fields is measure preserving.** -/
theorem measurePreserving_pairSplice {B C : Type*} [MeasurableSpace B] [MeasurableSpace C]
    (μB : Measure B) (μC : Measure C) [IsProbabilityMeasure μB] [IsProbabilityMeasure μC]
    {cB : B → B → B} {cC : C → C → C}
    (hB : MeasurePreserving (fun p : B × B => cB p.1 p.2) (μB.prod μB) μB)
    (hC : MeasurePreserving (fun p : C × C => cC p.1 p.2) (μC.prod μC) μC) :
    MeasurePreserving (fun p : (B × C) × (B × C) => (cB p.1.1 p.2.1, cC p.1.2 p.2.2))
      ((μB.prod μC).prod (μB.prod μC)) (μB.prod μC) :=
  (hB.prod hC).comp (measurePreserving_shuffle μB μC)

end Parking

end
