import Parking.Support.RoundMeanField
import Parking.Support.RoundHitting
import Parking.Support.BoundedMoment

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Incoming entries are the sum of their individual destination indicators. -/
theorem card_countArrivals_eq_sum (A : Site d → ℕ) (τ : RoundSlot d → Fin d × Bool) (x : Site d) :
    (countArrivals A τ x).card = ∑ y ∈ nbrFinset x, ∑ j ∈ Finset.range (A y),
      if y + stepVec (τ (Sum.inl (y, j))) = x then 1 else 0 := by
  classical
  unfold countArrivals
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro y _
    rw [Finset.card_image_of_injective _ (show Function.Injective (fun j : ℕ => (Sum.inl (y, j) : RoundSlot d)) from
      fun _ _ h => congrArg Prod.snd (Sum.inl_injective h)), Finset.card_filter]
  · intro y _ z _ hyz
    apply Finset.disjoint_left.mpr
    rintro q hq hq'
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hq
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hq'
    exact hyz (congrArg Prod.fst (Sum.inl_injective (hi.trans hj.symm)))

/-- A single fresh entry has the simple random walk transition probability. -/
theorem integral_round_entry_arrives (hd : 1 ≤ d) (y x : Site d) (j : ℕ) :
    ∫ τ, (if y + stepVec (τ (Sum.inl (y, j))) = x then (1 : ℝ) else 0)
      ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d) = kern d y x := by
  classical
  haveI := stepLaw_isProbability hd
  let f : Fin d × Bool → ℝ := fun b => if y + stepVec b = x then 1 else 0
  have hf : Measurable f := measurable_from_countable' _
  have hmap := measurePreserving_eval_infinitePi (fun _ : RoundSlot d => stepLaw d) (Sum.inl (y, j))
  have he : (∫ τ, f (τ (Sum.inl (y, j))) ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d)) =
      ∫ b, f b ∂(stepLaw d) := by
    have hi := integral_map (μ := Measure.infinitePi fun _ : RoundSlot d => stepLaw d)
      hmap.measurable.aemeasurable hf.aestronglyMeasurable
    rw [hmap.map_eq] at hi
    exact hi.symm
  rw [he]
  change (∫ b, (fun z : Site d => if z = x then (1 : ℝ) else 0) (y + stepVec b) ∂(stepLaw d)) = _
  rw [integral_stepLaw_add hd (fun z : Site d => if z = x then (1 : ℝ) else 0) y, walkOp_eq_nbrFinset]
  by_cases hx : x ∈ nbrFinset y <;> simp [kern, hx]

/-- Averaging all fresh directions sends the outgoing count through the walk operator. -/
theorem integral_countArrivals (hd : 1 ≤ d) (A : Site d → ℕ) (x : Site d) :
    ∫ τ, ((countArrivals A τ x).card : ℝ) ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d) =
      walkOp (fun y => (A y : ℝ)) x := by
  classical
  haveI := stepLaw_isProbability hd
  let μ := Measure.infinitePi fun _ : RoundSlot d => stepLaw d
  let f (y : Site d) (j : ℕ) (τ : RoundSlot d → Fin d × Bool) : ℝ :=
    if y + stepVec (τ (Sum.inl (y, j))) = x then 1 else 0
  have hi (y : Site d) (j : ℕ) : Integrable (f y j) μ := by
    have hm : Measurable (f y j) := (measurable_from_countable'
      (fun b : Fin d × Bool => if y + stepVec b = x then (1 : ℝ) else 0)).comp
        (measurable_pi_apply (Sum.inl (y, j)))
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact ae_of_all _ fun τ => by dsimp only [f]; split <;> norm_num
  have he (τ : RoundSlot d → Fin d × Bool) : ((countArrivals A τ x).card : ℝ) =
      ∑ y ∈ nbrFinset x, ∑ j ∈ Finset.range (A y), f y j τ := by
    rw [card_countArrivals_eq_sum]
    push_cast
    rfl
  simp_rw [he]
  rw [integral_finsetSum _ (fun y _ => integrable_finsetSum _ (fun j _ => hi y j))]
  have hinner (y : Site d) : (∫ τ, ∑ j ∈ Finset.range (A y), f y j τ ∂μ) = (A y : ℝ) * kern d y x := by
    rw [integral_finsetSum _ (fun j _ => hi y j)]
    have heq (j : ℕ) : (∫ τ, f y j τ ∂μ) = kern d y x := integral_round_entry_arrives hd y x j
    simp_rw [heq]
    simp
  simp_rw [hinner]
  rw [walkOp_eq_nbrFinset, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y hy
  rw [kern, if_pos (nbrFinset_symm hy)]
  ring
end Parking
