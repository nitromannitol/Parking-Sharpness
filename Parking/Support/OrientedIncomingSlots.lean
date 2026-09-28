import Parking.Support.OrientedLayerIndependence
import Parking.Support.OrientedInstructionIntegral
import LatticeProb.Prob.Exposure

/-!
# Finite family of incoming instructions

The finite family of incoming instructions specified by a vector of counts.
-/

noncomputable section
namespace Parking
open MeasureTheory ProbabilityTheory LatticeProb Finset
open scoped Classical
variable {d : ℕ}

/-- The finite set of instruction slots `(y, j)` that could route into `x` through one of
the `d` incoming directions, with `y = x - unit i` and `j < m i`, for a given vector of
counts `m : Fin d → ℕ`. -/
def orientedIncomingSlots (x : Site d) (m : Fin d → ℕ) : Finset (Site d × ℕ) :=
  (univ.sigma fun i : Fin d => range (m i)).image fun q => (x - unit q.1, q.2)

/-- The cardinality of `orientedIncomingSlots x m` is `∑ i, m i`, since the sigma-image
construction defining it is injective. -/
theorem orientedIncomingSlots_card (x : Site d) (m : Fin d → ℕ) :
    (orientedIncomingSlots x m).card = ∑ i, m i := by
  have hi : Function.Injective (fun q : Σ _ : Fin d, ℕ => (x - unit q.1, q.2)) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have hii := unit_sub_left_inj (congrArg Prod.fst h)
    have hjj := congrArg Prod.snd h
    change i = i' at hii
    change j = j' at hjj
    subst i'
    subst j'
    rfl
  rw [orientedIncomingSlots, card_image_of_injective _ hi, card_sigma]
  simp only [card_range]

/-- A slot `q` lies in `orientedIncomingSlots x m` iff some direction `i` has `q.1 = x -
unit i` and `q.2 < m i`. -/
theorem mem_orientedIncomingSlots (x : Site d) (m : Fin d → ℕ) (q : Site d × ℕ) :
    q ∈ orientedIncomingSlots x m ↔ ∃ i : Fin d, q.1 = x - unit i ∧ q.2 < m i := by
  simp only [orientedIncomingSlots, mem_image, mem_sigma, mem_univ, true_and, mem_range]
  constructor
  · rintro ⟨⟨i, j⟩, hj, hq⟩
    subst q
    exact ⟨i, rfl, hj⟩
  · rintro ⟨i, hi, hj⟩
    exact ⟨⟨i, q.2⟩, hj, Prod.ext hi.symm rfl⟩

/-- The arrival count from `y` to `x` over the first `m` instructions is zero iff none of
those instructions route to `x`, by unfolding `arrivals` as a filtered cardinality. -/
theorem arrivals_eq_zero_iff_miss (σ : Site d × ℕ → Site d) (y x : Site d) (m : ℕ) :
    arrivals σ y x m = 0 ↔ ∀ j, j < m → σ (y, j) ≠ x := by
  simp only [arrivals, card_eq_zero, filter_eq_empty_iff, mem_range]

/-- The total arrival count at `x` after `n` rounds is zero iff, for every incoming
direction `i` and every instruction index `j` below the corresponding odometer count,
that instruction misses `x`, via `arrivals_eq_zero_iff_miss` applied to each direction. -/
theorem orientedArrivalCount_eq_zero_iff (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (n : ℕ) (x : Site d) :
    orientedArrivalCount η σ n x = 0 ↔ ∀ i : Fin d, ∀ j,
      j < orientedOdometer η σ n (x - unit i) → σ (x - unit i, j) ≠ x := by
  simp only [orientedArrivalCount, sum_eq_zero_iff, mem_univ, forall_const,
    arrivals_eq_zero_iff_miss]

/-- Conditional on the incoming odometer counts at `x`'s `d` neighbors being exactly the
vector `m`, the probability of no arrivals at `x` is `(1 - 1 / d) ^ (∑ i, m i)` times the
probability of that conditioning event, since each of the finitely many relevant
instructions (`orientedIncomingSlots x m`) independently misses `x` with probability
`1 - 1 / d` (`orientedInstructionLaw_miss_mass`), via the update-invariance exposure lemma
`measure_inter_evalBox_of_update_invariant`. -/
theorem oriented_noArrival_count_fiber (hd : 1 ≤ d) (η : Site d → ℤ) (n : ℕ)
    (x : Site d) (m : Fin d → ℕ) :
    (orientedStackLaw d).real {σ : Site d × ℕ → Site d |
      orientedArrivalCount η σ n x = 0 ∧
        (fun i : Fin d => orientedOdometer η σ n (x - unit i)) = m} =
      (1 - (d : ℝ)⁻¹) ^ (∑ i, m i) *
        (orientedStackLaw d).real {σ : Site d × ℕ → Site d |
          (fun i : Fin d => orientedOdometer η σ n (x - unit i)) = m} := by
  haveI : ∀ q : Site d × ℕ, IsProbabilityMeasure (orientedInstructionLaw q.1) :=
    fun q => orientedInstructionLaw_isProbability hd q.1
  let A : Set (Site d × ℕ → Site d) := {σ |
    (fun i : Fin d => orientedOdometer η σ n (x - unit i)) = m}
  have hA : MeasurableSet A :=
    (measurable_pi_lambda _ fun i =>
      measurable_orientedOdometer _ _ measurable_const measurable_id n (x - unit i))
      (measurableSet_singleton m)
  have hinv : ∀ q ∈ orientedIncomingSlots x m, ∀ σ : Site d × ℕ → Site d,
      Function.update σ q (0 : Site d) ∈ A ↔ σ ∈ A := by
    intro q hq σ
    obtain ⟨i, hi, _⟩ := (mem_orientedIncomingSlots x m q).mp hq
    have he : (fun k : Fin d => orientedOdometer η (Function.update σ q 0) n (x - unit k)) =
        fun k : Fin d => orientedOdometer η σ n (x - unit k) := by
      funext k
      apply orientedOdometer_update_stack
      rw [hi, layerHeight_sub, layerHeight_sub, layerHeight_unit, layerHeight_unit]
    change _ = m ↔ _ = m
    rw [he]
  have he : {σ : Site d × ℕ → Site d | orientedArrivalCount η σ n x = 0 ∧
      (fun i : Fin d => orientedOdometer η σ n (x - unit i)) = m} =
      A ∩ {σ : Site d × ℕ → Site d |
        ∀ q ∈ orientedIncomingSlots x m, σ q ∈ ({x}ᶜ : Set (Site d))} := by
    ext σ
    constructor
    · rintro ⟨hz, hm⟩
      refine ⟨hm, ?_⟩
      intro q hq
      obtain ⟨i, hi, hj⟩ := (mem_orientedIncomingSlots x m q).mp hq
      have hmi := congrFun hm i
      have hz' := (orientedArrivalCount_eq_zero_iff η σ n x).mp hz i q.2 (by rwa [hmi])
      change σ q ≠ x
      simpa only [← hi, Prod.mk.eta] using hz'
    · rintro ⟨hm, hs⟩
      refine ⟨(orientedArrivalCount_eq_zero_iff η σ n x).mpr ?_, hm⟩
      intro i j hj
      have hmi := congrFun hm i
      exact hs (x - unit i, j) ((mem_orientedIncomingSlots x m _).mpr ⟨i, rfl, by rwa [← hmi]⟩)
  have h := measure_inter_evalBox_of_update_invariant
    (fun q : Site d × ℕ => orientedInstructionLaw q.1) (fun _ => (0 : Site d)) hA
    (fun _ => ({x}ᶜ : Set (Site d))) (fun _ => (measurableSet_singleton x).compl)
    (orientedIncomingSlots x m) hinv
  rw [← he] at h
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_prod] at hr
  change (orientedStackLaw d).real _ = (orientedStackLaw d).real A *
    ∏ q ∈ orientedIncomingSlots x m, (orientedInstructionLaw q.1).real ({x}ᶜ) at hr
  have hprod : (∏ q ∈ orientedIncomingSlots x m, (orientedInstructionLaw q.1).real ({x}ᶜ)) =
      (1 - (d : ℝ)⁻¹) ^ (∑ i, m i) := by
    rw [prod_congr rfl (fun q hq => ?_)]
    · rw [prod_const, orientedIncomingSlots_card]
    · obtain ⟨i, hi, _⟩ := (mem_orientedIncomingSlots x m q).mp hq
      rw [hi]
      simpa only [sub_add_cancel] using orientedInstructionLaw_miss_mass hd (x - unit i) i
  rw [hprod] at hr
  exact hr.trans (mul_comm _ _)

end Parking
