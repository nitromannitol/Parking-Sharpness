/-
Freshness for two predictable selections from the round tables. Their entries
have independent uniform laws in every round; reversing the second direction
preserves that law and produces increments of a difference of positions.
-/
import Parking.Support.MatchedLaw

noncomputable section

open MeasureTheory LatticeProb

variable {d : ℕ}

/-- Reversing a signed direction is a bijection and negates its displacement. -/
def Parking.reverseDirection (b : Fin d × Bool) : Fin d × Bool := (b.1, !b.2)

theorem Parking.reverseDirection_involutive :
    Function.Involutive (Parking.reverseDirection (d := d)) := by
  intro b
  simp [Parking.reverseDirection]

theorem Parking.stepVec_reverseDirection (b : Fin d × Bool) :
    Parking.stepVec (Parking.reverseDirection b) = -Parking.stepVec b := by
  rcases b with ⟨i, b⟩
  cases b <;> simp [Parking.reverseDirection, Parking.stepVec]

theorem Parking.map_reverseDirection :
    (Parking.stepLaw d).map Parking.reverseDirection = Parking.stepLaw d := by
  have hm : Measurable (Parking.reverseDirection (d := d)) := measurable_from_countable' _
  rw [Parking.stepLaw, Measure.map_smul, Measure.map_finset_sum' hm.aemeasurable]
  simp_rw [Measure.map_dirac' hm]
  congr 1
  exact Equiv.sum_comp ⟨Parking.reverseDirection, Parking.reverseDirection,
    Parking.reverseDirection_involutive, Parking.reverseDirection_involutive⟩ _

/-- Two distinct entries of one fresh table are independent uniform directions.
Reversing the second entry gives the increments of the difference of two positions. -/
theorem Parking.map_pair_roundEntries (hd : 1 ≤ d) (i j : Parking.RoundSlot d) (hij : i ≠ j) :
    (Measure.infinitePi fun _ : Parking.RoundSlot d => Parking.stepLaw d).map
        (fun σ => (σ i, Parking.reverseDirection (σ j))) =
      (Parking.stepLaw d).prod (Parking.stepLaw d) := by
  haveI := Parking.stepLaw_isProbability hd
  have hpair : (Measure.infinitePi fun _ : Parking.RoundSlot d => Parking.stepLaw d).map
      (fun σ => (σ i, σ j)) = (Parking.stepLaw d).prod (Parking.stepLaw d) := by
    exact Measure.infinitePi_map_eval_prod hij
  have hrev : Measurable (Parking.reverseDirection (d := d)) := measurable_from_countable' _
  have hp : Measurable fun σ : Parking.RoundSlot d → Fin d × Bool => (σ i, σ j) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have heq : (fun σ : Parking.RoundSlot d → Fin d × Bool =>
      (σ i, Parking.reverseDirection (σ j))) =
      (Prod.map id Parking.reverseDirection) ∘ (fun σ => (σ i, σ j)) := rfl
  rw [heq, ← Measure.map_map (measurable_id.prodMap hrev) hp, hpair,
    ← Measure.map_prod_map _ _ measurable_id hrev, Measure.map_id, Parking.map_reverseDirection]

/-- Two distinct entries chosen before each round remain independent uniform
directions throughout the sequence of rounds. The choices may depend on both
processes and on every earlier input table. -/
theorem Parking.map_predictable_roundPairs (hd : 1 ≤ d)
    (i j : Parking.RoundNoise d → ℕ → Parking.RoundSlot d)
    (hi : Measurable i) (hj : Measurable j)
    (hip : ∀ σ n k v, k ≤ n → i (Function.update σ n v) k = i σ k)
    (hjp : ∀ σ n k v, k ≤ n → j (Function.update σ n v) k = j σ k)
    (hij : ∀ σ n, i σ n ≠ j σ n) :
    (Parking.roundNoiseLaw d).map
        (fun σ n => (σ n (i σ n), Parking.reverseDirection (σ n (j σ n)))) =
      Measure.infinitePi fun _ : ℕ => (Parking.stepLaw d).prod (Parking.stepLaw d) := by
  classical
  haveI := Parking.stepLaw_isProbability hd
  apply Parking.map_layers
  · refine measurable_pi_lambda _ fun n => ?_
    have hrev : Measurable (Parking.reverseDirection (d := d)) := measurable_from_countable' _
    exact (Parking.measurable_eval_var _ ((measurable_pi_apply n).comp hi)
      (fun σ q => σ n q) (fun q => (measurable_pi_apply q).comp (measurable_pi_apply n))).prodMk
      (hrev.comp (Parking.measurable_eval_var _ ((measurable_pi_apply n).comp hj)
        (fun σ q => σ n q) (fun q => (measurable_pi_apply q).comp (measurable_pi_apply n))))
  · intro σ n k v hkn
    rw [hip σ n k v (by omega), hjp σ n k v (by omega),
      Function.update_of_ne (by omega)]
  · intro n σ
    have heq : (fun v =>
        ((Function.update σ n v) n (i (Function.update σ n v) n),
          Parking.reverseDirection ((Function.update σ n v) n (j (Function.update σ n v) n)))) =
        fun v => (v (i σ n), Parking.reverseDirection (v (j σ n))) := by
      funext v
      rw [hip σ n n v le_rfl, hjp σ n n v le_rfl, Function.update_self]
    rw [heq]
    exact Parking.map_pair_roundEntries hd (i σ n) (j σ n) (hij σ n)

end
