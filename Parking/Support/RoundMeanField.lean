import Parking.Support.MatchedUniform
import Parking.Support.MeanLocality

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Arrivals are bounded by the total possible departing count at neighboring sites. -/
theorem countArrivals_le_sum (A : Site d → ℕ) (τ : RoundSlot d → Fin d × Bool) (x : Site d) :
    (countArrivals A τ x).card ≤ ∑ y ∈ nbrFinset x, A y := by
  classical
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro y _
  exact (Finset.card_image_le).trans ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (Finset.card_range (A y)))

/-- The positive part of the next signed field has a bound independent of the current directions. -/
theorem roundSigned_particle_bound (A H : Site d → ℕ) (N : ℕ) (hA : ∀ y, A y ≤ N)
    (τ : RoundSlot d → Fin d × Bool) : ∀ x, (roundSigned A H τ x).toNat ≤ 2 * d * N := by
  intro x
  have h₁ : (roundSigned A H τ x).toNat ≤ (countArrivals A τ x).card := by
    unfold roundSigned
    omega
  have h₂ : (countArrivals A τ x).card ≤ (nbrFinset x).card * N := by
    calc
      _ ≤ ∑ y ∈ nbrFinset x, A y := countArrivals_le_sum A τ x
      _ ≤ ∑ _y ∈ nbrFinset x, N := Finset.sum_le_sum fun y _ => hA y
      _ = _ := by simp
  rw [LatticeProb.Graph.Zd.card_nbrFinset] at h₂
  exact h₁.trans h₂

/-- The expected future odometer is uniformly bounded over all current-round instructions. -/
theorem roundMeanU_bound (hd : 1 ≤ d) (A H : Site d → ℕ) (N : ℕ) (hA : ∀ y, A y ≤ N)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (τ : RoundSlot d → Fin d × Bool) :
    |matchedMeanU (roundSigned A H τ) ρ T x| ≤ ((T * ((2 * T + 1) ^ d * (2 * d * N)) : ℕ) : ℝ) := by
  haveI := roundNoiseLaw_isProbability hd
  rw [abs_of_nonneg (matchedMeanU_nonneg _ _ _ _)]
  have h := integral_mono (integrable_matchedOdometer hd (roundSigned A H τ) ρ T x)
    (integrable_const ((T * ((2 * T + 1) ^ d * (2 * d * N)) : ℕ) : ℝ))
    (fun σ => Nat.cast_le.mpr (matchedOdometer_le_box _ _ (roundSigned_particle_bound A H N hA τ) ρ σ T x))
  simpa only [matchedMeanU, integral_const, probReal_univ, one_smul] using h

/-- Arrival slots vary measurably with the outgoing counts and current table. -/
theorem measurable_countArrivals {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Site d → ℕ) (τ : Ω → RoundSlot d → Fin d × Bool)
    (hA : Measurable A) (hτ : Measurable τ) (x : Site d) :
    Measurable (fun ω => countArrivals (A ω) (τ ω) x) := by
  apply measurable_finset_iff.mpr
  intro q
  cases q with
  | inr p => simp [countArrivals]
  | inl q =>
      rcases q with ⟨v, j⟩
      simp only [mem_countArrivals]
      have hAv := (measurable_pi_apply v).comp hA
      have hq := (measurable_pi_apply (Sum.inl (v, j))).comp hτ
      have hd := (measurable_of_countable (fun b : Fin d × Bool => v + stepVec b)).comp hq
      exact measurableSet_setOf.mp ((measurableSet_lt measurable_const hAv).inter
        (measurableSet_eq_fun hd measurable_const))

/-- The signed current-round field is measurable, allowing the counts to vary measurably too. -/
theorem measurable_roundSigned {Ω : Type*} [MeasurableSpace Ω]
    (A H : Ω → Site d → ℕ) (τ : Ω → RoundSlot d → Fin d × Bool)
    (hA : Measurable A) (hH : Measurable H) (hτ : Measurable τ) :
    Measurable (fun ω => roundSigned (A ω) (H ω) (τ ω)) := by
  apply measurable_pi_lambda
  intro x
  exact ((measurable_from_countable' fun s : Finset (RoundSlot d) => (s.card : ℤ)).comp
    (measurable_countArrivals A τ hA hτ x)).sub
    ((measurable_from_countable' fun n : ℕ => (n : ℤ)).comp ((measurable_pi_apply x).comp hH))

/-- Suppressing a specified instruction also gives a measurable signed field. -/
theorem measurable_roundWithout {Ω : Type*} [MeasurableSpace Ω]
    (A H : Ω → Site d → ℕ) (τ : Ω → RoundSlot d → Fin d × Bool)
    (hA : Measurable A) (hH : Measurable H) (hτ : Measurable τ) (v : Site d) (j : ℕ) :
    Measurable (fun ω => roundWithout (A ω) (H ω) (τ ω) v j) := by
  classical
  apply measurable_pi_lambda
  intro x
  exact ((measurable_from_countable' fun s : Finset (RoundSlot d) =>
    ((s.erase (Sum.inl (v, j))).card : ℤ)).comp (measurable_countArrivals A τ hA hτ x)).sub
    ((measurable_from_countable' fun n : ℕ => (n : ℤ)).comp ((measurable_pi_apply x).comp hH))

/-- Only finitely many potentially used entries can affect the future mean at a site. -/
theorem roundMeanU_agree_finite (A H : Site d → ℕ) (N : ℕ) (hA : ∀ y, A y ≤ N)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (τ τ' : RoundSlot d → Fin d × Bool)
    (hτ : ∀ y ∈ boxFinset x (T + 1), ∀ j < N, τ (Sum.inl (y, j)) = τ' (Sum.inl (y, j))) :
    matchedMeanU (roundSigned A H τ) ρ T x = matchedMeanU (roundSigned A H τ') ρ T x := by
  classical
  apply matchedMeanU_agree_box
  intro y hy
  unfold roundSigned
  apply congrArg (fun s : Finset (RoundSlot d) => (s.card : ℤ) - H y)
  apply Finset.biUnion_congr rfl
  intro z hz
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hzx : z ∈ boxFinset x (T + 1) := by
    simpa only [Nat.add_comm 1 T] using mem_boxFinset_add hy (nbrFinset_subset_box y hz)
  rw [hτ z hzx j ((Finset.mem_range.mp hj).trans_le (hA z))]
end Parking
