import Parking.Support.InstructionPartialCentered
import Parking.Support.RoundPartialMeas
import Parking.Support.RevealPrefix

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d K : ℕ}

/-- An enumeration of site-rank entries as common table slots. -/
def slotEnumeration (e : Fin K ↪ Site d × ℕ) : Fin K ↪ RoundSlot d :=
  ⟨fun i => Sum.inl (e i), fun _ _ h => e.injective (Sum.inl_injective h)⟩

/-- A single increment while the current round is revealed. -/
def roundDiff (e : Fin K ↪ Site d × ℕ) (A H : Site d → ℕ)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (j : Fin K)
    (τ : RoundSlot d → Fin d × Bool) : ℝ :=
  partialInt (fun _ : RoundSlot d => stepLaw d) (revealPrefix (slotEnumeration e) (j.val + 1))
    (fun ζ => matchedMeanU (roundSigned A H ζ) ρ T x) τ -
  partialInt (fun _ : RoundSlot d => stepLaw d) (revealPrefix (slotEnumeration e) j.val)
    (fun ζ => matchedMeanU (roundSigned A H ζ) ρ T x) τ

/-- A reveal difference is centered in exactly the entry being revealed. -/
theorem roundDiff_update_eq_centered (hd : 1 ≤ d) (e : Fin K ↪ Site d × ℕ)
    (A H : Site d → ℕ) (N : ℕ) (hA : ∀ y, A y ≤ N)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (j : Fin K)
    (τ : RoundSlot d → Fin d × Bool) (a : Fin d × Bool) :
    roundDiff e A H ρ T x j (Function.update τ (Sum.inl (e j)) a) =
      let f := fun b : Fin d × Bool => partialInt (fun _ : RoundSlot d => stepLaw d)
        (insert (Sum.inl (e j)) (revealPrefix (slotEnumeration e) j.val))
          (fun ζ => matchedMeanU (roundSigned A H ζ) ρ T x)
            (Function.update τ (Sum.inl (e j)) b)
      f a - ∫ b, f b ∂(stepLaw d) := by
  classical
  haveI := stepLaw_isProbability hd
  unfold roundDiff
  simp only [revealPrefix_succ]
  apply partialInt_reveal_eq_centered _ _ _ (notMem_revealPrefix (slotEnumeration e) j)
    _ ((measurable_matchedMeanU hd ρ T x).comp
      (measurable_roundSigned (fun _ => A) (fun _ => H) id measurable_const measurable_const measurable_id))
    _ (roundMeanU_bound hd A H N hA ρ T x)

/-- Every current-round increment is bounded, and its fresh-coordinate variance is at most PG² when used. -/
theorem roundDiff_section_bounds (hd : 3 ≤ d) (e : Fin K ↪ Site d × ℕ)
    (A H : Site d → ℕ) (N : ℕ) (hA : ∀ y, A y ≤ N)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (j : Fin K)
    (τ : RoundSlot d → Fin d × Bool) :
    (∀ a, |roundDiff e A H ρ T x j (Function.update τ (Sum.inl (e j)) a)| ≤ escapeConst d) ∧
      (∫ a, (roundDiff e A H ρ T x j (Function.update τ (Sum.inl (e j)) a)) ^ 2 ∂(stepLaw d)) ≤
        if (e j).2 < A (e j).1 then walkOp (fun y => fullGreen d (y - x) ^ 2) (e j).1 else 0 := by
  classical
  simp_rw [roundDiff_update_eq_centered (by omega : 1 ≤ d) e A H N hA]
  exact instruction_partial_centered_bounds hd A H N hA (e j).1 (e j).2 ρ T x
    (revealPrefix (slotEnumeration e) j.val) τ

/-- The fresh-coordinate mean of an increment vanishes at every fixed past. -/
theorem roundDiff_section_zero (hd : 1 ≤ d) (e : Fin K ↪ Site d × ℕ)
    (A H : Site d → ℕ) (N : ℕ) (hA : ∀ y, A y ≤ N)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (j : Fin K)
    (τ : RoundSlot d → Fin d × Bool) :
    ∫ a, roundDiff e A H ρ T x j (Function.update τ (Sum.inl (e j)) a) ∂(stepLaw d) = 0 := by
  classical
  haveI := stepLaw_isProbability hd
  let f : (Fin d × Bool) → ℝ := fun b => partialInt (fun _ : RoundSlot d => stepLaw d)
    (insert (Sum.inl (e j)) (revealPrefix (slotEnumeration e) j.val))
      (fun ζ => matchedMeanU (roundSigned A H ζ) ρ T x) (Function.update τ (Sum.inl (e j)) b)
  have hfi : Integrable f (stepLaw d) := Integrable.of_bound
    (measurable_from_countable' _).aestronglyMeasurable
    ((T * ((2 * T + 1) ^ d * (2 * d * N)) : ℕ) : ℝ)
    (ae_of_all _ fun b => partialRoundMean_bound hd A H N hA _ ρ T x _)
  simp_rw [roundDiff_update_eq_centered hd e A H N hA]
  change (∫ a, f a - ∫ b, f b ∂(stepLaw d) ∂(stepLaw d)) = 0
  rw [integral_sub hfi (integrable_const _)]
  simp

/-- The current-round difference is measurable when its past counts are measurable. -/
theorem measurable_roundDiff {Ω : Type*} [MeasurableSpace Ω]
    (hd : 1 ≤ d) (e : Fin K ↪ Site d × ℕ) (A H : Ω → Site d → ℕ)
    (τ : Ω → RoundSlot d → Fin d × Bool) (hA : Measurable A) (hH : Measurable H) (hτ : Measurable τ)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (j : Fin K) :
    Measurable (fun ω => roundDiff e (A ω) (H ω) ρ T x j (τ ω)) := by
  unfold roundDiff
  exact (measurable_partialRoundMean hd A H τ hA hH hτ _ ρ T x).sub
    (measurable_partialRoundMean hd A H τ hA hH hτ _ ρ T x)

/-- A current-round increment reads only the prefix through the new entry. -/
theorem roundDiff_congr (e : Fin K ↪ Site d × ℕ) (A H : Site d → ℕ)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (j : Fin K)
    (τ τ' : RoundSlot d → Fin d × Bool)
    (hτ : ∀ q ∈ revealPrefix (slotEnumeration e) (j.val + 1), τ q = τ' q) :
    roundDiff e A H ρ T x j τ = roundDiff e A H ρ T x j τ' := by
  unfold roundDiff
  rw [partialInt_congr _ _ _ hτ,
    partialInt_congr _ _ _ (fun q hq => hτ q (revealPrefix_mono _ (by omega) hq))]
end Parking
