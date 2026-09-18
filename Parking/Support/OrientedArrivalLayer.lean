/- The directed layer average of the arrival count, unrolled over the routing instructions. -/
import Parking.Support.OrientedRouteOp
import Parking.Support.OrientedFreshness
import Parking.Support.BoxTranslation
import Parking.Support.OrientedErrorRoute
import Parking.Support.OrientedFiniteRoute
noncomputable section

namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

theorem summable_orientedRouteSum (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (hσ : ∀ q : Site d × ℕ, ∃ i : Fin d, σ q = q.1 + unit i) (k m : ℕ) :
    Summable fun y : Site d => ∑ j ∈ Finset.range (orientedOdometer η σ k y),
      orientedLayer d m (σ (y, j)) := by
  refine summable_of_ne_finset_zero
    (s := Finset.univ.biUnion fun i : Fin d => boxFinset (-(unit i)) m) fun y hy => ?_
  refine Finset.sum_eq_zero fun j _ => ?_
  obtain ⟨i₀, hi₀⟩ := hσ (y, j)
  rw [hi₀]
  by_contra hne
  refine hy (Finset.mem_biUnion.mpr ⟨i₀, Finset.mem_univ _, ?_⟩)
  have h := orientedLayer_mem_box hne
  rw [mem_boxFinset_iff] at h ⊢
  intro i
  simpa using h i

theorem orientedLayerAverage_arrival_eq (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (hσ : ∀ q : Site d × ℕ, ∃ i : Fin d, σ q = q.1 + unit i) (k m : ℕ) :
    (∑' z : Site d, orientedLayer d m z * (orientedArrivalCount η σ k z : ℝ)) =
      ∑' y : Site d, ∑ j ∈ Finset.range (orientedOdometer η σ k y),
        orientedLayer d m (σ (y, j)) := by
  classical
  have hterm : ∀ z : Site d, (orientedArrivalCount η σ k z : ℝ) =
      ∑ i : Fin d, ∑ j ∈ Finset.range (orientedOdometer η σ k (z - unit i)),
        (if σ (z - unit i, j) = z then (1 : ℝ) else 0) := by
    intro z
    rw [orientedArrivalCount, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [arrivals, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : σ (z - unit i, j) = z <;> simp [h]
  rw [tsum_congr fun z => by rw [hterm]]
  simp only [Finset.mul_sum]
  have hsum : ∀ i : Fin d, Summable fun z : Site d =>
      ∑ j ∈ Finset.range (orientedOdometer η σ k (z - unit i)),
        orientedLayer d m z * (if σ (z - unit i, j) = z then (1 : ℝ) else 0) := by
    intro i
    refine summable_of_ne_finset_zero (s := boxFinset 0 m) fun z hz => ?_
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [orientedLayer_eq_zero_of_notMem hz, zero_mul]
  rw [Summable.tsum_finsetSum (fun i _ => hsum i)]
  have hshift : ∀ i : Fin d, (∑' z : Site d,
      ∑ j ∈ Finset.range (orientedOdometer η σ k (z - unit i)),
        orientedLayer d m z * (if σ (z - unit i, j) = z then (1 : ℝ) else 0)) =
      ∑' y : Site d, ∑ j ∈ Finset.range (orientedOdometer η σ k y),
        orientedLayer d m (y + unit i) * (if σ (y, j) = y + unit i then (1 : ℝ) else 0) := by
    intro i
    have h := (Equiv.subRight (unit i)).tsum_eq (fun y : Site d =>
      ∑ j ∈ Finset.range (orientedOdometer η σ k y),
        orientedLayer d m (y + unit i) * (if σ (y, j) = y + unit i then (1 : ℝ) else 0))
    rw [← h]
    refine tsum_congr fun z => ?_
    simp only [Equiv.subRight_apply, sub_add_cancel]
  rw [Finset.sum_congr rfl fun i _ => hshift i]
  have hsum2 : ∀ i : Fin d, Summable fun y : Site d =>
      ∑ j ∈ Finset.range (orientedOdometer η σ k y),
        orientedLayer d m (y + unit i) * (if σ (y, j) = y + unit i then (1 : ℝ) else 0) := by
    intro i
    rw [← (Equiv.subRight (unit i)).summable_iff]
    refine (hsum i).congr fun z => ?_
    show _ = ∑ j ∈ Finset.range (orientedOdometer η σ k (z - unit i)),
        orientedLayer d m (z - unit i + unit i) * (if σ (z - unit i, j) = z - unit i + unit i then (1 : ℝ) else 0)
    simp only [sub_add_cancel]
  rw [← Summable.tsum_finsetSum (fun i _ => hsum2 i)]
  refine tsum_congr fun y => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨i₀, hi₀⟩ := hσ (y, j)
  have hi₀' : σ (y, j) = y + unit i₀ := hi₀
  rw [hi₀']
  rw [Finset.sum_eq_single i₀]
  · simp
  · intro i _ hi
    have hne : y + unit i₀ ≠ y + unit i := fun h => hi (unit_injective (add_left_cancel h : unit i₀ = unit i)).symm
    rw [if_neg hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

theorem orientedLayerAverage_noise_eq (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (hσ : ∀ q : Site d × ℕ, ∃ i : Fin d, σ q = q.1 + unit i) (k m : ℕ) :
    (∑' z : Site d, orientedLayer d m z * orientedNoise η σ k z) =
      ∑' y : Site d, ∑ j ∈ Finset.range (orientedOdometer η σ k y),
        orientedRouteDisc m y (σ (y, j)) := by
  have h1 := orientedLayerAverage_arrival_eq η σ hσ k m
  have h2 := orientedLayerAverage_op_eq η σ k m
  have hsplit : ∀ z : Site d, orientedLayer d m z * orientedNoise η σ k z =
      orientedLayer d m z * (orientedArrivalCount η σ k z : ℝ) -
        orientedLayer d m z * orientedOp (fun y => (orientedOdometer η σ k y : ℝ)) z := by
    intro z; rw [orientedNoise]; ring
  rw [tsum_congr hsplit]
  have hs1 : Summable fun z : Site d =>
      orientedLayer d m z * (orientedArrivalCount η σ k z : ℝ) := by
    refine summable_of_ne_finset_zero (s := boxFinset 0 m) fun z hz => ?_
    rw [orientedLayer_eq_zero_of_notMem hz, zero_mul]
  have hs2 : Summable fun z : Site d =>
      orientedLayer d m z * orientedOp (fun y => (orientedOdometer η σ k y : ℝ)) z := by
    refine summable_of_ne_finset_zero (s := boxFinset 0 m) fun z hz => ?_
    rw [orientedLayer_eq_zero_of_notMem hz, zero_mul]
  rw [Summable.tsum_sub hs1 hs2, h1, h2]
  have hA := summable_orientedRouteSum η σ hσ k m
  have hB : Summable fun y : Site d => ∑ j ∈ Finset.range (orientedOdometer η σ k y),
      orientedLayer d (m + 1) y :=
    (summable_orientedLayer_weight (m + 1) (fun y => (orientedOdometer η σ k y : ℝ))).congr
      fun y => by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range, mul_comm]
  rw [← Summable.tsum_sub hA hB]
  refine tsum_congr fun y => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [orientedRouteDisc]


theorem wErrOriented_eq_routeSum (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (hσ : ∀ q : Site d × ℕ, ∃ i : Fin d, σ q = q.1 + unit i) (n : ℕ) :
    wErrOriented η σ n 0 = ∑ k ∈ Finset.range n,
      ∑' y : Site d, ∑ j ∈ Finset.range (orientedOdometer η σ k y),
        orientedRouteDisc (n - (k + 1)) y (σ (y, j)) := by
  rw [wErrOriented_eq_orientedError, orientedError_eq_layers]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [orientedLayerAverage_at_zero]
  exact orientedLayerAverage_noise_eq η σ hσ k (n - (k + 1))


/-- The directed error at the origin is a sum over rounds of the finite-site routing
discrepancy, the departure stacks being truncated at the box of radius `n + 1`. -/
theorem wErrOriented_eq_finiteRoute (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (hσ : ∀ q : Site d × ℕ, ∃ i : Fin d, σ q = q.1 + unit i) (n : ℕ) :
    wErrOriented η σ n 0 = ∑ k ∈ Finset.range n,
      orientedFiniteRoute (boxFinset 0 (n + 1)) (fun _ => k) (fun _ => n - (k + 1)) (η, σ) := by
  rw [wErrOriented_eq_routeSum η σ hσ n]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [orientedFiniteRoute]
  refine tsum_eq_sum (s := boxFinset 0 (n + 1)) fun y hy => ?_
  refine Finset.sum_eq_zero fun j _ => ?_
  obtain ⟨i₀, hi₀⟩ := hσ (y, j)
  rw [hi₀, orientedRouteDisc]
  have hz : orientedLayer d (n - (k + 1)) (y + unit i₀) = 0 := by
    by_contra hne
    have h1 : y + unit i₀ ∈ boxFinset (0 : Site d) (n - (k + 1)) := orientedLayer_mem_box hne
    have h2 : y ∈ boxFinset (y + unit i₀) 1 := by
      rw [mem_boxFinset_iff]
      intro i
      simp only [Pi.add_apply, unit, Pi.single_apply]
      split <;> norm_num
    have h3 : y ∈ boxFinset (0 : Site d) ((n - (k + 1)) + 1) := mem_boxFinset_add h1 h2
    exact hy (boxFinset_mono (y := (0 : Site d)) (show (n - (k + 1)) + 1 ≤ n + 1 by omega) h3)
  have hy0 : orientedLayer d (n - (k + 1) + 1) y = 0 := by
    by_contra hne
    have hmem : y ∈ boxFinset (0 : Site d) (n - (k + 1) + 1) := orientedLayer_mem_box hne
    exact hy (boxFinset_mono (y := (0 : Site d)) (show n - (k + 1) + 1 ≤ n + 1 by omega) hmem)
  rw [hz, hy0, sub_zero]

end Parking
end
