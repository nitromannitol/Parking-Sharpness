import Parking.Support.RoundHoleSection
import Parking.Support.HoleLocality
import Parking.Support.ProductFactor
import Parking.Support.RoundBlock

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Summing over queried entries first sums over sites and then ranks. -/
theorem sum_roundQuerySet (u : Site d) (R N : ℕ) (f : RoundSlot d → ℝ) :
    ∑ q ∈ roundQuerySet u R N, f q =
      ∑ y ∈ boxFinset u R, ∑ j ∈ Finset.range N, f (Sum.inl (y, j)) := by
  classical
  unfold roundQuerySet
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro y _
    exact Finset.sum_image fun i _ j _ hij => congrArg Prod.snd (Sum.inl_injective hij)
  · intro y _ z _ hyz
    apply Finset.disjoint_left.mpr
    rintro q hq hq'
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hq
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hq'
    exact hyz (congrArg Prod.fst (Sum.inl_injective (hi.trans hj.symm)))

/-- Each departing rank contributes exactly its site's two-target weight. -/
theorem sum_roundHoleCost_query (A : Site d → ℕ) (x z u : Site d) (R N : ℕ)
    (hA : ∀ y ∈ boxFinset u R, A y ≤ N) :
    ∑ q ∈ roundQuerySet u R N, roundHoleCost d A x z q =
      (∑ y ∈ boxFinset u R, holeKernel d x z y * (A y : ℝ)) / (1 / (2 * escapeConst d)) ^ 2 := by
  classical
  rw [sum_roundQuerySet, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y hy
  simp only [roundHoleCost]
  rw [← Finset.sum_filter]
  have he : (Finset.range N).filter (fun j => j < A y) = Finset.range (A y) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    have h := hA y hy
    omega
  rw [he]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- The factors from a complete round are charged to the particles departing during that round. -/
theorem round_hole_product_factor (hd : 3 ≤ d) (A H : Site d → ℕ)
    (N : ℕ) (hA : ∀ y, A y ≤ N) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x z u : Site d)
    (R : ℕ) (hxR : boxFinset x (T + 1) ⊆ boxFinset u R)
    (hzR : boxFinset z (T + 1) ⊆ boxFinset u R) :
    (∫ τ, matchedMeanH (roundSigned A H τ) ρ T x * matchedMeanH (roundSigned A H τ) ρ T z
      ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d)) ≤
      Real.exp ((∑ y ∈ boxFinset u R, holeKernel d x z y * (A y : ℝ)) / (1 / (2 * escapeConst d)) ^ 2) *
        ((∫ τ, matchedMeanH (roundSigned A H τ) ρ T x ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d)) *
          ∫ τ, matchedMeanH (roundSigned A H τ) ρ T z ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  haveI := stepLaw_isProbability hd1
  have hm (v : Site d) : Measurable (fun ζ : RoundSlot d → Fin d × Bool => matchedMeanH (roundSigned A H ζ) ρ T v) :=
    (measurable_matchedMeanH hd1 ρ T v).comp
      (measurable_roundSigned (fun _ => A) (fun _ => H) id measurable_const measurable_const measurable_id)
  have hdep (v : Site d) (hv : boxFinset v (T + 1) ⊆ boxFinset u R)
      (τ τ' : RoundSlot d → Fin d × Bool)
      (he : ∀ q ∈ roundQuerySet u R N, τ q = τ' q) :
      matchedMeanH (roundSigned A H τ) ρ T v = matchedMeanH (roundSigned A H τ') ρ T v := by
    apply roundMeanH_agree_finite A H N hA ρ T v τ τ'
    intro y hy j hj
    exact he _ ((mem_roundQuerySet u R N y j).mpr ⟨hv hy, hj⟩)
  have h := integral_product_factor (fun _ : RoundSlot d => stepLaw d)
    (fun τ => matchedMeanH (roundSigned A H τ) ρ T x) (fun τ => matchedMeanH (roundSigned A H τ) ρ T z)
    (hm x) (hm z) (H x : ℝ) (H z : ℝ) (Nat.cast_nonneg _)
    (roundMeanH_bound hd1 A H ρ T x) (roundMeanH_bound hd1 A H ρ T z)
    (roundHoleCost d A x z) (fun S q hq τ => round_hole_reveal_section hd A H ρ T x z S q hq τ)
    (roundQuerySet u R N) (hdep x hxR) (hdep z hzR)
  rw [sum_roundHoleCost_query A x z u R N (fun y _ => hA y)] at h
  exact h
end Parking
