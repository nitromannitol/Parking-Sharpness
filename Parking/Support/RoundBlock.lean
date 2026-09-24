import Parking.Support.RoundMeanField
import Parking.Support.ProductDoob
import Parking.Support.ProductTower

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- The finite set of potential current-round entries relevant to a future mean. -/
def roundQuerySet (x : Site d) (R N : ℕ) : Finset (RoundSlot d) :=
  (boxFinset x R).biUnion fun y => (Finset.range N).image fun j => Sum.inl (y, j)

theorem mem_roundQuerySet (x : Site d) (R N : ℕ) (v : Site d) (j : ℕ) :
    Sum.inl (v, j) ∈ roundQuerySet x R N ↔ v ∈ boxFinset x R ∧ j < N := by
  classical
  simp only [roundQuerySet, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨y, hy, k, hk, he⟩
    cases Sum.inl_injective he
    exact ⟨hy, hk⟩
  · rintro ⟨hv, hj⟩
    exact ⟨v, hv, j, hj, rfl⟩

/-- Once the finite query set is revealed, the future mean is known exactly. -/
theorem partialInt_roundMeanU_query (hd : 1 ≤ d) (A H : Site d → ℕ)
    (N : ℕ) (hA : ∀ y, A y ≤ N) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d)
    (R : ℕ) (hR : T + 1 ≤ R) (τ : RoundSlot d → Fin d × Bool) :
    partialInt (fun _ : RoundSlot d => stepLaw d) (roundQuerySet x R N : Set (RoundSlot d))
      (fun ζ => matchedMeanU (roundSigned A H ζ) ρ T x) τ = matchedMeanU (roundSigned A H τ) ρ T x := by
  classical
  haveI := stepLaw_isProbability hd
  apply partialInt_eq_self
  intro ζ ζ' he
  apply roundMeanU_agree_finite A H N hA ρ T x ζ ζ'
  intro y hy j hj
  exact he (Sum.inl (y, j)) ((mem_roundQuerySet x R N y j).mpr ⟨boxFinset_mono hR hy, hj⟩)

/-- Before any current-round entry is revealed, its partial mean is the full round average. -/
theorem partialInt_empty_roundMeanU (A H : Site d → ℕ) (ρ : Label d × ℕ → ℝ)
    (T : ℕ) (x : Site d) (τ : RoundSlot d → Fin d × Bool) :
    partialInt (fun _ : RoundSlot d => stepLaw d) ∅
      (fun ζ => matchedMeanU (roundSigned A H ζ) ρ T x) τ =
      ∫ ζ, matchedMeanU (roundSigned A H ζ) ρ T x
        ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d) := by
  rfl
end Parking
