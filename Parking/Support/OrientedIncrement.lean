/- One-quarter time increments of the directed potential under the joint law. -/
import Parking.Support.OrientedSceneryMoment
import Parking.Support.OrientedCountLoad
import Parking.Support.NonnegativeProduct
import Parking.Support.Measurability

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset

/-- The linear potential evaluated along an independent directed walk. -/
def orientedPotentialAlong {d : ℕ} (n j : ℕ)
    (ω : (ℕ → Fin d × Bool) × (Site d → ℝ)) : ℝ :=
  orientedPotential ω.2 (n - j) (orientedPath 0 ω.1 j)

theorem measurable_orientedPath {d : ℕ} (x : Site d) (j : ℕ) :
    Measurable fun p : ℕ → Fin d × Bool => orientedPath x p j := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    exact ih.sub ((measurable_from_countable' (fun b : Fin d × Bool => unit b.1)).comp
      (measurable_pi_apply j))

theorem measurable_orientedPotentialAlong {d : ℕ} (n j : ℕ) :
    Measurable (orientedPotentialAlong (d := d) n j) :=
  measurable_eval_var (fun ω : (ℕ → Fin d × Bool) × (Site d → ℝ) => orientedPath 0 ω.1 j)
    ((measurable_orientedPath 0 j).comp measurable_fst)
    (fun ω x => orientedPotential ω.2 (n - j) x)
    (fun x => (measurable_orientedPotential (n - j) x).comp measurable_snd)

/-- The potential has one-quarter time increments in every available
`L^r`, `r>4`, under the joint scenery and walk law. -/
theorem exists_oriented_potential_increment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (r : ℝ) (hr : 4 < r) (hmom : Integrable (fun z : ℝ => |z| ^ r) μ)
    (hmean : ∫ z : ℝ, z ∂μ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ n j k : ℕ, j ≤ k → k ≤ n →
      Integrable (fun ω : (ℕ → Fin 2 × Bool) × (Site 2 → ℝ) =>
        |orientedPotentialAlong n j ω - orientedPotentialAlong n k ω| ^ r)
        ((walkLaw 2).prod (iidLaw 2 μ)) ∧
      (∫ ω : (ℕ → Fin 2 × Bool) × (Site 2 → ℝ),
        |orientedPotentialAlong n j ω - orientedPotentialAlong n k ω| ^ r
          ∂((walkLaw 2).prod (iidLaw 2 μ))) ^ (1 / r) ≤ C * ((k - j : ℕ) : ℝ) ^ ((1 : ℝ) / 4) := by
  have hr0 : 0 < r := by linarith
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  haveI : IsProbabilityMeasure (iidLaw 2 μ) := by unfold iidLaw; infer_instance
  obtain ⟨A, hA, hsc⟩ := exists_oriented_potential_scenery_bound μ r (by linarith) hmom hmean
  obtain ⟨B, hB, hwc⟩ := exists_orientedCount_load_moment (r / 2) (by linarith)
  let K := A ^ (r / 2) * B
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K ^ (1 / r), Real.rpow_pos_of_pos hK _, fun n j k hjk hkn => ?_⟩
  let h := k - j
  let N := n - k
  let D : (ℕ → Fin 2 × Bool) → ℤ := fun p => orientedFirstCount p j h
  let W : (ℕ → Fin 2 × Bool) → ℝ := fun p => Real.sqrt h + |(D p : ℝ) - (h : ℝ) / 2|
  let F : (ℕ → Fin 2 × Bool) × (Site 2 → ℝ) → ℝ :=
    fun ω => orientedPotentialAlong n j ω - orientedPotentialAlong n k ω
  have hm : Measurable F := (measurable_orientedPotentialAlong n j).sub (measurable_orientedPotentialAlong n k)
  have hh : j + h = k := Nat.add_sub_of_le hjk
  have hN : N + h = n - j := by dsimp only [N, h]; omega
  have hx (p : ℕ → Fin 2 × Bool) : orientedPath 0 p k =
      orientedPath 0 p j + orientedLayerPoint h (D p) := by
    have he := orientedPath_interval p j h 0
    rwa [hh] at he
  have he (p : ℕ → Fin 2 × Bool) (η : Site 2 → ℝ) : F (p, η) =
      orientedPotential η (N + h) (orientedPath 0 p j) -
        orientedPotential η N (orientedPath 0 p j + orientedLayerPoint h (D p)) := by
    change orientedPotential η (n - j) (orientedPath 0 p j) -
      orientedPotential η (n - k) (orientedPath 0 p k) = _
    rw [hN, ← hx]
  have hsec (p : ℕ → Fin 2 × Bool) :
      Integrable (fun η => |F (p, η)| ^ r) (iidLaw 2 μ) ∧
        (∫ η, |F (p, η)| ^ r ∂(iidLaw 2 μ)) ^ (2 / r) ≤ A * W p := by
    have hs := hsc N h (D p) (orientedPath 0 p j)
    simpa only [← he p] using hs
  have hW : ∀ p, 0 ≤ W p := fun p => add_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hload : Integrable (fun p => W p ^ (r / 2)) (walkLaw 2) ∧
      (∫ p, W p ^ (r / 2) ∂(walkLaw 2)) ≤ B * (h : ℝ) ^ (r / 4) := by
    have hb := hwc j h
    have heq : (r / 2) / 2 = r / 4 := by ring
    simpa only [W, D, Int.cast_natCast, heq] using hb
  have hpB (p : ℕ → Fin 2 × Bool) :
      (∫ η, |F (p, η)| ^ r ∂(iidLaw 2 μ)) ≤ A ^ (r / 2) * W p ^ (r / 2) := by
    have hI := le_rpow_of_rpow_two_div_le
      (integral_nonneg fun η => Real.rpow_nonneg (abs_nonneg _) r) hr0 (hsec p).2
    rwa [Real.mul_rpow hA.le (hW p)] at hI
  obtain ⟨hprod, hprodB⟩ := integral_prod_le_of_sections (walkLaw 2) (iidLaw 2 μ)
    (fun ω => |F ω| ^ r) (hm.abs.pow_const r) (fun ω => Real.rpow_nonneg (abs_nonneg _) r)
    (fun p => (hsec p).1) (fun p => A ^ (r / 2) * W p ^ (r / 2))
    (hload.1.const_mul _) hpB
  rw [integral_const_mul] at hprodB
  have hraw : (∫ ω, |F ω| ^ r ∂((walkLaw 2).prod (iidLaw 2 μ))) ≤ K * (h : ℝ) ^ (r / 4) := by
    have hb := mul_le_mul_of_nonneg_left hload.2 (Real.rpow_nonneg hA.le (r / 2))
    exact hprodB.trans (by simpa only [K, mul_assoc] using hb)
  have hroot := Real.rpow_le_rpow (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) r)
    hraw (by positivity : (0 : ℝ) ≤ 1 / r)
  rw [Real.mul_rpow hK.le (Real.rpow_nonneg (Nat.cast_nonneg h) _),
    ← Real.rpow_mul (Nat.cast_nonneg h),
    show (r / 4) * (1 / r) = (1 : ℝ) / 4 by field_simp] at hroot
  exact ⟨hprod, hroot⟩

end Parking
