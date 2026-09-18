/-
Finite dependence, perturbation bounds and convex comparison for sandpile odometers.
-/
import Parking.Support.ConvexProduct
import LatticeProb.Prob.FiniteMarginal

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
open scoped NNReal
variable {d : ℕ}

/-- A uniform bound on the field bounds the sandpile odometer. -/
theorem u_le_mul_of_le (hd : 1 ≤ d) {η : Site d → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hη : ∀ x, η x ≤ B) (n : ℕ) (x : Site d) : u η n x ≤ n * B := by
  induction n generalizing x with
  | zero => simp [u]
  | succ n ih =>
      change max 0 (η x + walkOp (u η n) x) ≤ (n + 1 : ℕ) * B
      have hw := walkOp_mono hd ih x
      rw [walkOp_const hd] at hw
      apply max_le
      · positivity
      · push_cast
        nlinarith only [hw, hη x]

/-- Subadditivity of the sandpile odometer. -/
theorem u_add_le (hd : 1 ≤ d) (η ξ : Site d → ℝ) (n : ℕ) (x : Site d) :
    u (η + ξ) n x ≤ u η n x + u ξ n x := by
  change u (fun y => η y + ξ y) n x ≤ u η n x + u ξ n x
  simpa only [one_mul] using u_positive_combination_le hd η ξ
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) n x

/-- A uniform field perturbation gives a linear-in-time odometer perturbation. -/
theorem abs_u_sub_le (hd : 1 ≤ d) {η ξ : Site d → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hη : ∀ x, |η x - ξ x| ≤ B) (n : ℕ) (x : Site d) :
    |u η n x - u ξ n x| ≤ n * B := by
  have hp : ∀ y, (η - ξ) y ≤ B := fun y => (le_abs_self _).trans (hη y)
  have hn : ∀ y, (ξ - η) y ≤ B := by
    intro y
    change ξ y - η y ≤ B
    have := (abs_le.mp (hη y)).1
    linarith
  have hp' := u_le_mul_of_le hd hB hp n x
  have hn' := u_le_mul_of_le hd hB hn n x
  have h1 := u_add_le hd (η - ξ) ξ n x
  have h2 := u_add_le hd (ξ - η) η n x
  rw [sub_add_cancel] at h1 h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The odometer reads only the time-radius box. -/
theorem u_eq_of_eqOn_box {η ξ : Site d → ℝ} (n : ℕ) (x : Site d)
    (heq : ∀ y ∈ boxFinset x n, η y = ξ y) : u η n x = u ξ n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have hx : x ∈ boxFinset x (n + 1) := mem_boxFinset_iff.mpr (fun i => by simp; positivity)
      have hnbr : ∀ y ∈ nbrFinset x, u η n y = u ξ n y := by
        intro y hy
        apply ih y
        intro z hz
        apply heq z
        have h := mem_boxFinset_add (nbrFinset_subset_box x hy) hz
        simpa only [Nat.add_comm 1 n] using h
      have hw : walkOp (u η n) x = walkOp (u ξ n) x := by
        unfold walkOp nbrSum
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [hnbr _ (mem_nbrFinset_add x i), hnbr _ (mem_nbrFinset_sub x i)]
      change max 0 (η x + walkOp (u η n) x) = max 0 (ξ x + walkOp (u ξ n) x)
      rw [heq x hx, hw]
end Parking

namespace Parking
open MeasureTheory LatticeProb
open scoped NNReal
variable {d : ℕ}

/-- Extend a field on a finite set by zero. -/
def extendField (s : Finset (Site d)) (η : s → ℝ) (x : Site d) : ℝ :=
  if hx : x ∈ s then η ⟨x, hx⟩ else 0

theorem extendField_restrict (s : Finset (Site d)) (η : Site d → ℝ)
    {x : Site d} (hx : x ∈ s) : extendField s (s.restrict η) x = η x := by
  simp [extendField, hx, Finset.restrict]

/-- Restriction to the time-radius box preserves the odometer. -/
theorem u_extendField_restrict (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    u (extendField (boxFinset x n) ((boxFinset x n).restrict η)) n x = u η n x :=
  u_eq_of_eqOn_box n x (fun _ hy => extendField_restrict _ _ hy)

/-- A finite-field odometer is Lipschitz with constant equal to the horizon. -/
theorem lipschitzWith_u_extendField (hd : 1 ≤ d) (s : Finset (Site d)) (n : ℕ) (x : Site d) :
    LipschitzWith (n : ℝ≥0) (fun η : s → ℝ => u (extendField s η) n x) := by
  apply LipschitzWith.of_dist_le_mul
  intro η ξ
  simp only [Real.dist_eq, NNReal.coe_natCast]
  apply abs_u_sub_le hd dist_nonneg
  intro y
  by_cases hy : y ∈ s
  · simp only [extendField, dif_pos hy]
    exact dist_le_pi_dist η ξ ⟨y, hy⟩
  · simp [extendField, hy]

/-- A finite-field odometer is convex. -/
theorem convexOn_u_extendField (hd : 1 ≤ d) (s : Finset (Site d)) (n : ℕ) (x : Site d) :
    ConvexOn ℝ Set.univ (fun η : s → ℝ => u (extendField s η) n x) := by
  refine ⟨convex_univ, fun η _ ξ _ a b ha hb hab => ?_⟩
  have heq : extendField s (a • η + b • ξ) =
      a • extendField s η + b • extendField s ξ := by
    funext y
    by_cases hy : y ∈ s <;> simp [extendField, hy]
  change u (extendField s (a • η + b • ξ)) n x ≤
    a • u (extendField s η) n x + b • u (extendField s ξ) n x
  rw [heq]
  exact (convexOn_u hd n x).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

/-- The expected odometer can be integrated over its finite set of input sites. -/
theorem integral_u_iid_eq_pi (hd : 1 ≤ d) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (x : Site d) :
    ∫ η, u η n x ∂(iidLaw d μ) =
      ∫ η : (boxFinset x n) → ℝ, u (extendField (boxFinset x n) η) n x
        ∂(Measure.pi (fun _ => μ)) := by
  have hm : Measurable ((boxFinset x n).restrict : (Site d → ℝ) → ((boxFinset x n) → ℝ)) :=
    measurable_pi_lambda _ fun y => measurable_pi_apply (y : Site d)
  have hF := (lipschitzWith_u_extendField hd (boxFinset x n) n x).continuous.measurable
  rw [← iidLaw_map_restrict d μ (boxFinset x n), integral_map hm.aemeasurable hF.aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ fun η => (u_extendField_restrict η n x).symm)

/-- First moments of the input field suffice for odometer integrability. -/
theorem integrable_u_iid (hd : 1 ≤ d) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (id : ℝ → ℝ) μ) (n : ℕ) (x : Site d) :
    Integrable (fun η => u η n x) (iidLaw d μ) := by
  have hm : Measurable ((boxFinset x n).restrict : (Site d → ℝ) → ((boxFinset x n) → ℝ)) :=
    measurable_pi_lambda _ fun y => measurable_pi_apply (y : Site d)
  have hp : MeasurePreserving (boxFinset x n).restrict (iidLaw d μ)
      (Measure.pi (fun _ : boxFinset x n => μ)) := ⟨hm, iidLaw_map_restrict d μ _⟩
  have hi := integrable_real_lipschitz (lipschitzWith_u_extendField hd (boxFinset x n) n x)
    (integrable_id_pi (fun _ => μ) (fun _ => hμ))
  refine (hp.integrable_comp_of_integrable hi).congr ?_
  exact ae_of_all _ fun η => u_extendField_restrict η n x

/-- One-site convex comparison bounds the expected sandpile odometer. -/
theorem integral_u_iid_le (hd : 1 ≤ d) {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (id : ℝ → ℝ) μ) (hν : Integrable (id : ℝ → ℝ) ν)
    (hcomp : ∀ (f : ℝ → ℝ) (K : ℝ≥0), ConvexOn ℝ Set.univ f → LipschitzWith K f →
      ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν) (n : ℕ) (x : Site d) :
    ∫ η, u η n x ∂(iidLaw d μ) ≤ ∫ η, u η n x ∂(iidLaw d ν) := by
  rw [integral_u_iid_eq_pi hd μ, integral_u_iid_eq_pi hd ν]
  exact convex_lipschitz_integral_le_finite_pi hμ hν hcomp
    (convexOn_u_extendField hd _ n x) (lipschitzWith_u_extendField hd _ n x)
end Parking
