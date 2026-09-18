/- First-moment control of a scenery pairing with a uniformly small coefficient. -/
import Parking.Support.SpatWSceneryFdd
import Parking.Support.SpatWMartingaleVariance

open MeasureTheory Filter Topology
noncomputable section
namespace Parking
variable {d : ℕ}

/-- A coefficient supported in a fixed box has an integrable scenery pairing.
The bound is explicit in its uniform size and needs only the first absolute moment. -/
theorem integral_abs_scenePair_le (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {φ : (Fin d → ℝ) → ℝ} {B ε R : ℝ} (hB : 0 < B) (hε : 0 ≤ ε) (hR : 1 ≤ R)
    (hsupp : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B) (hbound : ∀ x, |φ x| ≤ ε) :
    Integrable (fun w => scenePair w R φ) (law d ν) ∧
      (∫ w, |scenePair w R φ| ∂law d ν) ≤
        (2 * B + 5) ^ d * (∫ k : ℤ, |(k : ℝ)| ∂ν) * ε * R ^ ((d : ℝ) / 2) := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have hpow : 0 ≤ R ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hRpos.le _
  let S := sceneryBox d B R
  have hi : ∀ y : Site d, Integrable (fun w : Data d => |confReal w y|) (law d ν) := by
    intro y
    have hm := law_map_conf_eval hd ν y
    have hh : Integrable (fun k : ℤ => |(k : ℝ)|)
        ((law d ν).map (fun w : Data d => w.1 y)) := by rwa [hm]
    exact hh.comp_aemeasurable (((measurable_pi_apply y).comp measurable_fst).aemeasurable)
  have he : ∀ y : Site d, (∫ w : Data d, |confReal w y| ∂law d ν) =
      ∫ k : ℤ, |(k : ℝ)| ∂ν := by
    intro y
    have hm := integral_map (μ := law d ν) (φ := fun w : Data d => w.1 y)
      (((measurable_pi_apply y).comp measurable_fst).aemeasurable)
      (measurable_intCastReal.abs.aestronglyMeasurable)
    rw [law_map_conf_eval hd ν y] at hm
    exact hm.symm
  have hscene : (fun w => scenePair w R φ) =
      fun w => ∑ y ∈ S, R ^ (-(d : ℝ) / 2) * (confReal w y * φ (fun j => (y j : ℝ) / R)) :=
    funext fun w => scenePair_eq_sceneryBox_sum hB hsupp hR w
  have hsi : Integrable (fun w => scenePair w R φ) (law d ν) := by
    rw [hscene]
    exact integrable_finsetSum _ fun y _ => ((integrable_norm_iff ((measurable_pi_apply y).comp measurable_confReal).aestronglyMeasurable).mp (hi y) |>.mul_const _).const_mul _
  refine ⟨hsi, ?_⟩
  have hupper : ∀ w : Data d, |scenePair w R φ| ≤
      ∑ y ∈ S, R ^ (-(d : ℝ) / 2) * (|confReal w y| * ε) := by
    intro w
    rw [congrFun hscene w]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [abs_mul, abs_of_nonneg hpow, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hbound _) (abs_nonneg _)) hpow
  have hsu : Integrable (fun w : Data d =>
      ∑ y ∈ S, R ^ (-(d : ℝ) / 2) * (|confReal w y| * ε)) (law d ν) :=
    integrable_finsetSum _ fun y _ => ((hi y).mul_const ε).const_mul _
  have hintle := integral_mono hsi.abs hsu hupper
  rw [integral_finsetSum _ (fun y _ => ((hi y).mul_const ε).const_mul _)] at hintle
  simp_rw [integral_const_mul, integral_mul_const, he] at hintle
  rw [Finset.sum_const, nsmul_eq_mul] at hintle
  refine hintle.trans ?_
  have hcard : (S.card : ℝ) ≤ (2 * B + 5) ^ d * R ^ d := by
    apply le_trans _ (card_sceneryBox_le (d := d) hB hR)
    exact_mod_cast Finset.card_le_card (LatticeProb.boxFinset_mono
      (y := (0 : Site d)) (Nat.le_succ ⌈B * R⌉₊))
  have hfac : R ^ d * R ^ (-(d : ℝ) / 2) = R ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hRpos]
    congr 1
    ring
  calc
    (S.card : ℝ) * (R ^ (-(d : ℝ) / 2) * ((∫ k : ℤ, |(k : ℝ)| ∂ν) * ε))
      ≤ ((2 * B + 5) ^ d * R ^ d) *
        (R ^ (-(d : ℝ) / 2) * ((∫ k : ℤ, |(k : ℝ)| ∂ν) * ε)) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hpow
        (mul_nonneg (integral_nonneg fun _ => abs_nonneg _) hε))
    _ = _ := by rw [show ((2 * B + 5) ^ d * R ^ d) *
        (R ^ (-(d : ℝ) / 2) * ((∫ k : ℤ, |(k : ℝ)| ∂ν) * ε)) =
        (2 * B + 5) ^ d * (∫ k : ℤ, |(k : ℝ)| ∂ν) * ε *
          (R ^ d * R ^ (-(d : ℝ) / 2)) by ring, hfac]

/-- Uniform errors of order `R⁻²` in a fixed spatial box give vanishing scenery
pairings in `L¹` in dimensions at most three. -/
theorem tendsto_integral_abs_scenePair_of_quadratic_error (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    {φ : ℝ → (Fin d → ℝ) → ℝ} {B C : ℝ} (hB : 0 < B) (hC : 0 ≤ C)
    (hsupp : ∀ᶠ R : ℝ in atTop, ∀ x, φ R x ≠ 0 → ‖x‖ ≤ B)
    (hbound : ∀ᶠ R : ℝ in atTop, ∀ x, |φ R x| ≤ C / R ^ 2) :
    Tendsto (fun R : ℝ => ∫ w, |scenePair w R (φ R)| ∂law d ν) atTop (𝓝 0) := by
  let A := (2 * B + 5) ^ d * (∫ k : ℤ, |(k : ℝ)| ∂ν) * C
  have hneg : 0 < 2 - (d : ℝ) / 2 := by
    have hd' : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
    linarith
  have hlim : Tendsto (fun R : ℝ => A * R ^ ((d : ℝ) / 2 - 2)) atTop (𝓝 0) := by
    simpa only [neg_sub, mul_zero] using (tendsto_rpow_neg_atTop hneg).const_mul A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Eventually.of_forall fun R => integral_nonneg fun _ => abs_nonneg _
  filter_upwards [hsupp, hbound, eventually_ge_atTop (1 : ℝ)] with R hs hb hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have h := (integral_abs_scenePair_le hd ν hint hB (div_nonneg hC (sq_nonneg R))
    hR hs hb).2
  have heq : (2 * B + 5) ^ d * (∫ k : ℤ, |(k : ℝ)| ∂ν) * (C / R ^ 2) *
      R ^ ((d : ℝ) / 2) = A * R ^ ((d : ℝ) / 2 - 2) := by
    rw [Real.rpow_sub hRpos, Real.rpow_two]
    dsimp [A]
    ring
  exact h.trans_eq heq

end Parking
