/- Uniform approximation of the continuum Laplacian by the rescaled lattice walk generator. -/
import Parking.Support.SpatWTaylorLap
import Parking.Generic.LatticeTaylor

open Set Filter Topology LatticeProb Parking.Generic.LatticeTaylor
noncomputable section
namespace Parking
variable {d : ℕ}

/-- Taylor expansion of all lattice directions, with explicit intermediate points. -/
theorem exists_walkOp_taylor (hd : 1 ≤ d) {φ : (Fin d → ℝ) → ℝ}
    (hφ : ContDiff ℝ (2 : ℕ) φ) (y : Site d) {R : ℝ} (hR : 0 < R) :
    ∃ a b : Fin d → ℝ,
      (∀ i, a i ∈ Ioo ((y i : ℝ) / R) ((y i : ℝ) / R + 1 / R)) ∧
      (∀ i, b i ∈ Ioo ((y i : ℝ) / R - 1 / R) ((y i : ℝ) / R)) ∧
      R ^ 2 * (walkOp (fun z => φ (fun j => (z j : ℝ) / R)) y -
        φ (fun j => (y j : ℝ) / R)) =
      (∑ i : Fin d, (lapTerm φ i (Function.update (fun j => (y j : ℝ) / R) i (a i)) +
        lapTerm φ i (Function.update (fun j => (y j : ℝ) / R) i (b i)))) / (4 * d) := by
  have ht := fun i : Fin d => exists_symm_second_diff_lapTerm hφ
    (fun j => (y j : ℝ) / R) i (one_div_pos.mpr hR)
  choose a ha b hb heq using ht
  refine ⟨a, b, ha, hb, ?_⟩
  rw [walkOp_sub_eq_sum hd]
  have hterm : ∀ i : Fin d,
      φ (fun j => ((y + unit i) j : ℝ) / R) +
        φ (fun j => ((y - unit i) j : ℝ) / R) - 2 * φ (fun j => (y j : ℝ) / R) =
      (1 / R) ^ 2 / 2 * (lapTerm φ i (Function.update (fun j => (y j : ℝ) / R) i (a i)) +
        lapTerm φ i (Function.update (fun j => (y j : ℝ) / R) i (b i))) := by
    intro i
    rw [rescale_add_unit, rescale_sub_unit]
    exact heq i
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  field_simp
  ring


/-- Compact support makes each second partial derivative uniformly continuous globally. -/
theorem uniformContinuous_lapTerm {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) (i : Fin d) :
    UniformContinuous (lapTerm φ i) := by
  have heq : lapTerm φ i = partialDeriv (partialDeriv φ i) i :=
    funext (lapTerm_eq_partialDeriv hφ.1 i)
  rw [heq]
  exact (hasCompactSupport_partialDeriv (hasCompactSupport_partialDeriv hφ.2 i) i).uniformContinuous_of_continuous
      (contDiff_partialDeriv (contDiff_partialDeriv hφ.1 i) i).continuous

/-- A single modulus controls coordinate perturbations in every direction. -/
theorem exists_lapTerm_update_modulus {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (z : Fin d → ℝ) (i : Fin d) (t : ℝ),
      |t - z i| < δ → |lapTerm φ i (Function.update z i t) - lapTerm φ i z| < ε := by
  have huc : UniformContinuous (fun z => fun i : Fin d => lapTerm φ i z) :=
    uniformContinuous_pi.mpr (uniformContinuous_lapTerm hφ)
  obtain ⟨δ, hδ, hm⟩ := Metric.uniformContinuous_iff.mp huc ε hε
  refine ⟨δ, hδ, fun z i t ht => ?_⟩
  have hdist : dist (Function.update z i t) z ≤ |t - z i| := by
    apply (dist_pi_le_iff (abs_nonneg _)).mpr
    intro j
    by_cases hji : j = i
    · subst j
      simp [Real.dist_eq]
    · simp [Function.update_of_ne hji, abs_nonneg]
  have h := hm (lt_of_le_of_lt hdist ht)
  exact lt_of_le_of_lt (dist_le_pi_dist
    (fun j => lapTerm φ j (Function.update z i t)) (fun j => lapTerm φ j z) i) h

/-- The scaled walk generator approximates the continuum operator uniformly over all sites. -/
theorem exists_walkOp_taylor_modulus (hd : 1 ≤ d) {φ : (Fin d → ℝ) → ℝ}
    (hφ : IsTestFun φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (R : ℝ), 0 < R → 1 / R < δ → ∀ y : Site d,
      |R ^ 2 * (walkOp (fun z => φ (fun j => (z j : ℝ) / R)) y -
        φ (fun j => (y j : ℝ) / R)) - contOp d φ (fun j => (y j : ℝ) / R)| ≤ ε := by
  obtain ⟨δ, hδ, hm⟩ := exists_lapTerm_update_modulus hφ hε
  refine ⟨δ, hδ, fun R hR hmesh y => ?_⟩
  obtain ⟨a, b, ha, hb, heq⟩ := exists_walkOp_taylor hd (hφ.1.of_le (by norm_cast)) y hR
  let z : Fin d → ℝ := fun j => (y j : ℝ) / R
  let A : Fin d → ℝ := fun i => lapTerm φ i (Function.update z i (a i)) - lapTerm φ i z
  let B : Fin d → ℝ := fun i => lapTerm φ i (Function.update z i (b i)) - lapTerm φ i z
  have hA : ∀ i, |A i| ≤ ε := by
    intro i
    apply le_of_lt (hm z i (a i) ?_)
    rw [abs_of_pos (sub_pos.mpr (ha i).1)]
    exact lt_trans (by linarith [(ha i).2]) hmesh
  have hB : ∀ i, |B i| ≤ ε := by
    intro i
    apply le_of_lt (hm z i (b i) ?_)
    rw [abs_of_neg (sub_neg.mpr (hb i).2)]
    exact lt_trans (by linarith [(hb i).1]) hmesh
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hden : (0 : ℝ) < 4 * d := by positivity
  have herr : R ^ 2 * (walkOp (fun q => φ (fun j => (q j : ℝ) / R)) y - φ z) -
      contOp d φ z = (∑ i, (A i + B i)) / (4 * d) := by
    rw [heq]
    dsimp [A, B, contOp]
    rw [lap_eq_sum_lapTerm]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [herr, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  calc
    |∑ i, (A i + B i)| ≤ ∑ i, |A i + B i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, (2 * ε) := Finset.sum_le_sum fun i _ =>
      (abs_add_le (A i) (B i)).trans (by linarith [hA i, hB i])
    _ = (d : ℝ) * (2 * ε) := by simp
    _ ≤ ε * (4 * d) := by nlinarith

/-- The walk-generator approximation error vanishes uniformly as the lattice scale grows. -/
theorem eventually_walkOp_taylor_error_le (hd : 1 ≤ d) {φ : (Fin d → ℝ) → ℝ}
    (hφ : IsTestFun φ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ y : Site d,
      |R ^ 2 * (walkOp (fun z => φ (fun j => (z j : ℝ) / R)) y -
        φ (fun j => (y j : ℝ) / R)) - contOp d φ (fun j => (y j : ℝ) / R)| ≤ ε := by
  obtain ⟨δ, hδ, hm⟩ := exists_walkOp_taylor_modulus hd hφ hε
  have ht : Tendsto (fun R : ℝ => 1 / R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  filter_upwards [eventually_gt_atTop (0 : ℝ), (tendsto_order.mp ht).2 δ hδ] with R hR hmesh
  exact hm R hR hmesh
end Parking
end
