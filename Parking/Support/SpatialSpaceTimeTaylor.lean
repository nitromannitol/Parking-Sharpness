/- Uniform consistency of the lattice generator on space-time test functions. -/
import Parking.Support.SpatWWalkTaylor
import Parking.Support.SpaceTimeContOp

open Set Filter Topology LatticeProb
open Parking.Generic.SpaceTimeDerivatives
noncomputable section
namespace Parking
variable {d : ℕ}

/-- The second spatial derivatives are uniformly continuous jointly in space and time. -/
theorem uniformContinuous_spaceTime_lapTerm {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : IsSpaceTimeTest ψ) (i : Fin d) :
    UniformContinuous (fun p : ℝ × (Fin d → ℝ) => lapTerm (fun x => ψ (p.1, x)) i p.2) := by
  have heq : (fun p : ℝ × (Fin d → ℝ) => lapTerm (fun x => ψ (p.1, x)) i p.2) =
      spaceDeriv (spaceDeriv ψ i) i :=
    funext fun p => second_deriv_spaceSlice hψ.1 p i
  rw [heq]
  have hc : HasCompactSupport (spaceDeriv (spaceDeriv ψ i) i) :=
    (hψ.2.1.fderiv_apply ℝ (0, Pi.single i 1)).fderiv_apply ℝ (0, Pi.single i 1)
  exact hc.uniformContinuous_of_continuous
    (contDiff_spaceDeriv (contDiff_spaceDeriv hψ.1 i) i).continuous

theorem exists_spaceTime_lapTerm_update_modulus {ψ : ℝ × (Fin d → ℝ) → ℝ}
    (hψ : IsSpaceTimeTest ψ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (s : ℝ) (z : Fin d → ℝ) (i : Fin d) (t : ℝ),
      |t - z i| < δ →
      |lapTerm (fun x => ψ (s, x)) i (Function.update z i t) -
        lapTerm (fun x => ψ (s, x)) i z| < ε := by
  have huc : UniformContinuous (fun p : ℝ × (Fin d → ℝ) =>
      fun i : Fin d => lapTerm (fun x => ψ (p.1, x)) i p.2) :=
    uniformContinuous_pi.mpr (uniformContinuous_spaceTime_lapTerm hψ)
  obtain ⟨δ, hδ, hm⟩ := Metric.uniformContinuous_iff.mp huc ε hε
  refine ⟨δ, hδ, fun s z i t ht => ?_⟩
  have hdist : dist (Function.update z i t) z ≤ |t - z i| := by
    apply (dist_pi_le_iff (abs_nonneg _)).mpr
    intro j
    by_cases hji : j = i
    · subst j
      simp [Real.dist_eq]
    · simp [Function.update_of_ne hji, abs_nonneg]
  have hpair : dist (s, Function.update z i t) (s, z) < δ := by
    simpa [Prod.dist_eq] using hdist.trans_lt ht
  exact (dist_le_pi_dist _ _ i).trans_lt (hm hpair)

/-- One mesh size controls the spatial consistency error at all times and sites. -/
theorem exists_spaceTime_walkOp_taylor_modulus (hd : 1 ≤ d)
    {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (R : ℝ), 0 < R → 1 / R < δ → ∀ (s : ℝ) (y : Site d),
      |R ^ 2 * (walkOp (fun z => ψ (s, fun j => (z j : ℝ) / R)) y -
        ψ (s, fun j => (y j : ℝ) / R)) -
        contOp d (fun x => ψ (s, x)) (fun j => (y j : ℝ) / R)| ≤ ε := by
  obtain ⟨δ, hδ, hm⟩ := exists_spaceTime_lapTerm_update_modulus hψ hε
  refine ⟨δ, hδ, fun R hR hmesh s y => ?_⟩
  have hs : ContDiff ℝ (2 : ℕ) (fun x => ψ (s, x)) :=
    (hψ.1.comp (contDiff_const.prodMk contDiff_id)).of_le (by norm_cast)
  obtain ⟨a, b, ha, hb, heq⟩ := exists_walkOp_taylor hd hs y hR
  let z : Fin d → ℝ := fun j => (y j : ℝ) / R
  let A : Fin d → ℝ := fun i => lapTerm (fun x => ψ (s, x)) i (Function.update z i (a i)) -
    lapTerm (fun x => ψ (s, x)) i z
  let B : Fin d → ℝ := fun i => lapTerm (fun x => ψ (s, x)) i (Function.update z i (b i)) -
    lapTerm (fun x => ψ (s, x)) i z
  have hA : ∀ i, |A i| ≤ ε := by
    intro i
    apply le_of_lt (hm s z i (a i) ?_)
    rw [abs_of_pos (sub_pos.mpr (ha i).1)]
    exact lt_trans (by linarith [(ha i).2]) hmesh
  have hB : ∀ i, |B i| ≤ ε := by
    intro i
    apply le_of_lt (hm s z i (b i) ?_)
    rw [abs_of_neg (sub_neg.mpr (hb i).2)]
    exact lt_trans (by linarith [(hb i).1]) hmesh
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hden : (0 : ℝ) < 4 * d := by positivity
  have herr : R ^ 2 * (walkOp (fun q => ψ (s, fun j => (q j : ℝ) / R)) y - ψ (s, z)) -
      contOp d (fun x => ψ (s, x)) z = (∑ i, (A i + B i)) / (4 * d) := by
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

theorem eventually_spaceTime_walkOp_taylor_error_le (hd : 1 ≤ d)
    {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ (s : ℝ) (y : Site d),
      |R ^ 2 * (walkOp (fun z => ψ (s, fun j => (z j : ℝ) / R)) y -
        ψ (s, fun j => (y j : ℝ) / R)) -
        contOp d (fun x => ψ (s, x)) (fun j => (y j : ℝ) / R)| ≤ ε := by
  obtain ⟨δ, hδ, hm⟩ := exists_spaceTime_walkOp_taylor_modulus hd hψ hε
  have ht : Tendsto (fun R : ℝ => 1 / R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  filter_upwards [eventually_gt_atTop (0 : ℝ), (tendsto_order.mp ht).2 δ hδ] with R hR hmesh
  exact hm R hR hmesh

end Parking
