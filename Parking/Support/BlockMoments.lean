/-
Stationarity and the a priori bounds of Step 2 of `lem:mean-horizon`.

Step 2 reads the paper's sentence "the walk is independent of `ξ_δ`, so
stationarity gives `(E u_{ℓ_k}(X_{s_k};ξ_δ)^q)^{1/q} ≤ C_q φ_d(ℓ_k)`".  In Lean
that is `lintegral_prod_u_xi`: averaging the odometer's fifth moment over the
configuration AND the walk gives the same number as averaging it at the origin,
because the i.i.d. law is translation invariant
(`Parking.iidLaw_map_shiftConf`) and the odometer commutes with translation
(`Parking.u_shift`).  It is stated in `ℝ≥0∞` so that no integrability is assumed
before it is proved.

The rest of the file is what Step 2 needs to know about the block terms before
integrating them: that the fifth moment is finite at the recentred scenery
(`integrable_u_xi_pow`, through the convex-comparison law of
`Parking/Support/XiLaw.lean`), and the a priori bound `u_ℓ(y) ≤ ℓ ∑_{box} |ξ|`
of `eq:apriori-finite` read along the walk (`blockTerm_bound`), which is what
makes the block terms integrable in the configuration.
-/
import Parking.Support.JointStopping
import Parking.Support.MeanHorizonStep1
import Parking.Support.Invariance

noncomputable section

namespace Parking

open MeasureTheory LatticeProb
open scoped ENNReal

variable {d : ℕ}

theorem xi_shiftConf (δ : ℝ) (η : Site d → ℤ) (y : Site d) :
    Parking.xi δ (fun x => η (x + y)) = fun z => Parking.xi δ η (z + y) := rfl

/-- **Stationarity.**  The law of the odometer of the recentred scenery does not depend on
where it is read. -/
theorem lintegral_u_xi_shift (hd : 1 ≤ d) (δ : ℝ) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (ℓ : ℕ) (y : Site d) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ η, g (u (Parking.xi δ η) ℓ y) ∂(LatticeProb.iidLaw d ν)
      = ∫⁻ η, g (u (Parking.xi δ η) ℓ 0) ∂(LatticeProb.iidLaw d ν) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hsm : Measurable (fun η : Site d → ℤ => fun x => η (x + y)) :=
    measurable_pi_lambda _ fun x => measurable_pi_apply (x + y)
  have hshift : (LatticeProb.iidLaw d ν).map (fun η : Site d → ℤ => fun x => η (x + y))
      = LatticeProb.iidLaw d ν := iidLaw_map_shiftConf ν y
  have hkey : ∀ η : Site d → ℤ,
      u (Parking.xi δ (fun x => η (x + y))) ℓ 0 = u (Parking.xi δ η) ℓ y := by
    intro η
    rw [xi_shiftConf]
    rw [u_shift hd (Parking.xi δ η) ℓ y 0, zero_add]
  have hmeas : Measurable (fun η : Site d → ℤ => g (u (Parking.xi δ η) ℓ 0)) :=
    hg.comp ((measurable_u_eval ℓ 0).comp (measurable_xiField δ))
  calc ∫⁻ η, g (u (Parking.xi δ η) ℓ y) ∂(LatticeProb.iidLaw d ν)
      = ∫⁻ η, g (u (Parking.xi δ (fun x => η (x + y))) ℓ 0) ∂(LatticeProb.iidLaw d ν) := by
        refine lintegral_congr fun η => ?_
        rw [hkey η]
    _ = ∫⁻ η, g (u (Parking.xi δ η) ℓ 0) ∂((LatticeProb.iidLaw d ν).map
          (fun η : Site d → ℤ => fun x => η (x + y))) := (lintegral_map hmeas hsm).symm
    _ = ∫⁻ η, g (u (Parking.xi δ η) ℓ 0) ∂(LatticeProb.iidLaw d ν) := by rw [hshift]

/-- **The fifth moment of the odometer along the walk.**  Averaging over the configuration
and over the walk gives the same number as averaging at the origin. -/
theorem lintegral_prod_u_xi (hd : 1 ≤ d) (δ : ℝ) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (ℓ s : ℕ) :
    ∫⁻ p, ENNReal.ofReal (u (Parking.xi δ p.1) ℓ (p.2 s) ^ (5:ℕ))
        ∂((LatticeProb.iidLaw d ν).prod (LatticeProb.siteWalkLaw d (0 : Site d)))
      = ∫⁻ η, ENNReal.ofReal (u (Parking.xi δ η) ℓ 0 ^ (5:ℕ)) ∂(LatticeProb.iidLaw d ν) := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hg : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (5:ℕ))) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const 5)
  have hf : Measurable (fun p : (Site d → ℤ) × (ℕ → Site d) =>
      ENNReal.ofReal (u (Parking.xi δ p.1) ℓ (p.2 s) ^ (5:ℕ))) :=
    hg.comp ((measurable_u_xi_pair (d := d) δ ℓ).fun_comp
      (measurable_fst.prodMk ((measurable_pi_apply s).comp measurable_snd)))
  rw [MeasureTheory.lintegral_prod_symm _ hf.aemeasurable]
  have hinner : ∀ X : ℕ → Site d,
      (∫⁻ η, ENNReal.ofReal (u (Parking.xi δ η) ℓ (X s) ^ (5:ℕ)) ∂(LatticeProb.iidLaw d ν))
        = ∫⁻ η, ENNReal.ofReal (u (Parking.xi δ η) ℓ 0 ^ (5:ℕ)) ∂(LatticeProb.iidLaw d ν) :=
    fun X => lintegral_u_xi_shift hd δ ν ℓ (X s) hg
  simp_rw [hinner]
  rw [lintegral_const, measure_univ, mul_one]

/-! ### Integrability of the fifth moment of the odometer of the recentred scenery -/

theorem integrable_u_xi_pow (hd : 1 ≤ d) {δ θ : ℝ} (hθ : 0 < θ)
    (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) (r ℓ : ℕ) (y : Site d) :
    Integrable (fun η : Site d → ℤ => u (Parking.xi δ η) ℓ y ^ r) (LatticeProb.iidLaw d ν) := by
  haveI : IsProbabilityMeasure (shiftLaw δ ν) := inferInstance
  have hexp' : Integrable (fun z : ℝ => Real.exp (θ * |z|)) (shiftLaw δ ν) :=
    integrable_exp_abs_shiftLaw θ δ hθ.le ν hexp
  have hmax : Integrable (fun t : ℝ => max t 0 ^ r) (shiftLaw δ ν) :=
    integrable_maxPow_of_exp (shiftLaw δ ν) hθ hexp' r
  have hI : Integrable (fun η : Site d → ℝ => u η ℓ y ^ r)
      (LatticeProb.iidLaw d (shiftLaw δ ν)) := integrable_u_pow_iid hd _ r hmax ℓ y
  rw [← law_map_xi (d := d) δ ν] at hI
  refine (integrable_map_measure ?_ (measurable_xiField δ).aemeasurable).mp hI
  rw [law_map_xi (d := d) δ ν]
  exact ((measurable_u_eval ℓ y).pow_const r).aestronglyMeasurable

/-! ### The a priori bound on a block term -/

theorem u_xi_le_boxSum (hd : 1 ≤ d) (δ : ℝ) (η : Site d → ℤ) {t ℓ : ℕ} {y : Site d}
    (hy : y ∈ boxFinset (0 : Site d) t) :
    u (Parking.xi δ η) ℓ y
      ≤ (ℓ : ℝ) * ∑ z ∈ boxFinset (0 : Site d) (t + ℓ), |Parking.xi δ η z| := by
  refine (u_le_mul_posBox hd (Parking.xi δ η) ℓ y).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg ℓ)
  have hstep : (∑ z ∈ boxFinset y ℓ, max (Parking.xi δ η z) 0)
      ≤ ∑ z ∈ boxFinset y ℓ, |Parking.xi δ η z| :=
    Finset.sum_le_sum fun z _ => max_le (le_abs_self _) (abs_nonneg _)
  refine hstep.trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun w hw => mem_boxFinset_add hy hw) (fun z _ _ => abs_nonneg _)

theorem blockTerm_bound (hd : 1 ≤ d) (δ : ℝ) (η : Site d → ℤ)
    {σ : (ℕ → Site d) → ℕ} {n N : ℕ} (hσn : ∀ X, σ X ≤ n) (k : ℕ)
    {X : ℕ → Site d} (hX : ∀ j ≤ n, X j ∈ boxFinset (0 : Site d) n) :
    (if blockBound N k < σ X then
        u (Parking.xi δ η) (blockBound N (k + 1) - blockBound N k) (X (blockBound N k)) else 0)
      ≤ ((max N (2 * n) : ℕ) : ℝ)
          * ∑ z ∈ boxFinset (0 : Site d) (n + max N (2 * n)), |Parking.xi δ η z| := by
  set L : ℕ := max N (2 * n) with hL
  set G : ℝ := ∑ z ∈ boxFinset (0 : Site d) (n + L), |Parking.xi δ η z| with hG
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun _ _ => abs_nonneg _
  by_cases hlt : blockBound N k < σ X
  swap
  · rw [if_neg hlt]
    positivity
  rw [if_pos hlt]
  have hbk : blockBound N k ≤ n := by have := hσn X; omega
  have hmem : X (blockBound N k) ∈ boxFinset (0 : Site d) n := hX _ hbk
  have hsucc : blockBound N (k + 1) ≤ L := by
    have h1 : blockBound N (k + 1) = max N (2 * blockBound N k) := rfl
    rw [h1, hL]
    omega
  have hℓ : blockBound N (k + 1) - blockBound N k ≤ L := by omega
  refine (u_xi_le_boxSum hd δ η hmem).trans ?_
  refine mul_le_mul ?_ ?_ (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg L)
  · exact_mod_cast hℓ
  · rw [hG]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (boxFinset_mono (by omega)) (fun z _ _ => abs_nonneg _)

end Parking

end
