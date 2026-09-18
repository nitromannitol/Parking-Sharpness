/-
`eq:near-centered-moment` (`parking.tex:2797-2801`), at every exponent.

"Replacing the finitely many relevant coordinates one at a time by independent
copies of `ζ` and applying `eq:near-convex` gives
`(E u_m(0;ξ_δ)^r)^{1/r} ≤ (E u_m(0;ζ)^r)^{1/r}`.  Theorem 2.5 bounds
`E u_m(0;ζ)` by `C φ_d(m)`.  Lemma 7.1 and `eq:green-norms` therefore give
`(E u_m(0;ξ_δ)^r)^{1/r} ≤ C(φ_d(m) + √r ‖g_m‖_2 + r max_x g_m(x))`."

The coordinate replacement of `Parking/Support/MeanHorizonStep1.lean` is available at
every even exponent, and the reference law does not depend on `δ`, so the whole bound
is uniform in `δ`: the growth of the mean odometer and the concentration estimate are
applied once, at that law alone.  The two Green quantities are left as they stand here
rather than replaced by their rates, because the horizon at which they will be read
depends on `δ`.
-/
import Parking.Support.MeanHorizonStep1

open MeasureTheory LatticeProb ProbabilityTheory

noncomputable section
namespace Parking
variable {d : ℕ}

/-- **The moment bound at the reference law at every exponent.**  `thm:BP` bounds the
mean and `lem:u-concentration` with `eq:green-norms` bounds the deviation. -/
theorem exists_zeta_norm (hd : 1 ≤ d) (hGrowth : Parking.External.SandpileGrowth)
    (hConc : Parking.External.UConcentration) (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    (hmean : ∫ z, z ∂ζ = 0) (hv0 : 0 < evariance id ζ) (hvT : evariance id ζ < ⊤)
    {θ' : ℝ} (hθ' : 0 < θ') (hexp' : Integrable (fun z : ℝ => Real.exp (θ' * |z|)) ζ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m → ∀ r : ℝ, 2 ≤ r →
      (∫ η, |u η m 0| ^ r ∂(LatticeProb.iidLaw d ζ)) ^ (1 / r)
        ≤ C * (phi d m + Real.sqrt r * l2Norm (green d m) + r * greenMax d m) := by
  obtain ⟨C0, hC0, hmeanle⟩ :=
    exists_mean_le_phi (d := d) hd hGrowth ζ hmean hv0 hvT ⟨θ', hθ', hexp'⟩
  obtain ⟨C1, hC1, hnorm⟩ := exists_uNormReal_le (d := d) hd hConc ζ hθ' hexp'
  refine ⟨C0 + C1, by positivity, fun m hm r hr => ?_⟩
  have hm1 : 1 ≤ m := by omega
  have h1 := hnorm m hm1 r hr
  have h2 := hmeanle m hm
  have hphi0 : 0 ≤ phi d m :=
    le_trans (le_of_lt (Real.log_pos (by norm_num))) (log_two_le_phi d m)
  have hl20 : (0 : ℝ) ≤ l2Norm (green d m) := Real.sqrt_nonneg _
  have hmx0 : (0 : ℝ) ≤ greenMax d m := Real.iSup_nonneg fun x => green_nonneg m x
  have hs0 : (0 : ℝ) ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hr0 : (0 : ℝ) < r := by linarith
  nlinarith [h1, h2, hphi0, hl20, hmx0, hs0, hC0, hC1,
    mul_nonneg hs0 hl20, mul_nonneg hr0.le hmx0]

/-- **`eq:near-centered-moment`** (`parking.tex:2797-2801`).  The coordinatewise convex
comparison replaces the recentred scenery by the fixed reference law at every even
enough exponent, and the reference bound is uniform in `δ`. -/
theorem exists_near_centered (hd : 1 ≤ d) (hGrowth : Parking.External.SandpileGrowth)
    (hConc : Parking.External.UConcentration) {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ} (hfam : NearFamily δ₀ ν θ M K) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Icc (0 : ℝ) δ₀, ∀ m : ℕ, 2 ≤ m → ∀ j : ℕ,
      (∫ η, u (Parking.xi δ η) m 0 ^ (j + 2) ∂(LatticeProb.iidLaw d (ν δ)))
            ^ (1 / ((j : ℝ) + 2))
        ≤ C * (phi d m + Real.sqrt ((j : ℝ) + 2) * l2Norm (green d m)
            + ((j : ℝ) + 2) * greenMax d m) := by
  have hfam' : NearFamily δ₀ ν θ M K := hfam
  obtain ⟨hδ₀, hθ, hprob, hmeanν, -, hexp, -⟩ := hfam
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) δ₀ := ⟨le_rfl, hδ₀.le⟩
  haveI hp0 : IsProbabilityMeasure (ν 0) := hprob 0 h0mem
  have hM1 : 1 ≤ M :=
    le_trans (one_le_integral_exp_abs hθ (ν 0) (hexp 0 h0mem).1) (hexp 0 h0mem).2
  have hA1 : 1 ≤ refBound θ δ₀ M := by
    rw [refBound]
    have h1 : (1 : ℝ) ≤ Real.exp (θ * δ₀) := Real.one_le_exp (by positivity)
    nlinarith
  have hb : (0 : ℝ) < θ⁻¹ := inv_pos.mpr hθ
  have hc : (0 : ℝ) ≤ 2 * Real.log (refBound θ δ₀ M) / θ := by
    have : 0 ≤ Real.log (refBound θ δ₀ M) := Real.log_nonneg hA1
    positivity
  haveI hpζ : IsProbabilityMeasure (refZeta θ δ₀ M) := by rw [refZeta]; infer_instance
  have hζmean : ∫ z, z ∂(refZeta θ δ₀ M) = 0 := by rw [refZeta]; exact integral_refLaw_id _ _
  have hζv0 : 0 < evariance (id : ℝ → ℝ) (refZeta θ δ₀ M) := by
    rw [refZeta]; exact evariance_refLaw_pos hb hc
  have hζvT : evariance (id : ℝ → ℝ) (refZeta θ δ₀ M) < ⊤ := by
    rw [refZeta]; exact evariance_refLaw_lt_top _ _
  have hζexp : Integrable (fun z : ℝ => Real.exp ((θ / 2) * |z|)) (refZeta θ δ₀ M) := by
    rw [refZeta]
    refine integrable_exp_abs_refLaw hb hc ?_
    rw [div_mul_eq_mul_div, mul_inv_cancel₀ (ne_of_gt hθ)]
    norm_num
  obtain ⟨C, hC, hCle⟩ := exists_zeta_norm (d := d) hd hGrowth hConc (refZeta θ δ₀ M)
    hζmean hζv0 hζvT (by positivity : (0 : ℝ) < θ / 2) hζexp
  refine ⟨C, hC, fun δ hδ m hm j => ?_⟩
  have hr2 : (2 : ℝ) ≤ (j : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hconv : ∫ η, |u η m 0| ^ ((j : ℝ) + 2) ∂(LatticeProb.iidLaw d (refZeta θ δ₀ M))
      = ∫ η, u η m 0 ^ (j + 2) ∂(LatticeProb.iidLaw d (refZeta θ δ₀ M)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show |u η m 0| ^ ((j : ℝ) + 2) = u η m 0 ^ (j + 2)
    rw [abs_of_nonneg (u_nonneg η m 0),
      show ((j : ℝ) + 2) = (((j + 2 : ℕ)) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hcmp := integral_pow_u_xi_le (d := d) hd hfam' hδ j m
  have hnn : (0 : ℝ) ≤ ∫ η, u (Parking.xi δ η) m 0 ^ (j + 2) ∂(LatticeProb.iidLaw d (ν δ)) :=
    integral_nonneg fun η => pow_nonneg (u_nonneg _ m 0) _
  refine le_trans (Real.rpow_le_rpow hnn hcmp (by positivity)) ?_
  rw [← hconv]
  exact hCle m hm ((j : ℝ) + 2) hr2

end Parking
end
