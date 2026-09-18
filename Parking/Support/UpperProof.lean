/-
Step 1 of the proof of `thm:upper` (`parking.tex:1419-1443`).

The paper takes `r`-th moments in `eq:pathwise-comparison`, inserts
`prop:w-moment`, absorbs half of `(E U_n(0)^r)^{1/r}` by Young's inequality and
uses `κ_d(n) ≥ 1`:

    (E U_n(0)^r)^{1/r} ≤ (E u_n(0)^r)^{1/r}
      + C (n+1)^{1/r} (√(r κ_d(n) (E U_n(0)^r)^{1/r}) + r)

and therefore

    (E U_n(0)^r)^{1/r} ≤ C ((E u_n(0)^r)^{1/r} + r (n+1)^{2/r} κ_d(n)).

Everything analytic in that is in `Parking/Support/UpperStep.lean`
(`Parking.rNorm_add_le`, `Parking.young_absorb`, `Parking.one_le_kappa`); this
file is the assembly.
-/
import Parking.Support.UpperStep
import Parking.Support.UBound

noncomputable section

namespace Parking

open MeasureTheory LatticeProb

variable {d : ℕ}

/-! ### Two exponent identities -/

theorem rpow_one_div_le_rpow_two_div {x r : ℝ} (hx : 1 ≤ x) (hr : 0 < r) :
    x ^ (1 / r) ≤ x ^ (2 / r) :=
  Real.rpow_le_rpow_of_exponent_le hx (by gcongr; norm_num)

theorem rpow_add_le_two_rpow {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) :
    (a + b) ^ p ≤ 2 ^ p * (a ^ p + b ^ p) := by
  have hmax : a + b ≤ 2 * max a b := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hm0 : 0 ≤ max a b := le_trans ha (le_max_left a b)
  have h1 : (a + b) ^ p ≤ (2 * max a b) ^ p :=
    Real.rpow_le_rpow (by linarith) hmax hp
  have h2 : (2 * max a b) ^ p = 2 ^ p * (max a b) ^ p :=
    Real.mul_rpow (by norm_num) hm0
  have h3 : (max a b) ^ p ≤ a ^ p + b ^ p := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]
      have := Real.rpow_nonneg ha p
      linarith
    · rw [max_eq_left h]
      have := Real.rpow_nonneg hb p
      linarith
  have h20 : (0 : ℝ) ≤ (2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) p
  calc (a + b) ^ p ≤ 2 ^ p * (max a b) ^ p := by rw [← h2]; exact h1
    _ ≤ 2 ^ p * (a ^ p + b ^ p) := by exact mul_le_mul_of_nonneg_left h3 h20

theorem sq_rpow_one_div {x r : ℝ} (hx : 0 < x) (_hr : r ≠ 0) :
    (x ^ (1 / r)) ^ 2 = x ^ (2 / r) := by
  rw [sq, ← Real.rpow_add hx]
  congr 1
  ring

/-! ### The `r`-th moment norms of the three fields at the origin -/

theorem rNorm_U (μ : Measure (Data d)) (r : ℝ) (n : ℕ) :
    rNorm μ r (fun ω => ((U ω n 0 : ℕ) : ℝ))
      = (∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ r ∂μ) ^ (1 / r) := by
  have habs : ∀ ω : Data d, |((U ω n 0 : ℕ) : ℝ)| = ((U ω n 0 : ℕ) : ℝ) :=
    fun ω => abs_of_nonneg (Nat.cast_nonneg _)
  simp only [rNorm, habs]

theorem rNorm_wStar (μ : Measure (Data d)) (r : ℝ) (n : ℕ) :
    rNorm μ r (fun ω => wStar ω n 0) = (∫ ω, wStar ω n 0 ^ r ∂μ) ^ (1 / r) := by
  have habs : ∀ ω : Data d, |wStar ω n 0| = wStar ω n 0 :=
    fun ω => abs_of_nonneg (wStar_nonneg ω n 0)
  simp only [rNorm, habs]

/-! ### The discrepancy has every moment -/

theorem integrable_diff_rpow (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν)
    {r : ℝ} (hr : 1 ≤ r) (n : ℕ) :
    Integrable (fun ω : Data d => |((U ω n 0 : ℕ) : ℝ) - uOf ω n 0| ^ r) (law d ν) := by
  have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one hr
  have hdom : Integrable (fun ω : Data d => 2 ^ r * wStar ω n 0 ^ r) (law d ν) :=
    (integrable_wStar_rpow hd ν hθ hexp hr n 0).const_mul _
  refine Integrable.mono' hdom
    (((((measurable_from_countable' fun m : ℕ => (m : ℝ)).comp
      (measurable_U n 0)).sub (measurable_uOf n 0)).abs.pow_const r).aestronglyMeasurable)
    ((ae_stack_nbr_law hd ν).mono fun ω hω => ?_)
  have hpath := (pathwise_comparison_of_labelOrder (d := d) hd hω n 0).2
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r),
    ← Real.mul_rpow (by norm_num) (wStar_nonneg ω n 0)]
  exact Real.rpow_le_rpow (abs_nonneg _) hpath hr0

/-! ### Step 1 -/

/-- **Step 1 of `thm:upper`.**  The `r`-th moment of the parking odometer
against the `r`-th moment of the sandpile odometer, with the error absorbed. -/
theorem upper_step_one_uniform (hd : 1 ≤ d) (hBern : Parking.External.Bernstein) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : Measure ℤ, IsProbabilityMeasure ν → ∀ θ : ℝ, 0 < θ →
      Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν →
      ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
      (∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ r ∂(law d ν)) ^ (1 / r)
        ≤ C * ((∫ ω, |uOf ω n 0| ^ r ∂(law d ν)) ^ (1 / r)
            + r * ((n : ℝ) + 1) ^ (2 / r) * kappa d n) := by
  obtain ⟨C₀, hC₀, hC₀le'⟩ := exists_wErr_moment_const_uniform (d := d) hd hBern
  refine ⟨2 + 4 * C₀ ^ 2 + 4 * C₀, by positivity, ?_⟩
  intro ν hprobν θ hθ hexp n hn r hr2
  haveI := hprobν
  have hC₀le := hC₀le' ν hprobν θ hθ hexp
  have hr1 : (1 : ℝ) ≤ r := by linarith
  have hr0 : (0 : ℝ) < r := by linarith
  set μ : Measure (Data d) := law d ν with hμ
  set X : ℝ := (∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ r ∂μ) ^ (1 / r) with hXdef
  set Y : ℝ := (∫ ω, |uOf ω n 0| ^ r ∂μ) ^ (1 / r) with hYdef
  set W : ℝ := (∫ ω, wStar ω n 0 ^ r ∂μ) ^ (1 / r) with hWdef
  set S : ℝ := ⨆ m ∈ Set.Iic n, (∫ ω, |wErr ω m 0| ^ r ∂μ) ^ (1 / r) with hSdef
  -- the three integrability facts
  have hIU : Integrable (fun ω : Data d => |((U ω n 0 : ℕ) : ℝ)| ^ r) μ := by
    have h := integrable_U_rpow hd ν hθ hexp hr1 n 0
    have habs : ∀ ω : Data d, |((U ω n 0 : ℕ) : ℝ)| = ((U ω n 0 : ℕ) : ℝ) :=
      fun ω => abs_of_nonneg (Nat.cast_nonneg _)
    simpa only [habs] using h
  have hIu : Integrable (fun ω : Data d => |uOf ω n 0| ^ r) μ :=
    integrable_uOf_rpow hd ν hθ hexp hr1 n 0
  have hId : Integrable (fun ω : Data d =>
      |((U ω n 0 : ℕ) : ℝ) - uOf ω n 0| ^ r) μ :=
    integrable_diff_rpow hd ν hθ hexp hr1 n
  have hIw : Integrable (fun ω : Data d => |2 * wStar ω n 0| ^ r) μ := by
    have h := (integrable_wStar_rpow hd ν hθ hexp hr1 n 0).const_mul (2 ^ r)
    have habs : ∀ ω : Data d, |2 * wStar ω n 0| ^ r = 2 ^ r * wStar ω n 0 ^ r := by
      intro ω
      rw [abs_of_nonneg (mul_nonneg (by norm_num) (wStar_nonneg ω n 0)),
        Real.mul_rpow (by norm_num) (wStar_nonneg ω n 0)]
    simpa only [habs] using h
  -- Minkowski
  have hmeasU : AEStronglyMeasurable (fun ω : Data d => ((U ω n 0 : ℕ) : ℝ)) μ :=
    (((measurable_from_countable' fun m : ℕ => (m : ℝ)).comp
      (measurable_U n 0))).aestronglyMeasurable
  have hmeasu : AEStronglyMeasurable (fun ω : Data d => uOf ω n 0) μ :=
    (measurable_uOf n 0).aestronglyMeasurable
  have hmeasd : AEStronglyMeasurable
      (fun ω : Data d => ((U ω n 0 : ℕ) : ℝ) - uOf ω n 0) μ := hmeasU.sub hmeasu
  have hsplit : (fun ω : Data d => uOf ω n 0 + (((U ω n 0 : ℕ) : ℝ) - uOf ω n 0))
      = fun ω : Data d => ((U ω n 0 : ℕ) : ℝ) := by
    funext ω; ring
  have hIsum : Integrable
      (fun ω : Data d => |uOf ω n 0 + (((U ω n 0 : ℕ) : ℝ) - uOf ω n 0)| ^ r) μ := by
    have heq : ∀ ω : Data d, uOf ω n 0 + (((U ω n 0 : ℕ) : ℝ) - uOf ω n 0)
        = ((U ω n 0 : ℕ) : ℝ) := fun ω => by ring
    simpa only [heq] using hIU
  have hmink := rNorm_add_le μ hr1 hmeasu hmeasd hIu hId hIsum
  rw [hsplit] at hmink
  rw [rNorm_U μ r n, ← hXdef] at hmink
  have hYeq : rNorm μ r (fun ω : Data d => uOf ω n 0) = Y := by
    rw [hYdef, rNorm]
  rw [hYeq] at hmink
  -- the error term
  have hdiff : rNorm μ r (fun ω : Data d => ((U ω n 0 : ℕ) : ℝ) - uOf ω n 0) ≤ 2 * W := by
    have hmono : rNorm μ r (fun ω : Data d => ((U ω n 0 : ℕ) : ℝ) - uOf ω n 0)
        ≤ rNorm μ r (fun ω : Data d => 2 * wStar ω n 0) := by
      refine rNorm_mono μ hr0 ?_ hIw
      refine (ae_stack_nbr_law hd ν).mono fun ω hω => ?_
      have hpath := (pathwise_comparison_of_labelOrder (d := d) hd hω n 0).2
      rw [abs_of_nonneg (mul_nonneg (by norm_num) (wStar_nonneg ω n 0))]
      exact hpath
    refine hmono.trans ?_
    rw [rNorm_const_mul μ hr0 (by norm_num : (0:ℝ) ≤ 2), rNorm_wStar μ r n, ← hWdef]
  -- w^\star against the maximum of the errors, and the martingale moment bound
  have hWS : W ≤ ((n : ℝ) + 1) ^ (1 / r) * S := by
    rw [hWdef, hSdef]
    exact wStar_moment_bound hd ν hθ hexp hr1 n
  have hSb : S ≤ C₀ * (Real.sqrt (r * kappa d n * X) + r) := by
    rw [hSdef, hXdef]
    exact hC₀le n hn r hr2
  -- the absorption
  have hnp : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hnp0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  set a : ℝ := 2 * (((n : ℝ) + 1) ^ (1 / r) * C₀) with hadef
  have ha0 : 0 ≤ a := by
    have : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (1 / r) := Real.rpow_nonneg (le_of_lt hnp0) _
    rw [hadef]; positivity
  have hX0 : 0 ≤ X := Real.rpow_nonneg (integral_nonneg fun ω =>
    Real.rpow_nonneg (Nat.cast_nonneg _) r) _
  have hb0 : (0 : ℝ) ≤ r * kappa d n := mul_nonneg (le_of_lt hr0) (kappa_nonneg d n)
  have hkey : X ≤ Y + a * (Real.sqrt (r * kappa d n * X) + r) := by
    have hW0 : 0 ≤ W := Real.rpow_nonneg (integral_nonneg fun ω =>
      Real.rpow_nonneg (wStar_nonneg ω n 0) r) _
    have hnpow0 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (1 / r) := Real.rpow_nonneg (le_of_lt hnp0) _
    have h1 : 2 * W ≤ a * (Real.sqrt (r * kappa d n * X) + r) := by
      calc 2 * W ≤ 2 * (((n : ℝ) + 1) ^ (1 / r) * S) := by linarith
        _ ≤ 2 * (((n : ℝ) + 1) ^ (1 / r) * (C₀ * (Real.sqrt (r * kappa d n * X) + r))) := by
            have : S ≤ C₀ * (Real.sqrt (r * kappa d n * X) + r) := hSb
            nlinarith [hnpow0]
        _ = a * (Real.sqrt (r * kappa d n * X) + r) := by rw [hadef]; ring
    linarith [hmink, hdiff]
  have habs := young_absorb hX0 hb0 hkey
  -- the two error terms against `r (n+1)^{2/r} κ`
  have hkap : 1 ≤ kappa d n := one_le_kappa d hn
  have h2r : ((n : ℝ) + 1) ^ (1 / r) ≤ ((n : ℝ) + 1) ^ (2 / r) :=
    rpow_one_div_le_rpow_two_div hnp hr0
  have hsq : (((n : ℝ) + 1) ^ (1 / r)) ^ 2 = ((n : ℝ) + 1) ^ (2 / r) :=
    sq_rpow_one_div hnp0 (ne_of_gt hr0)
  have hE0 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (2 / r) := Real.rpow_nonneg (le_of_lt hnp0) _
  have hY0 : 0 ≤ Y := Real.rpow_nonneg (integral_nonneg fun ω =>
    Real.rpow_nonneg (abs_nonneg _) r) _
  have ha2 : a ^ 2 * (r * kappa d n) = 4 * C₀ ^ 2 * (r * ((n : ℝ) + 1) ^ (2 / r) * kappa d n) := by
    rw [hadef]
    rw [show (2 * (((n : ℝ) + 1) ^ (1 / r) * C₀)) ^ 2
        = 4 * ((((n : ℝ) + 1) ^ (1 / r)) ^ 2) * C₀ ^ 2 by ring, hsq]
    ring
  have ha3 : 2 * a * r ≤ 4 * C₀ * (r * ((n : ℝ) + 1) ^ (2 / r) * kappa d n) := by
    have hstep : 2 * a * r = 4 * C₀ * (r * ((n : ℝ) + 1) ^ (1 / r)) := by rw [hadef]; ring
    rw [hstep]
    have h1 : r * ((n : ℝ) + 1) ^ (1 / r) ≤ r * ((n : ℝ) + 1) ^ (2 / r) := by
      exact mul_le_mul_of_nonneg_left h2r (le_of_lt hr0)
    have h2 : r * ((n : ℝ) + 1) ^ (2 / r)
        ≤ r * ((n : ℝ) + 1) ^ (2 / r) * kappa d n := by
      nlinarith [mul_nonneg (le_of_lt hr0) hE0]
    nlinarith [hC₀.le]
  have hfin : 0 ≤ r * ((n : ℝ) + 1) ^ (2 / r) * kappa d n := by
    have : (0 : ℝ) ≤ kappa d n := kappa_nonneg d n
    positivity
  calc X ≤ 2 * Y + a ^ 2 * (r * kappa d n) + 2 * a * r := habs
    _ ≤ 2 * Y + 4 * C₀ ^ 2 * (r * ((n : ℝ) + 1) ^ (2 / r) * kappa d n)
        + 4 * C₀ * (r * ((n : ℝ) + 1) ^ (2 / r) * kappa d n) := by rw [ha2]; linarith
    _ ≤ (2 + 4 * C₀ ^ 2 + 4 * C₀) * (Y + r * ((n : ℝ) + 1) ^ (2 / r) * kappa d n) := by
        nlinarith [hY0, hfin, hC₀.le]

/-- Step 1 of `thm:upper` at a single law. -/
theorem upper_step_one (hd : 1 ≤ d) (hBern : Parking.External.Bernstein)
    (ν : Measure ℤ) [IsProbabilityMeasure ν] {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
      (∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ r ∂(law d ν)) ^ (1 / r)
        ≤ C * ((∫ ω, |uOf ω n 0| ^ r ∂(law d ν)) ^ (1 / r)
            + r * ((n : ℝ) + 1) ^ (2 / r) * kappa d n) := by
  obtain ⟨C, hC, h⟩ := upper_step_one_uniform (d := d) hd hBern
  exact ⟨C, hC, h ν inferInstance θ hθ hexp⟩

end Parking

end