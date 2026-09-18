/-
The `L^q`-moment form of a sub-Gaussian-on-a-range tail bound: the standard
"exponential tilt, then optimize the tilt parameter" argument that turns
`LatticeProb.SubGaussianOn X c s₀ μ` (a bounded moment generating function for
every parameter of size at most `s₀`; `LatticeProb.Prob.WeightedConc` builds
exactly this fact internally on the way to its tail bound
`LatticeProb.weighted_exp_conc_tail`) into the two-regime `L^q` moment bound

    (∫ |X|^q ∂μ)^(1/q) ≤ K · (√c · √q + q / s₀)

for real `q ≥ 1`, with ONE universal numeric constant `K` (not depending on
`X, c, s₀, μ, q`).  This is exactly the shape `Parking.External.UConcentration`
carries and that `Parking.Support.SpatField`'s Kolmogorov moment bound needs;
it converts `Parking.exists_linPotential_increment_concentration`'s tail bound
into that shape without any further citation.

The pointwise inequality driving the whole argument, for `t ≥ 0`, `q > 0`,
`λ > 0`,

    t^q ≤ (q/λ)^q · exp(λt − q),

is `Real.log_le_sub_one_of_pos` at `u := λt/q` (`log u ≤ u − 1`, multiplied by
`q` and rearranged using `q·u = λt`).  No Gamma function and no layer-cake
integral is needed: only this one elementary exponential-tilt bound, applied
at the two-sided exponential moment `SubGaussianOn` already supplies, and then
optimized over the tilt `λ` (capped at `s₀`), reproduces the classical
sub-Gaussian/sub-exponential moment growth `√q` below the range and `q` beyond
it.
-/
import LatticeProb.Prob.WeightedConc

noncomputable section

namespace Parking

open MeasureTheory LatticeProb

/-! ### The pointwise exponential-tilt bound -/

/-- **The elementary tilt bound.**  For `t ≥ 0`, `q > 0`, `λ > 0`,
`t^q ≤ (q/λ)^q · exp(λt − q)`. -/
theorem rpow_le_mul_exp_sub (q lam t : ℝ) (hq : 0 < q) (hlam : 0 < lam) (ht : 0 ≤ t) :
    t ^ q ≤ (q / lam) ^ q * Real.exp (lam * t - q) := by
  by_cases ht0 : t = 0
  · rw [ht0, Real.zero_rpow hq.ne']
    positivity
  · have ht0' : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    set u : ℝ := lam * t / q with hu
    have hupos : 0 < u := by positivity
    have hqu : q * u = lam * t := by rw [hu]; field_simp
    have hlogle : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hupos
    have h3 : u ^ q ≤ Real.exp (lam * t - q) := by
      rw [Real.rpow_def_of_pos hupos q]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hlogle hq.le]
    have hteq : t = (q / lam) * u := by rw [hu]; field_simp
    calc t ^ q = ((q / lam) * u) ^ q := by rw [hteq]
      _ = (q / lam) ^ q * u ^ q := Real.mul_rpow (by positivity) hupos.le
      _ ≤ (q / lam) ^ q * Real.exp (lam * t - q) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)

/-- `exp(λ|x|) ≤ exp(λx) + exp(−λx)`. -/
theorem exp_mul_abs_le_add (lam x : ℝ) :
    Real.exp (lam * |x|) ≤ Real.exp (lam * x) + Real.exp (-(lam * x)) := by
  rcases abs_choice x with h | h
  · rw [h]; nlinarith [Real.exp_pos (-(lam * x))]
  · rw [h]
    have hxx : lam * -x = -(lam * x) := by ring
    rw [hxx]
    nlinarith [Real.exp_pos (lam * x)]

/-- **The two-sided tilt bound.**  For `q > 0`, `λ > 0`,
`|x|^q ≤ (q/λ)^q·exp(−q)·(exp(λx) + exp(−λx))`. -/
theorem abs_rpow_le_const_mul_add_exp (q lam x : ℝ) (hq : 0 < q) (hlam : 0 < lam) :
    |x| ^ q ≤ (q / lam) ^ q * Real.exp (-q) * (Real.exp (lam * x) + Real.exp (-(lam * x))) := by
  have h1 := rpow_le_mul_exp_sub q lam |x| hq hlam (abs_nonneg x)
  have h2 := exp_mul_abs_le_add lam x
  have h3 : Real.exp (lam * |x| - q) = Real.exp (-q) * Real.exp (lam * |x|) := by
    rw [← Real.exp_add]; congr 1; ring
  calc |x| ^ q ≤ (q / lam) ^ q * Real.exp (lam * |x| - q) := h1
    _ = (q / lam) ^ q * (Real.exp (-q) * Real.exp (lam * |x|)) := by rw [h3]
    _ = (q / lam) ^ q * Real.exp (-q) * Real.exp (lam * |x|) := by ring
    _ ≤ (q / lam) ^ q * Real.exp (-q) *
        (Real.exp (lam * x) + Real.exp (-(lam * x))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-! ### The integrated bound, at a fixed tilt parameter -/

/-- **The `L^q` moment bound at a fixed tilt `λ ≤ s₀`**, from
`LatticeProb.SubGaussianOn X c s₀ μ`. -/
theorem integral_rpow_abs_le_of_subGaussianOn {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X : Ω → ℝ} {c s0 : ℝ} (hSG : SubGaussianOn X c s0 μ)
    {q lam : ℝ} (hq : 0 < q) (hlam : 0 < lam) (hlams0 : lam ≤ s0) :
    ∫ ω, |X ω| ^ q ∂μ ≤ 2 * (q / lam) ^ q * Real.exp (c * lam ^ 2 - q) := by
  obtain ⟨hint1, hb1⟩ := hSG lam (by rwa [abs_of_pos hlam])
  obtain ⟨hint2', hb2'⟩ := hSG (-lam) (by rwa [abs_neg, abs_of_pos hlam])
  have heqfun : (fun ω => Real.exp (-lam * X ω)) = fun ω => Real.exp (-(lam * X ω)) := by
    funext ω; congr 1; ring
  have hint2 : Integrable (fun ω => Real.exp (-(lam * X ω))) μ := by
    rw [← heqfun]; exact hint2'
  have hb2 : ∫ ω, Real.exp (-(lam * X ω)) ∂μ ≤ Real.exp (c * lam ^ 2) := by
    have hrw : ∫ ω, Real.exp (-(lam * X ω)) ∂μ = ∫ ω, Real.exp (-lam * X ω) ∂μ := by
      rw [heqfun]
    rw [hrw]
    have hsq : (-lam) ^ 2 = lam ^ 2 := by ring
    rwa [hsq] at hb2'
  have hbound : ∀ ω, |X ω| ^ q ≤ (q / lam) ^ q * Real.exp (-q) *
      (Real.exp (lam * X ω) + Real.exp (-(lam * X ω))) := fun ω =>
    abs_rpow_le_const_mul_add_exp q lam (X ω) hq hlam
  have hintg : Integrable (fun ω => (q / lam) ^ q * Real.exp (-q) *
      (Real.exp (lam * X ω) + Real.exp (-(lam * X ω)))) μ :=
    (hint1.add hint2).const_mul _
  have hle : ∫ ω, |X ω| ^ q ∂μ
      ≤ ∫ ω, (q / lam) ^ q * Real.exp (-q) *
          (Real.exp (lam * X ω) + Real.exp (-(lam * X ω))) ∂μ :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity) hintg
      (Filter.Eventually.of_forall hbound)
  have heval : ∫ ω, (q / lam) ^ q * Real.exp (-q) *
        (Real.exp (lam * X ω) + Real.exp (-(lam * X ω))) ∂μ
      = (q / lam) ^ q * Real.exp (-q) *
        (∫ ω, Real.exp (lam * X ω) ∂μ + ∫ ω, Real.exp (-(lam * X ω)) ∂μ) := by
    rw [integral_const_mul, integral_add hint1 hint2]
  have hsum : ∫ ω, Real.exp (lam * X ω) ∂μ + ∫ ω, Real.exp (-(lam * X ω)) ∂μ
      ≤ 2 * Real.exp (c * lam ^ 2) := by linarith [add_le_add hb1 hb2]
  have hfin : (q / lam) ^ q * Real.exp (-q) * (2 * Real.exp (c * lam ^ 2))
      = 2 * (q / lam) ^ q * Real.exp (c * lam ^ 2 - q) := by
    have hexp : Real.exp (c * lam ^ 2 - q) = Real.exp (c * lam ^ 2) * Real.exp (-q) := by
      rw [← Real.exp_add]; congr 1
    rw [hexp]; ring
  calc ∫ ω, |X ω| ^ q ∂μ
      ≤ ∫ ω, (q / lam) ^ q * Real.exp (-q) *
          (Real.exp (lam * X ω) + Real.exp (-(lam * X ω))) ∂μ := hle
    _ = (q / lam) ^ q * Real.exp (-q) *
        (∫ ω, Real.exp (lam * X ω) ∂μ + ∫ ω, Real.exp (-(lam * X ω)) ∂μ) := heval
    _ ≤ (q / lam) ^ q * Real.exp (-q) * (2 * Real.exp (c * lam ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * (q / lam) ^ q * Real.exp (c * lam ^ 2 - q) := hfin

/-! ### Taking the `q`-th root of a `2·A^q·exp v` bound -/

/-- `(2·(q/λ)^q·exp v)^(1/q) = 2^(1/q)·(q/λ)·exp(v/q)`. -/
theorem rpow_inv_two_mul_rpow_mul_exp (q lam v : ℝ) (hq : 0 < q) (hlam : 0 < lam) :
    (2 * (q / lam) ^ q * Real.exp v) ^ (1 / q)
      = 2 ^ (1 / q) * (q / lam) * Real.exp (v / q) := by
  have hbase : (0 : ℝ) ≤ q / lam := by positivity
  rw [Real.mul_rpow (by positivity) (Real.exp_pos v).le,
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity : (0:ℝ) ≤ (q / lam) ^ q)]
  have h1 : ((q / lam) ^ q) ^ (1 / q) = q / lam := by
    rw [← Real.rpow_mul hbase, mul_one_div, div_self hq.ne', Real.rpow_one]
  have h2 : Real.exp v ^ (1 / q) = Real.exp (v / q) := by
    rw [← Real.exp_mul]; congr 1; ring
  rw [h1, h2]

/-! ### The two-regime `L^q` moment bound -/

/-- **The `L^q` moment bound.**  For `SubGaussianOn X c s₀ μ` with `c, s₀ > 0`
and every real `q ≥ 1`,

    (∫ |X|^q ∂μ)^(1/q) ≤ K · (√c · √q + q / s₀),

with the universal constant `K = 2√2·exp(−1/2)`. -/
theorem exists_Lq_moment_bound_of_subGaussianOn {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X : Ω → ℝ} {c s0 : ℝ} (hc : 0 < c) (hs0 : 0 < s0)
    (hSG : SubGaussianOn X c s0 μ) {q : ℝ} (hq : 1 ≤ q) :
    (∫ ω, |X ω| ^ q ∂μ) ^ (1 / q)
      ≤ (2 * Real.sqrt 2 * Real.exp (-(1 / 2))) * (Real.sqrt c * Real.sqrt q + q / s0) := by
  have hq0 : 0 < q := by linarith
  have hqne : q ≠ 0 := hq0.ne'
  have hcne : c ≠ 0 := hc.ne'
  set K : ℝ := 2 * Real.sqrt 2 * Real.exp (-(1 / 2)) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  set lamStar : ℝ := Real.sqrt (q / (2 * c)) with hlamStarDef
  have hlamStarPos : 0 < lamStar := Real.sqrt_pos.mpr (by positivity)
  have hsqLam : lamStar ^ 2 = q / (2 * c) := Real.sq_sqrt (by positivity)
  have hqlam : q / lamStar = Real.sqrt 2 * Real.sqrt c * Real.sqrt q := by
    have hlhs_nonneg : 0 ≤ q / lamStar := by positivity
    have hlhs_sq : (q / lamStar) ^ 2 = 2 * c * q := by
      rw [div_pow, hsqLam]; field_simp
    have hval : q / lamStar = Real.sqrt (2 * c * q) := by
      rw [← hlhs_sq, Real.sqrt_sq hlhs_nonneg]
    rw [hval, Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * c) q,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) c]
  have h2qle : (2:ℝ) ^ (1 / q) ≤ 2 := by
    have hle1 : (1:ℝ) / q ≤ 1 := by rw [div_le_one hq0]; linarith
    calc (2:ℝ) ^ (1 / q) ≤ (2:ℝ) ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hle1
      _ = 2 := Real.rpow_one 2
  have hnonneg : (0:ℝ) ≤ ∫ ω, |X ω| ^ q ∂μ := integral_nonneg fun ω => by positivity
  have hqi : (0:ℝ) ≤ 1 / q := by positivity
  rcases le_total lamStar s0 with hcase | hcase
  · -- Case A: the Gaussian regime, tilt at `λ* = √(q/(2c))`.
    have hbound := integral_rpow_abs_le_of_subGaussianOn μ hSG hq0 hlamStarPos hcase
    have hclam : c * lamStar ^ 2 = q / 2 := by rw [hsqLam]; field_simp
    have hveq : (c * lamStar ^ 2 - q) / q = -(1 / 2) := by rw [hclam]; field_simp; ring
    have hnonneg2 : (0:ℝ) ≤ 2 * (q / lamStar) ^ q * Real.exp (c * lamStar ^ 2 - q) := by
      positivity
    have hstep1 : (∫ ω, |X ω| ^ q ∂μ) ^ (1 / q)
        ≤ (2 * (q / lamStar) ^ q * Real.exp (c * lamStar ^ 2 - q)) ^ (1 / q) :=
      Real.rpow_le_rpow hnonneg hbound hqi
    have hstep2 := rpow_inv_two_mul_rpow_mul_exp q lamStar (c * lamStar ^ 2 - q) hq0 hlamStarPos
    rw [hveq] at hstep2
    have hqlpos : (0:ℝ) ≤ q / lamStar := by positivity
    have hfinal : (2 * (q / lamStar) ^ q * Real.exp (c * lamStar ^ 2 - q)) ^ (1 / q)
        ≤ 2 * (q / lamStar) * Real.exp (-(1 / 2)) := by
      rw [hstep2]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h2qle hqlpos) (Real.exp_pos _).le
    have hKbound : 2 * (q / lamStar) * Real.exp (-(1 / 2))
        ≤ K * (Real.sqrt c * Real.sqrt q + q / s0) := by
      rw [hqlam]
      have hnn : (0:ℝ) ≤ q / s0 := by positivity
      have hcq : (0:ℝ) ≤ Real.sqrt c * Real.sqrt q := by positivity
      have hstepeq : 2 * (Real.sqrt 2 * Real.sqrt c * Real.sqrt q) * Real.exp (-(1 / 2))
          = K * (Real.sqrt c * Real.sqrt q) := by rw [hKdef]; ring
      rw [hstepeq]
      nlinarith [mul_le_mul_of_nonneg_left hnn hKpos.le]
    exact hstep1.trans (hfinal.trans hKbound)
  · -- Case B: the sub-exponential regime, tilt at `λ = s₀`.
    have hbound := integral_rpow_abs_le_of_subGaussianOn μ hSG hq0 hs0 le_rfl
    have hcs0 : c * s0 ^ 2 ≤ q / 2 := by
      have h1 : s0 ^ 2 ≤ lamStar ^ 2 := pow_le_pow_left₀ hs0.le hcase 2
      rw [hsqLam] at h1
      have h2 : c * s0 ^ 2 ≤ c * (q / (2 * c)) := mul_le_mul_of_nonneg_left h1 hc.le
      have h3 : c * (q / (2 * c)) = q / 2 := by field_simp
      linarith
    have hexple : Real.exp (c * s0 ^ 2 - q) ≤ Real.exp (-(q / 2)) := by
      apply Real.exp_le_exp.mpr; linarith
    have hbound2 : ∫ ω, |X ω| ^ q ∂μ ≤ 2 * (q / s0) ^ q * Real.exp (-(q / 2)) := by
      calc ∫ ω, |X ω| ^ q ∂μ ≤ 2 * (q / s0) ^ q * Real.exp (c * s0 ^ 2 - q) := hbound
        _ ≤ 2 * (q / s0) ^ q * Real.exp (-(q / 2)) :=
            mul_le_mul_of_nonneg_left hexple (by positivity)
    have hstep1 : (∫ ω, |X ω| ^ q ∂μ) ^ (1 / q)
        ≤ (2 * (q / s0) ^ q * Real.exp (-(q / 2))) ^ (1 / q) :=
      Real.rpow_le_rpow hnonneg hbound2 hqi
    have hstep2 := rpow_inv_two_mul_rpow_mul_exp q s0 (-(q / 2)) hq0 hs0
    have hveq : (-(q / 2)) / q = -(1 / 2) := by field_simp
    rw [hveq] at hstep2
    have hqspos : (0:ℝ) ≤ q / s0 := by positivity
    have hfinal : (2 * (q / s0) ^ q * Real.exp (-(q / 2))) ^ (1 / q)
        ≤ 2 * (q / s0) * Real.exp (-(1 / 2)) := by
      rw [hstep2]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h2qle hqspos) (Real.exp_pos _).le
    have hKbound : 2 * (q / s0) * Real.exp (-(1 / 2))
        ≤ K * (Real.sqrt c * Real.sqrt q + q / s0) := by
      have hcq : (0:ℝ) ≤ Real.sqrt c * Real.sqrt q := by positivity
      have hqs0 : (0:ℝ) ≤ q / s0 := by positivity
      have h1sqrt2 : (1:ℝ) ≤ Real.sqrt 2 := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by norm_num)
      have h2e : (2:ℝ) * Real.exp (-(1 / 2)) ≤ K := by
        rw [hKdef]; nlinarith [Real.exp_pos (-(1 / 2 : ℝ)), h1sqrt2]
      nlinarith [mul_le_mul_of_nonneg_right h2e hqs0, mul_nonneg hKpos.le hcq]
    exact hstep1.trans (hfinal.trans hKbound)

/-! ### From a coordinate-Lipschitz function of a product measure to `SubGaussianOn` -/

/-- **`SubGaussianOn` for a coordinate-Lipschitz function of a product measure with an
exponential one-site moment.**  The construction `LatticeProb.weighted_exp_conc_tail`
performs internally on the way to its own Chernoff tail bound; exported here, unchanged
in substance, so it can feed the `L^q`-moment route
(`Parking.exists_Lq_moment_bound_of_subGaussianOn`) instead. -/
theorem subGaussianOn_sub_mean_of_lipschitz (θ0 K0 : ℝ) (hθ0 : 0 < θ0) (N : ℕ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hexp : Integrable (fun z : ℝ => Real.exp (θ0 * |z|)) ν)
    (hK : ∫ z, Real.exp (θ0 * |z|) ∂ν ≤ K0)
    (F : (Fin N → ℝ) → ℝ) (hFm : Measurable F) (ℓ : Fin N → ℝ)
    (hℓnn : ∀ i, 0 ≤ ℓ i) (hℓne : ∃ i, ℓ i ≠ 0)
    (hLip : ∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
      |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) :
    SubGaussianOn (fun ξ => F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν))
      (16 * (Real.exp (max K0 1) * max K0 1) / θ0 ^ 2 * lTwoNorm ℓ ^ 2)
      (θ0 / (2 * lInfNorm ℓ)) (Measure.pi fun _ : Fin N => ν) := by
  have hL0 : 0 < lInfNorm ℓ := lInfNorm_pos ℓ hℓnn hℓne
  have hM1 : (1:ℝ) ≤ max K0 1 := le_max_right K0 1
  have hMpos : (0:ℝ) < max K0 1 := lt_of_lt_of_le one_pos hM1
  have hKle : ∫ z, Real.exp (θ0 * |z|) ∂ν ≤ max K0 1 := hK.trans (le_max_left K0 1)
  intro lam hlam
  have hlam' : |lam| * lInfNorm ℓ ≤ θ0 / 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * lInfNorm ℓ)] at hlam
    nlinarith [hlam]
  have hlamθ : |lam| * lInfNorm ℓ < θ0 := by linarith
  obtain ⟨hint, hb⟩ := weighted_exp_conc_exp θ0 (max K0 1) hθ0 N ν inferInstance hexp hKle F
    hFm ℓ hℓnn hℓne hLip lam hlamθ
  refine ⟨hint, ?_⟩
  have hδ : θ0 / 2 ≤ θ0 - |lam| * lInfNorm ℓ := by linarith
  have hδ0 : 0 < θ0 - |lam| * lInfNorm ℓ := by linarith [hθ0]
  have hsqle : θ0 ^ 2 ≤ 4 * (θ0 - |lam| * lInfNorm ℓ) ^ 2 := by nlinarith [hδ, hδ0]
  have hApos : 0 ≤ 4 * (Real.exp (max K0 1) * max K0 1) := by positivity
  have hCle : 4 * (Real.exp (max K0 1) * max K0 1) / (θ0 - |lam| * lInfNorm ℓ) ^ 2
      ≤ 16 * (Real.exp (max K0 1) * max K0 1) / θ0 ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsqle hApos]
  calc ∫ ξ, Real.exp (lam * (F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)))
        ∂(Measure.pi fun _ : Fin N => ν)
      ≤ Real.exp (4 * (Real.exp (max K0 1) * max K0 1) / (θ0 - |lam| * lInfNorm ℓ) ^ 2 * lam ^ 2 *
          lTwoNorm ℓ ^ 2) := hb
    _ ≤ Real.exp (16 * (Real.exp (max K0 1) * max K0 1) / θ0 ^ 2 * lTwoNorm ℓ ^ 2 * lam ^ 2) := by
        apply Real.exp_le_exp.mpr
        have hnn : (0:ℝ) ≤ lam ^ 2 * lTwoNorm ℓ ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hCle hnn]

/-- **The `L^q`-moment form of `LatticeProb.weighted_exp_conc_tail`.**  Same hypotheses
as `LatticeProb.weighted_exp_conc_exp`/`weighted_exp_conc_tail`, but the conclusion is
the `L^q` moment bound `(∫|F − EF|^q)^(1/q) ≤ C(√q·‖ℓ‖₂ + q·‖ℓ‖_∞)` (the shape
`Parking.External.UConcentration` carries), for every real `q ≥ 1`, not the Chernoff
tail. -/
theorem weighted_exp_conc_Lq (θ0 K0 : ℝ) (hθ0 : 0 < θ0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun z : ℝ => Real.exp (θ0 * |z|)) ν →
        ∫ z, Real.exp (θ0 * |z|) ∂ν ≤ K0 →
        ∀ F : (Fin N → ℝ) → ℝ, Measurable F →
        ∀ ℓ : Fin N → ℝ, (∀ i, 0 ≤ ℓ i) → (∃ i, ℓ i ≠ 0) →
          (∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
            |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) →
          ∀ q : ℝ, 1 ≤ q →
            (∫ ξ, |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)| ^ q
                ∂(Measure.pi fun _ : Fin N => ν)) ^ (1 / q)
              ≤ C * (Real.sqrt q * lTwoNorm ℓ + q * lInfNorm ℓ) := by
  set Kbig : ℝ := max K0 1 with hKbigDef
  set C0 : ℝ := 16 * (Real.exp Kbig * Kbig) / θ0 ^ 2 with hC0def
  have hC0pos : 0 < C0 := by
    have hM1 : (1:ℝ) ≤ Kbig := le_max_right K0 1
    have hMpos : (0:ℝ) < Kbig := lt_of_lt_of_le one_pos hM1
    rw [hC0def]; positivity
  set Kgen : ℝ := 2 * Real.sqrt 2 * Real.exp (-(1 / 2)) with hKgenDef
  have hKgenPos : 0 < Kgen := by rw [hKgenDef]; positivity
  refine ⟨Kgen * Real.sqrt C0 + 2 * Kgen / θ0, by positivity, ?_⟩
  intro N ν hprob hexp hK F hFm ℓ hℓnn hℓne hLip q hq
  have hSG := subGaussianOn_sub_mean_of_lipschitz θ0 K0 hθ0 N ν hexp hK F hFm ℓ hℓnn hℓne hLip
  have hL0 : 0 < lInfNorm ℓ := lInfNorm_pos ℓ hℓnn hℓne
  have hL2 : 0 < lTwoNorm ℓ := lTwoNorm_pos ℓ hℓnn hℓne
  have hs0pos : 0 < θ0 / (2 * lInfNorm ℓ) := by positivity
  have hcpos : 0 < C0 * lTwoNorm ℓ ^ 2 := by positivity
  have hbound := exists_Lq_moment_bound_of_subGaussianOn
    (Measure.pi fun _ : Fin N => ν) hcpos hs0pos hSG hq
  have hsqrtc : Real.sqrt (C0 * lTwoNorm ℓ ^ 2) = Real.sqrt C0 * lTwoNorm ℓ := by
    rw [Real.sqrt_mul hC0pos.le, Real.sqrt_sq (le_of_lt hL2)]
  rw [hsqrtc] at hbound
  have hqs0 : q / (θ0 / (2 * lInfNorm ℓ)) = 2 / θ0 * q * lInfNorm ℓ := by
    field_simp
  rw [hqs0] at hbound
  have hgoal : Kgen * (Real.sqrt C0 * lTwoNorm ℓ * Real.sqrt q + 2 / θ0 * q * lInfNorm ℓ)
      ≤ (Kgen * Real.sqrt C0 + 2 * Kgen / θ0) * (Real.sqrt q * lTwoNorm ℓ + q * lInfNorm ℓ) := by
    have hexpand : (Kgen * Real.sqrt C0 + 2 * Kgen / θ0) *
        (Real.sqrt q * lTwoNorm ℓ + q * lInfNorm ℓ)
        = Kgen * Real.sqrt C0 * (Real.sqrt q * lTwoNorm ℓ)
          + Kgen * Real.sqrt C0 * (q * lInfNorm ℓ)
          + (2 * Kgen / θ0) * (Real.sqrt q * lTwoNorm ℓ)
          + (2 * Kgen / θ0) * (q * lInfNorm ℓ) := by ring
    rw [hexpand]
    have h1 : (0:ℝ) ≤ Kgen * Real.sqrt C0 * (q * lInfNorm ℓ) := by positivity
    have h2 : (0:ℝ) ≤ (2 * Kgen / θ0) * (Real.sqrt q * lTwoNorm ℓ) := by positivity
    have h3 : Kgen * (Real.sqrt C0 * lTwoNorm ℓ * Real.sqrt q)
        = Kgen * Real.sqrt C0 * (Real.sqrt q * lTwoNorm ℓ) := by ring
    have h4 : Kgen * (2 / θ0 * q * lInfNorm ℓ) = (2 * Kgen / θ0) * (q * lInfNorm ℓ) := by ring
    nlinarith [h1, h2, h3, h4]
  calc (∫ ξ, |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)| ^ q
        ∂(Measure.pi fun _ : Fin N => ν)) ^ (1 / q)
      ≤ Kgen * (Real.sqrt C0 * lTwoNorm ℓ * Real.sqrt q + 2 / θ0 * q * lInfNorm ℓ) := hbound
    _ ≤ (Kgen * Real.sqrt C0 + 2 * Kgen / θ0) *
        (Real.sqrt q * lTwoNorm ℓ + q * lInfNorm ℓ) := hgoal

end Parking

end
