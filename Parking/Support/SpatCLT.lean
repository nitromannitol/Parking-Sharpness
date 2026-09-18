/-
The scalar characteristic-function engine for the finite-dimensional convergence clause of
`prop:spatial-scaling` (`parking.tex:1679-1737`).

`Parking.linPotential` is, for each fixed `n`, EXACTLY linear in the i.i.d. scenery
(`Parking.Support.LinPotentialSum.linPotential_eq_sum`), so any finite linear combination of
values `V_{n_j}(x_j)` is itself a single finitely-supported weighted sum
`∑_w d(w)·η(w)`.  This module transcribes `Parking.Support.TightCLT`'s cosine-product
characteristic-function argument (built for the oriented node's `Site 2`-valued box reward)
to a general `Site d`, since none of the argument — Taylor expansion of the one-site
characteristic function, the logarithm bound, the product-of-characteristic-functions
identity via `iIndepFun_infinitePi`, and the triangular-array assembly — is specific to a
fixed dimension:

- `Parking.spatRealLaw_sq_integral_pos`, `Parking.exists_spatTaylor_charFun_realLaw`,
  `Parking.exists_spatLog_charFun_realLaw`: the one-site variance positivity, the
  quantitative Taylor expansion of `charFun (realLaw ν)` at `0`, and the combined Taylor
  + logarithm bound — none of these three mentions `Site` at all, so they are transcribed
  verbatim from `TightCLT.lean` under new names (the oriented node owns the unqualified
  names).
- `Parking.charFun_map_weighted_sum_eq_prod`: the characteristic function of a
  finitely-supported weighted sum of the i.i.d. scenery over `Site d` is the product, over
  the support, of the one-site characteristic function at the rescaled argument — the
  literal `Site 2 → Site d` generalization, since `ProbabilityTheory.iIndepFun_infinitePi`
  (`Mathlib.Probability.Independence.InfinitePi`) is already stated for a general index
  type.
- `Parking.tendsto_charFun_weighted_scenery_sum`: **the scalar triangular-array central
  limit theorem** this module exists for, general `Site d`.  For a triangular array of
  finite supports and weights whose squares sum to a limit `V` and are uniformly
  negligible, the characteristic function of the weighted i.i.d. sum converges to the
  Gaussian one `exp(-σ²Vt²/2)`.
-/
import Parking.Support.LinPotentialSum
import Parking.Support.CriticalLawReal
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

open MeasureTheory LatticeProb ProbabilityTheory Filter Complex
open scoped Topology RealInnerProductSpace InnerProductSpace

noncomputable section
namespace Parking

/-- The one-site variance `σ² = ∫x² ∂(realLaw ν)` is strictly positive: a vanishing
variance forces a point mass at `0`, contradicting `nonconst`. -/
theorem spatRealLaw_sq_integral_pos (ν : Measure ℤ) (hν : CriticalLaw ν) :
    0 < ∫ x : ℝ, x ^ 2 ∂(realLaw ν) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  have hnn : (0 : ℝ) ≤ ∫ x : ℝ, x ^ 2 ∂(realLaw ν) :=
    integral_nonneg fun x => sq_nonneg x
  rcases hnn.lt_or_eq with hpos | heq
  · exact hpos
  · exfalso
    have hint : Integrable (fun x : ℝ => x ^ 2) (realLaw ν) :=
      (realLaw_memLp_two ν hν).integrable_sq
    have hae : (fun x : ℝ => x ^ 2) =ᵐ[realLaw ν] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg x) hint).mp heq.symm
    have hae0 : (fun x : ℝ => x) =ᵐ[realLaw ν] 0 := by
      filter_upwards [hae] with x hx
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx
    have hcompl : (realLaw ν) {x : ℝ | x ≠ 0} = 0 := by
      have := hae0
      rw [Filter.EventuallyEq, ae_iff] at this
      simpa using this
    have hsingle : (realLaw ν) {(0 : ℝ)} = 1 := by
      have huniv : (realLaw ν) Set.univ = 1 := measure_univ
      have hsplit : (Set.univ : Set ℝ) = {(0 : ℝ)} ∪ {x : ℝ | x ≠ 0} := by
        ext x; by_cases hx : x = 0 <;> simp [hx]
      have hle : (realLaw ν) Set.univ ≤ (realLaw ν) {(0 : ℝ)} + (realLaw ν) {x : ℝ | x ≠ 0} := by
        rw [hsplit]; exact measure_union_le _ _
      rw [huniv, hcompl, add_zero] at hle
      exact le_antisymm (by simpa using prob_le_one) hle
    have hpre : (fun k : ℤ => (k : ℝ)) ⁻¹' {(0 : ℝ)} = ({0} : Set ℤ) := by
      ext k; simp
    have : ν ({0} : Set ℤ) = 1 := by
      rw [← hpre, ← Measure.map_apply measurable_intCastReal (measurableSet_singleton _)]
      exact hsingle
    exact hν.nonconst 0 this

/-- **The quantitative second-order Taylor expansion of the one-site characteristic
function** at `0`, with variance `σ² = ∫x² ∂(realLaw ν)`: for every `ε > 0` there is a
neighborhood of `0` on which `charFun (realLaw ν)` is within `ε·s²` of `1 - σ²s²/2`. -/
theorem exists_spatTaylor_charFun_realLaw (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ →
      ‖charFun (realLaw ν) s -
          (1 - ((∫ x : ℝ, x ^ 2 ∂(realLaw ν) : ℝ) : ℂ) * (s : ℂ) ^ 2 / 2)‖ ≤ ε * s ^ 2 := by
  intro ε hε
  haveI := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  set σ2 : ℝ := ∫ x : ℝ, x ^ 2 ∂(realLaw ν) with hσ2
  have hσ2pos : 0 < σ2 := spatRealLaw_sq_integral_pos ν hν
  set σ : ℝ := Real.sqrt σ2 with hσ
  have hσpos : 0 < σ := Real.sqrt_pos.mpr hσ2pos
  have hσsq : σ ^ 2 = σ2 := Real.sq_sqrt hσ2pos.le
  set X : ℝ → ℝ := fun z => σ⁻¹ * z with hX
  have hXm : AEMeasurable X (realLaw ν) := (continuous_const.mul continuous_id).measurable.aemeasurable
  have hmean : ∫ z : ℝ, z ∂(realLaw ν) = 0 := realLaw_mean ν hν
  have hint2 : Integrable (fun z : ℝ => z ^ 2) (realLaw ν) :=
    (realLaw_memLp_two ν hν).integrable_sq
  have h0 : ∫ z : ℝ, X z ∂(realLaw ν) = 0 := by
    show ∫ z : ℝ, σ⁻¹ * z ∂(realLaw ν) = 0
    rw [integral_const_mul, hmean, mul_zero]
  have h1 : ∫ z : ℝ, (X z) ^ 2 ∂(realLaw ν) = 1 := by
    have heq : ∀ z : ℝ, (X z) ^ 2 = σ⁻¹ ^ 2 * z ^ 2 := by
      intro z; show (σ⁻¹ * z) ^ 2 = σ⁻¹ ^ 2 * z ^ 2; ring
    simp_rw [heq]
    rw [integral_const_mul, ← hσ2]
    rw [inv_pow, hσsq]
    field_simp
  have hTaylor := taylor_charFun_two hXm h0 h1
  rw [Asymptotics.isLittleO_iff] at hTaylor
  have hc : (0 : ℝ) < ε / σ2 := div_pos hε hσ2pos
  obtain ⟨δ', hδ'pos, hδ'⟩ := Metric.eventually_nhds_iff.mp (hTaylor hc)
  refine ⟨δ' / σ, div_pos hδ'pos hσpos, fun s hs => ?_⟩
  have hσs : dist (σ * s) 0 < δ' := by
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos hσpos]
    calc σ * |s| < σ * (δ' / σ) := mul_lt_mul_of_pos_left hs hσpos
      _ = δ' := by field_simp
  have hbound := hδ' hσs
  have heval : charFun ((realLaw ν).map X) (σ * s) - (1 - ((σ * s : ℝ) : ℂ) ^ 2 / 2)
      = charFun (realLaw ν) s - (1 - (σ2 : ℂ) * (s : ℂ) ^ 2 / 2) := by
    have hXfun : X = fun z : ℝ => σ⁻¹ * z := rfl
    rw [hXfun, charFun_map_mul σ⁻¹ (σ * s)]
    have hcancel : σ⁻¹ * (σ * s) = s := by field_simp
    rw [hcancel]
    have hsq : ((σ * s : ℝ) : ℂ) ^ 2 = (σ2 : ℂ) * (s : ℂ) ^ 2 := by
      have hreal : (σ * s) ^ 2 = σ2 * s ^ 2 := by rw [mul_pow, hσsq]
      have hcast := congrArg (fun x : ℝ => (x : ℂ)) hreal
      push_cast at hcast ⊢
      exact hcast
    rw [hsq]
  rw [heval] at hbound
  refine hbound.trans_eq ?_
  rw [Real.norm_eq_abs]
  have : ((σ * s : ℝ)) ^ 2 = σ2 * s ^ 2 := by rw [mul_pow, hσsq]
  rw [this, abs_of_nonneg (by positivity)]
  field_simp [hσ2pos.ne']

/-- **The characteristic function of a finitely-supported weighted sum of the i.i.d.
scenery, over a general `Site d`, is the product of the one-site characteristic function
over the support.** The `Site 2 → Site d` generalization of `Parking.Support.TightCLT`'s
`charFun_map_weighted_sum_eq_prod` (`ProbabilityTheory.iIndepFun_infinitePi` is already
general in the index type). -/
theorem charFun_map_weighted_sum_eq_prod {d : ℕ} (ν : Measure ℤ) (hν : CriticalLaw ν)
    (S : Finset (Site d)) (c : Site d → ℝ) (t : ℝ) :
    charFun ((iidLaw d (realLaw ν)).map (fun η : Site d → ℝ => ∑ w ∈ S, c w * η w)) t
      = ∏ w ∈ S, charFun (realLaw ν) (t * c w) := by
  classical
  haveI := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw d (realLaw ν)) := by unfold iidLaw; infer_instance
  set g : Site d → ℝ → ℂ := fun w b => Complex.exp (((t * c w * b : ℝ) : ℂ) * Complex.I) with hg
  have hgmeas : ∀ w : Site d, Measurable (g w) := fun w =>
    (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
        continuous_const)).measurable
  have hind : iIndepFun (fun (w : Site d) (η : Site d → ℝ) => g w (η w)) (iidLaw d (realLaw ν)) :=
    iIndepFun_infinitePi (Ω := fun _ : Site d => ℝ) (P := fun _ : Site d => realLaw ν)
      (X := fun w b => g w b) (fun w => hgmeas w)
  have hind' := hind.precomp (g := fun w : (S : Finset (Site d)) => (w : Site d))
    Subtype.val_injective
  have hmeas : ∀ w : (S : Finset (Site d)),
      AEStronglyMeasurable (fun η : Site d → ℝ => g (w : Site d) (η (w : Site d)))
        (iidLaw d (realLaw ν)) :=
    fun w => ((hgmeas (w : Site d)).comp (measurable_pi_apply (w : Site d))).aestronglyMeasurable
  have hkey : (∫ η, ∏ w : (S : Finset (Site d)), g (w : Site d) (η (w : Site d))
        ∂(iidLaw d (realLaw ν)))
      = ∏ w : (S : Finset (Site d)), ∫ η, g (w : Site d) (η (w : Site d)) ∂(iidLaw d (realLaw ν)) :=
    hind'.integral_fun_prod_eq_prod_integral hmeas
  have hmap : ∀ w : Site d, (iidLaw d (realLaw ν)).map (fun η : Site d → ℝ => η w) = realLaw ν :=
    fun w => Measure.infinitePi_map_eval _ w
  have hfactor : ∀ w : Site d, ∫ η, g w (η w) ∂(iidLaw d (realLaw ν)) = charFun (realLaw ν) (t * c w) := by
    intro w
    have h1 : (∫ η, g w (η w) ∂(iidLaw d (realLaw ν))) = ∫ b, g w b ∂(realLaw ν) := by
      have hfwd : ∫ b, g w b ∂((iidLaw d (realLaw ν)).map (fun η : Site d → ℝ => η w))
          = ∫ η, g w (η w) ∂(iidLaw d (realLaw ν)) :=
        integral_map (measurable_pi_apply w).aemeasurable (hgmeas w).aestronglyMeasurable
      rw [hmap w] at hfwd
      exact hfwd.symm
    rw [h1]
    have h2 : charFun (realLaw ν) (t * c w) = ∫ b, Complex.exp (((t * c w * b : ℝ) : ℂ) * Complex.I)
        ∂(realLaw ν) := by
      rw [charFun_apply]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      have hib : (⟪b, t * c w⟫_ℝ : ℝ) = t * c w * b := by
        rw [RCLike.inner_apply]
        simp only [starRingEnd_apply, star_trivial]
      show Complex.exp (↑(⟪b, t * c w⟫_ℝ) * Complex.I) = Complex.exp (↑(t * c w * b) * Complex.I)
      rw [hib]
    rw [h2]
  have hcont : Continuous fun x : ℝ => Complex.exp (↑(⟪x, t⟫_ℝ) * Complex.I) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (Continuous.inner continuous_id continuous_const)).mul continuous_const)
  have hchar : charFun ((iidLaw d (realLaw ν)).map (fun η : Site d → ℝ => ∑ w ∈ S, c w * η w)) t
      = ∫ η, ∏ w : (S : Finset (Site d)), g (w : Site d) (η (w : Site d)) ∂(iidLaw d (realLaw ν)) := by
    have hmeasSum : AEMeasurable (fun η : Site d → ℝ => ∑ w ∈ S, c w * η w)
        (iidLaw d (realLaw ν)) :=
      (Finset.measurable_sum S fun w _ =>
        measurable_const.mul (measurable_pi_apply w)).aemeasurable
    calc charFun ((iidLaw d (realLaw ν)).map (fun η : Site d → ℝ => ∑ w ∈ S, c w * η w)) t
        = ∫ x, Complex.exp (↑(⟪x, t⟫_ℝ) * Complex.I)
            ∂((iidLaw d (realLaw ν)).map (fun η : Site d → ℝ => ∑ w ∈ S, c w * η w)) :=
          charFun_apply t
      _ = ∫ η, Complex.exp (↑(⟪(∑ w ∈ S, c w * η w : ℝ), t⟫_ℝ) * Complex.I)
            ∂(iidLaw d (realLaw ν)) :=
          integral_map hmeasSum hcont.aestronglyMeasurable
      _ = ∫ η, ∏ w : (S : Finset (Site d)), g (w : Site d) (η (w : Site d))
            ∂(iidLaw d (realLaw ν)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
          have hinner : (⟪(∑ w ∈ S, c w * η w : ℝ), t⟫_ℝ : ℝ)
              = ∑ w ∈ S, t * c w * η w := by
            rw [RCLike.inner_apply]
            simp only [starRingEnd_apply, star_trivial, Finset.mul_sum]
            refine Finset.sum_congr rfl fun w _ => ?_
            ring
          show Complex.exp (↑(⟪(∑ w ∈ S, c w * η w : ℝ), t⟫_ℝ) * Complex.I)
              = ∏ w : (S : Finset (Site d)), g (w : Site d) (η (w : Site d))
          rw [hinner]
          have hexp : ((↑(∑ w ∈ S, t * c w * η w) : ℂ) * Complex.I)
              = ∑ w ∈ S, ((t * c w * η w : ℝ) : ℂ) * Complex.I := by
            push_cast
            rw [← Finset.sum_mul]
          rw [hexp, Complex.exp_sum, ← Finset.prod_coe_sort S (fun w => g w (η w))]
  rw [hchar, hkey]
  rw [← Finset.prod_coe_sort S (fun w => charFun (realLaw ν) (t * c w))]
  exact Finset.prod_congr rfl fun w _ => hfactor (w : Site d)

theorem exists_spatLog_charFun_realLaw (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ →
      charFun (realLaw ν) s ≠ 0 ∧
      ‖Complex.log (charFun (realLaw ν) s) +
          ((∫ x : ℝ, x ^ 2 ∂(realLaw ν) : ℝ) : ℂ) * (s : ℂ) ^ 2 / 2‖ ≤ ε * s ^ 2 := by
  intro ε hε
  haveI := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  set σ2 : ℝ := ∫ x : ℝ, x ^ 2 ∂(realLaw ν) with hσ2
  have hσ2nonneg : 0 ≤ σ2 := by rw [hσ2]; exact integral_nonneg fun x => sq_nonneg x
  set K : ℝ := σ2 / 2 + 1 with hK
  have hKpos : 0 < K := by rw [hK]; linarith
  set εT : ℝ := min ε 1 / 2 with hεT
  have hεTpos : 0 < εT := by rw [hεT]; positivity
  have hεTle1 : εT ≤ 1 := by
    have h1 : min ε 1 ≤ 1 := min_le_right _ _
    rw [hεT]; linarith
  have hεTlee2 : εT ≤ ε / 2 := by
    have h1 : min ε 1 ≤ ε := min_le_left _ _
    rw [hεT]; linarith
  obtain ⟨δT, hδTpos, hδT⟩ := exists_spatTaylor_charFun_realLaw ν hν εT hεTpos
  set δcap : ℝ := Real.sqrt (1 / (2 * K)) with hδcap
  have hδcappos : 0 < δcap := by rw [hδcap]; positivity
  set δε : ℝ := Real.sqrt (ε / (2 * K ^ 2)) with hδε
  have hδεpos : 0 < δε := by rw [hδε]; positivity
  refine ⟨min δT (min δcap δε), lt_min hδTpos (lt_min hδcappos hδεpos), fun s hs => ?_⟩
  have hsT : |s| < δT := lt_of_lt_of_le hs (min_le_left _ _)
  have hscap : |s| < δcap := lt_of_lt_of_le hs (le_trans (min_le_right _ _) (min_le_left _ _))
  have hsε : |s| < δε := lt_of_lt_of_le hs (le_trans (min_le_right _ _) (min_le_right _ _))
  have hrho := hδT s hsT
  have hs2cap : s ^ 2 < 1 / (2 * K) := by
    have h1 : (0:ℝ) ≤ 1 / (2 * K) := by positivity
    have h2 : |s| < Real.sqrt (1 / (2 * K)) := hscap
    have h3 := (Real.lt_sqrt (abs_nonneg s)).mp h2
    rwa [sq_abs] at h3
  have hs2eps : s ^ 2 < ε / (2 * K ^ 2) := by
    have h1 : (0:ℝ) ≤ ε / (2 * K ^ 2) := by positivity
    have h2 : |s| < Real.sqrt (ε / (2 * K ^ 2)) := hsε
    have h3 := (Real.lt_sqrt (abs_nonneg s)).mp h2
    rwa [sq_abs] at h3
  set z : ℂ := charFun (realLaw ν) s - 1 with hz
  have hzeq : charFun (realLaw ν) s = 1 + z := by rw [hz]; ring
  have hznorm : ‖z‖ ≤ K * s ^ 2 := by
    have hzeq2 : z = -(σ2 : ℂ) * (s : ℂ) ^ 2 / 2 +
        (charFun (realLaw ν) s - (1 - (σ2 : ℂ) * (s : ℂ) ^ 2 / 2)) := by
      rw [hz]; ring
    rw [hzeq2]
    refine (norm_add_le _ _).trans ?_
    have hcast : (-(σ2 : ℂ) * (s : ℂ) ^ 2 / 2) = ((-(σ2 * s ^ 2 / 2) : ℝ) : ℂ) := by
      push_cast; ring
    have h1 : ‖(-(σ2 : ℂ) * (s : ℂ) ^ 2 / 2)‖ = σ2 / 2 * s ^ 2 := by
      rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      have hnn : (0:ℝ) ≤ σ2 * s ^ 2 / 2 := by
        have := mul_nonneg hσ2nonneg (sq_nonneg s)
        linarith
      rw [abs_neg, abs_of_nonneg hnn]
      ring
    rw [h1]
    have h2 : σ2 / 2 * s ^ 2 + εT * s ^ 2 ≤ K * s ^ 2 := by
      have hcoef : σ2 / 2 + εT ≤ K := by rw [hK]; linarith
      nlinarith [sq_nonneg s]
    linarith [hrho]
  have hzhalf : ‖z‖ ≤ 1 / 2 := by
    calc ‖z‖ ≤ K * s ^ 2 := hznorm
      _ ≤ K * (1 / (2 * K)) := mul_le_mul_of_nonneg_left hs2cap.le hKpos.le
      _ = 1 / 2 := by field_simp
  have hzlt1 : ‖z‖ < 1 := lt_of_le_of_lt hzhalf (by norm_num)
  have hne : charFun (realLaw ν) s ≠ 0 := by
    rw [hzeq]
    intro hcontra
    have hzm1 : z = -1 := by linear_combination hcontra
    rw [hzm1] at hzlt1
    simp at hzlt1
  refine ⟨hne, ?_⟩
  have hlogeq : Complex.log (charFun (realLaw ν) s) = z + (Complex.log (1 + z) - z) := by
    rw [hzeq]; ring
  have herr2 : Complex.log (charFun (realLaw ν) s) +
      (σ2 : ℂ) * (s : ℂ) ^ 2 / 2
      = (charFun (realLaw ν) s - (1 - (σ2 : ℂ) * (s : ℂ) ^ 2 / 2)) +
        (Complex.log (1 + z) - z) := by
    rw [hlogeq, hzeq]; ring
  rw [herr2]
  refine (norm_add_le _ _).trans ?_
  have htau : ‖Complex.log (1 + z) - z‖ ≤ (K * s ^ 2) ^ 2 := by
    refine (Complex.norm_log_one_add_sub_self_le hzlt1).trans ?_
    have hinvbound : (1 - ‖z‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2
        ≤ ‖z‖ ^ 2 * 2 / 2 := by
          apply div_le_div_of_nonneg_right ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left hinvbound (sq_nonneg _)
      _ = ‖z‖ ^ 2 := by ring
      _ ≤ (K * s ^ 2) ^ 2 := by
          apply sq_le_sq' (by linarith [norm_nonneg z]) hznorm
  have hsplit : (K * s ^ 2) ^ 2 ≤ ε / 2 * s ^ 2 := by
    have hKs2 : (K * s ^ 2) ^ 2 = (K ^ 2 * s ^ 2) * s ^ 2 := by ring
    rw [hKs2]
    have hbound : K ^ 2 * s ^ 2 ≤ ε / 2 := by
      have hK2pos : (0 : ℝ) < K ^ 2 := by positivity
      have hlt : K ^ 2 * s ^ 2 < K ^ 2 * (ε / (2 * K ^ 2)) :=
        mul_lt_mul_of_pos_left hs2eps hK2pos
      have heq : K ^ 2 * (ε / (2 * K ^ 2)) = ε / 2 := by field_simp
      rw [heq] at hlt
      exact hlt.le
    nlinarith [sq_nonneg s]
  calc ‖charFun (realLaw ν) s - (1 - (σ2 : ℂ) * (s : ℂ) ^ 2 / 2)‖ +
        ‖Complex.log (1 + z) - z‖
      ≤ εT * s ^ 2 + (K * s ^ 2) ^ 2 := add_le_add hrho htau
    _ ≤ ε / 2 * s ^ 2 + ε / 2 * s ^ 2 := by
        have h1 : εT * s ^ 2 ≤ ε / 2 * s ^ 2 :=
          mul_le_mul_of_nonneg_right hεTlee2 (sq_nonneg s)
        linarith [hsplit]
    _ = ε * s ^ 2 := by ring

/-- **The characteristic function of a triangular array of finitely-supported weighted
i.i.d. sums over `Site d` converges to the Gaussian one**, provided the weights' squares
sum to a limit `V` and are uniformly negligible.  This is the scalar triangular-array central
limit theorem behind the finite-dimensional convergence clause of `prop:spatial-scaling`,
for a general `Site d`; it is transcribed from
`Parking.Support.TightCLT.tendsto_charFun_weighted_scenery_sum`. -/
theorem tendsto_charFun_weighted_scenery_sum {d : ℕ} (ν : Measure ℤ) (hν : CriticalLaw ν)
    (S : ℕ → Finset (Site d)) (c : ℕ → Site d → ℝ) (t : ℝ) {V : ℝ}
    (hV : Tendsto (fun n => ∑ w ∈ S n, (c n w) ^ 2) atTop (𝓝 V))
    (M : ℕ → ℝ) (hM : Tendsto M atTop (𝓝 0)) (hMd : ∀ n, ∀ w ∈ S n, |c n w| ≤ M n) :
    Tendsto (fun n : ℕ => charFun ((iidLaw d (realLaw ν)).map
        (fun η : Site d → ℝ => ∑ w ∈ S n, c n w * η w)) t) atTop
      (𝓝 (Complex.exp (-((∫ x : ℝ, x ^ 2 ∂(realLaw ν) : ℝ) : ℂ) * (V : ℂ) * (t : ℂ) ^ 2 / 2))) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  set σ2 : ℝ := ∫ x : ℝ, x ^ 2 ∂(realLaw ν) with hσ2
  have hσ2nonneg : 0 ≤ σ2 := by rw [hσ2]; exact integral_nonneg fun x => sq_nonneg x
  have hprodeq : ∀ n : ℕ, charFun ((iidLaw d (realLaw ν)).map
      (fun η : Site d → ℝ => ∑ w ∈ S n, c n w * η w)) t
      = ∏ w ∈ S n, charFun (realLaw ν) (t * c n w) :=
    fun n => charFun_map_weighted_sum_eq_prod ν hν (S n) (c n) t
  have hVnonneg : 0 ≤ V :=
    ge_of_tendsto' hV (fun n => Finset.sum_nonneg fun w _ => sq_nonneg (c n w))
  have hnegligible : ∀ δ' : ℝ, 0 < δ' → ∀ᶠ n : ℕ in atTop, ∀ w ∈ S n, |t * c n w| < δ' := by
    intro δ' hδ'pos
    rcases eq_or_ne t 0 with ht0 | ht0
    · filter_upwards [] with n w _
      simp [ht0, hδ'pos]
    · have hδt : (0 : ℝ) < δ' / |t| := by positivity
      filter_upwards [hM.eventually (eventually_lt_nhds hδt)] with n hn w hw
      have h1 : |t * c n w| ≤ |t| * M n := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hMd n w hw) (abs_nonneg t)
      have h2 : |t| * M n < |t| * (δ' / |t|) :=
        mul_lt_mul_of_pos_left hn (abs_pos.mpr ht0)
      have h3 : |t| * (δ' / |t|) = δ' := by field_simp
      linarith
  have hLsum : Tendsto (fun n : ℕ => ∑ w ∈ S n, Complex.log (charFun (realLaw ν) (t * c n w)))
      atTop (𝓝 (-(σ2 : ℂ) * (V : ℂ) * (t : ℂ) ^ 2 / 2)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set B : ℝ := t ^ 2 * (V + 1) + 1 with hB
    have hBpos : 0 < B := by
      rw [hB]; nlinarith [sq_nonneg t, hVnonneg]
    set ε' : ℝ := ε / (2 * B) with hε'
    have hε'pos : 0 < ε' := by rw [hε']; positivity
    obtain ⟨δ, hδpos, hδ⟩ := exists_spatLog_charFun_realLaw ν hν ε' hε'pos
    have hMev : ∀ᶠ n : ℕ in atTop, ∀ w ∈ S n, |t * c n w| < δ := hnegligible δ hδpos
    set D : ℝ := σ2 * t ^ 2 / 2 with hD
    have hDnonneg : 0 ≤ D := by rw [hD]; nlinarith [hσ2nonneg, sq_nonneg t]
    have hDp1pos : 0 < D + 1 := by linarith
    set C : ℝ := min (ε / 2 / (D + 1)) 1 with hC
    have hCpos : 0 < C := by
      rw [hC]; exact lt_min (div_pos (by linarith) hDp1pos) (by norm_num)
    have hCleD1 : C ≤ ε / 2 / (D + 1) := by rw [hC]; exact min_le_left _ _
    have hCle1 : C ≤ 1 := by rw [hC]; exact min_le_right _ _
    have hVclose : ∀ᶠ n : ℕ in atTop, |∑ w ∈ S n, (c n w) ^ 2 - V| < C := by
      have h := Metric.tendsto_nhds.mp hV C hCpos
      filter_upwards [h] with n hn
      rwa [Real.dist_eq] at hn
    filter_upwards [hMev, hVclose] with n hn hCn
    have hVn : ∑ w ∈ S n, (c n w) ^ 2 ≤ V + 1 := by
      have := (abs_lt.mp hCn).2
      linarith
    have herrbound : ∀ w ∈ S n,
        ‖Complex.log (charFun (realLaw ν) (t * c n w)) +
            (σ2 : ℂ) * ((t * c n w : ℝ) : ℂ) ^ 2 / 2‖
          ≤ ε' * (t * c n w) ^ 2 :=
      fun w hw => (hδ (t * c n w) (hn w hw)).2
    have hsumerr : ‖∑ w ∈ S n, (Complex.log (charFun (realLaw ν) (t * c n w)) +
          (σ2 : ℂ) * ((t * c n w : ℝ) : ℂ) ^ 2 / 2)‖ ≤ ε' * t ^ 2 * ∑ w ∈ S n, (c n w) ^ 2 := by
      calc ‖∑ w ∈ S n, (Complex.log (charFun (realLaw ν) (t * c n w)) +
              (σ2 : ℂ) * ((t * c n w : ℝ) : ℂ) ^ 2 / 2)‖
          ≤ ∑ w ∈ S n, ‖Complex.log (charFun (realLaw ν) (t * c n w)) +
              (σ2 : ℂ) * ((t * c n w : ℝ) : ℂ) ^ 2 / 2‖ := norm_sum_le _ _
        _ ≤ ∑ w ∈ S n, ε' * (t * c n w) ^ 2 := Finset.sum_le_sum herrbound
        _ = ε' * t ^ 2 * ∑ w ∈ S n, (c n w) ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun w _ => ?_
            ring
    have hsumdecomp : (∑ w ∈ S n, Complex.log (charFun (realLaw ν) (t * c n w)))
        + (σ2 : ℂ) * (t : ℂ) ^ 2 / 2 * (∑ w ∈ S n, ((c n w : ℂ)) ^ 2)
        = ∑ w ∈ S n, (Complex.log (charFun (realLaw ν) (t * c n w)) +
            (σ2 : ℂ) * ((t * c n w : ℝ) : ℂ) ^ 2 / 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun w _ => ?_
      push_cast
      ring
    have hsumcast : (∑ w ∈ S n, ((c n w : ℂ)) ^ 2) = ((∑ w ∈ S n, (c n w) ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [Complex.dist_eq]
    have hfinalbound : ‖(∑ w ∈ S n, Complex.log (charFun (realLaw ν) (t * c n w))) -
        (-(σ2 : ℂ) * (V : ℂ) * (t : ℂ) ^ 2 / 2)‖
        ≤ ε' * t ^ 2 * ∑ w ∈ S n, (c n w) ^ 2 +
          σ2 * t ^ 2 / 2 * |∑ w ∈ S n, (c n w) ^ 2 - V| := by
      have hrewrite : (∑ w ∈ S n, Complex.log (charFun (realLaw ν) (t * c n w))) -
          (-(σ2 : ℂ) * (V : ℂ) * (t : ℂ) ^ 2 / 2)
          = (∑ w ∈ S n, (Complex.log (charFun (realLaw ν) (t * c n w)) +
              (σ2 : ℂ) * ((t * c n w : ℝ) : ℂ) ^ 2 / 2)) -
            (σ2 : ℂ) * (t : ℂ) ^ 2 / 2 * (((∑ w ∈ S n, (c n w) ^ 2 : ℝ) : ℂ) - (V : ℂ)) := by
        rw [← hsumdecomp, ← hsumcast]
        ring
      rw [hrewrite]
      refine (norm_sub_le _ _).trans ?_
      refine add_le_add hsumerr ?_
      have hcast2 : ((σ2 : ℂ) * (t : ℂ) ^ 2 / 2 *
          (((∑ w ∈ S n, (c n w) ^ 2 : ℝ) : ℂ) - (V : ℂ)))
          = (((σ2 * t ^ 2 / 2 * (∑ w ∈ S n, (c n w) ^ 2 - V) : ℝ)) : ℂ) := by
        push_cast; ring
      rw [hcast2, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have hnn : (0:ℝ) ≤ σ2 * t ^ 2 / 2 := by nlinarith [hσ2nonneg, sq_nonneg t]
      rw [abs_of_nonneg hnn]
    refine lt_of_le_of_lt hfinalbound ?_
    have h1 : ε' * t ^ 2 * ∑ w ∈ S n, (c n w) ^ 2 ≤ ε' * B := by
      have hε'nn : 0 ≤ ε' := hε'pos.le
      have ht2nn : 0 ≤ t ^ 2 := sq_nonneg t
      calc ε' * t ^ 2 * ∑ w ∈ S n, (c n w) ^ 2 ≤ ε' * t ^ 2 * (V + 1) := by
            apply mul_le_mul_of_nonneg_left hVn (by positivity)
        _ ≤ ε' * B := by rw [hB]; nlinarith
    have h2 : σ2 * t ^ 2 / 2 * |∑ w ∈ S n, (c n w) ^ 2 - V| < ε / 2 := by
      rw [← hD]
      calc D * |∑ w ∈ S n, (c n w) ^ 2 - V| ≤ D * C :=
            mul_le_mul_of_nonneg_left hCn.le hDnonneg
        _ ≤ D * (ε / 2 / (D + 1)) := mul_le_mul_of_nonneg_left hCleD1 hDnonneg
        _ < ε / 2 := by
            rw [mul_div_assoc', div_lt_iff₀ hDp1pos]
            nlinarith [hε]
    have h3 : ε' * B = ε / 2 := by
      rw [hε']; field_simp
    linarith [h1, h2, h3.le]
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := exists_spatLog_charFun_realLaw ν hν 1 one_pos
  have hne_ev : ∀ᶠ n : ℕ in atTop, ∀ w ∈ S n, charFun (realLaw ν) (t * c n w) ≠ 0 := by
    filter_upwards [hnegligible δ₁ hδ₁pos] with n hn w hw
    exact (hδ₁ (t * c n w) (hn w hw)).1
  have hprodexp : (fun n : ℕ => ∏ w ∈ S n, charFun (realLaw ν) (t * c n w)) =ᶠ[atTop]
      (fun n : ℕ => Complex.exp (∑ w ∈ S n, Complex.log (charFun (realLaw ν) (t * c n w)))) := by
    filter_upwards [hne_ev] with n hn
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun w hw => (Complex.exp_log (hn w hw)).symm
  have hexpconv : Tendsto (fun n : ℕ => Complex.exp
      (∑ w ∈ S n, Complex.log (charFun (realLaw ν) (t * c n w)))) atTop
      (𝓝 (Complex.exp (-(σ2 : ℂ) * (V : ℂ) * (t : ℂ) ^ 2 / 2))) :=
    (Complex.continuous_exp.tendsto _).comp hLsum
  have hprodconv : Tendsto (fun n : ℕ => ∏ w ∈ S n, charFun (realLaw ν) (t * c n w)) atTop
      (𝓝 (Complex.exp (-(σ2 : ℂ) * (V : ℂ) * (t : ℂ) ^ 2 / 2))) :=
    hexpconv.congr' hprodexp.symm
  exact hprodconv.congr' (Filter.Eventually.of_forall fun n => (hprodeq n).symm)

end Parking

end
