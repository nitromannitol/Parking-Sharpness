/-
Finite-dimensional distributions of the rescaled oriented walk
(`parking.tex:3175-3196`): this is the `hWalk` hypothesis of
`Parking.tendsto_integral_orientedCutoffValue`.

The oriented walk subtracts a unit vector per step, so the projected walk
`z ↦ z 1 - z 0` is a simple symmetric one-dimensional walk driven by the
coordinate part of the direction sequence: the Bool part never enters
`orientedPath`.  Its rescaling by `2√n`, read at the finitely many times
`⌊n * tᵢ⌋₊`, converges in finite-dimensional distributions to any
quarter-Brownian motion `B` (a process with `2B` a standard Brownian motion,
i.e. `Var(B_t) = t/4`).

The proof is Lévy's continuity theorem on `EuclideanSpace ℝ (Fin m)`:
`Parking.charFun_walkFddLaw` computes the walk characteristic function as the
cosine product of the symmetric ±1 steps,
`Parking.tendsto_charFun_walkFddLaw` takes the logarithm and uses
`log cos x = -x²/2 + o(x²)`, and `Parking.charFun_brownianFdd` computes the
Gaussian limit through `HasGaussianLaw.charFun_map_eq`.
-/

import Parking.Support.ContOrientedLimit
import Parking.Support.Pathwise
import Parking.Support.OrientedScaling
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

open LatticeProb Finset MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal RealInnerProductSpace InnerProductSpace Topology

noncomputable section

namespace Parking

/-- The change of the coordinate difference `z 1 - z 0` of a site of `ℤ²` when
the oriented walk subtracts `unit c`: `+1` for `c = 0` and `-1` for `c = 1`. -/
def walkStepSign (c : Fin 2) : ℝ := if c = 0 then 1 else -1

theorem walkStepSign_eq_unit_sub (c : Fin 2) :
    walkStepSign c
      = ((LatticeProb.unit c : Site 2) 0 : ℝ) - ((LatticeProb.unit c : Site 2) 1 : ℝ) := by
  fin_cases c <;> simp [walkStepSign, LatticeProb.unit]

/-- The coordinate difference of the oriented path is the sum of the step signs. -/
theorem orientedPath_coord_sub (k : ℕ) (p : ℕ → Fin 2 × Bool) :
    ((orientedPath (0 : Site 2) p k : Site 2) 1 : ℝ)
        - ((orientedPath (0 : Site 2) p k : Site 2) 0 : ℝ)
      = ∑ j ∈ Finset.range k, walkStepSign (p j).1 := by
  induction k with
  | zero => simp [orientedPath]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    show ((orientedPath (0 : Site 2) p k - unit (p k).1 : Site 2) 1 : ℝ)
        - ((orientedPath (0 : Site 2) p k - unit (p k).1 : Site 2) 0 : ℝ)
        = _ + walkStepSign (p k).1
    have h := walkStepSign_eq_unit_sub (p k).1
    simp only [Pi.sub_apply]
    push_cast
    linarith

/-- The rescaled oriented walk read at the times `⌊n * ts i⌋₊`. -/
def walkFddVec (m : ℕ) (n : ℕ) (ts : Fin m → ℝ) (p : ℕ → Fin 2 × Bool) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => orientedScaledSite n (orientedPath (0 : Site 2) p ⌊(n : ℝ) * ts i⌋₊))

theorem measurable_walkFddVec (m n : ℕ) (ts : Fin m → ℝ) : Measurable (walkFddVec m n ts) := by
  have hv : Measurable (fun (p : ℕ → Fin 2 × Bool) (i : Fin m) =>
      orientedScaledSite n (orientedPath (0 : Site 2) p ⌊(n : ℝ) * ts i⌋₊)) :=
    measurable_pi_lambda _ fun i =>
      measurable_of_finite_dependence (d := 2) (by norm_num) _ _
        (fun p q hpq => by rw [orientedPath_congr (0 : Site 2) _ (fun j hj => hpq j hj)])
  exact (PiLp.continuous_toLp 2 _).measurable.comp hv

/-- The law of the rescaled walk vector. -/
def walkFddLaw (m n : ℕ) (ts : Fin m → ℝ) : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)) :=
  ⟨(walkLaw 2).map (walkFddVec m n ts), by
    haveI := stepLaw_isProbability (d := 2) (by norm_num)
    haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
    exact Measure.isProbabilityMeasure_map (measurable_walkFddVec m n ts).aemeasurable⟩

end Parking

end

namespace Parking

/-- The characteristic integral of one step: averaging `e^{i x σ}` over the
symmetric sign `σ` gives `cos x`. -/
theorem integral_stepLaw_cexp (x : ℝ) :
    ∫ b : Fin 2 × Bool, Complex.exp (((x * walkStepSign b.1 : ℝ) : ℂ) * Complex.I) ∂(stepLaw 2)
      = (Real.cos x : ℂ) := by
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  have hfin : ∀ b : Fin 2 × Bool,
      Integrable (fun b' => Complex.exp (((x * walkStepSign b'.1 : ℝ) : ℂ) * Complex.I))
        (Measure.dirac b) := fun b => integrable_dirac (by simp)
  rw [stepLaw, integral_smul_measure, integral_finsetSum_measure (fun b _ => hfin b)]
  simp only [integral_dirac]
  rw [Complex.real_smul, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fintype.sum_bool, walkStepSign, Fin.isValue, ↓reduceIte]
  rw [ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  push_cast
  simp only [mul_one, mul_neg_one]
  rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  have h4 : ((2 : ℂ) * 2)⁻¹ = 1 / 4 := by norm_num
  rw [h4]
  ring

/-- The characteristic function of the rescaled walk vector is the cosine
product of its symmetric `±1` steps: the coefficient of step `j` is
`Λⱼ = ∑_{i : j < ⌊n tᵢ⌋₊} uᵢ`. -/
theorem charFun_walkFddLaw (m : ℕ) (ts : Fin m → ℝ) {T : ℝ}
    (hts : ∀ i, ts i ∈ Set.Icc (0 : ℝ) T) (n : ℕ) (u : EuclideanSpace ℝ (Fin m)) :
    charFun ((walkFddLaw m n ts : ProbabilityMeasure (EuclideanSpace ℝ (Fin m))) :
        Measure (EuclideanSpace ℝ (Fin m))) u
      = ∏ j ∈ Finset.range ⌊(n : ℝ) * T⌋₊,
          (Real.cos ((∑ i : Fin m, (if j < ⌊(n : ℝ) * ts i⌋₊ then u i else 0))
            / (2 * Real.sqrt (n : ℝ))) : ℂ) := by
  classical
  haveI := stepLaw_isProbability (d := 2) (by norm_num)
  haveI : IsProbabilityMeasure (walkLaw 2) := by unfold walkLaw; infer_instance
  set k : Fin m → ℕ := fun i => ⌊(n : ℝ) * ts i⌋₊ with hk
  set K : ℕ := ⌊(n : ℝ) * T⌋₊ with hK
  set c : ℝ := 2 * Real.sqrt (n : ℝ) with hc
  set Λ : ℕ → ℝ := fun j => ∑ i : Fin m, if j < k i then u i else 0 with hΛ
  set g : ℕ → Fin 2 × Bool → ℂ :=
    fun j b => Complex.exp (((Λ j * walkStepSign b.1 / c : ℝ) : ℂ) * Complex.I) with hg
  have hkK : ∀ i, k i ≤ K := fun i =>
    Nat.floor_mono (mul_le_mul_of_nonneg_left (hts i).2 (Nat.cast_nonneg n))
  have hinner : ∀ p : ℕ → Fin 2 × Bool,
      ⟪walkFddVec m n ts p, u⟫_ℝ = (∑ j ∈ Finset.range K, Λ j * walkStepSign (p j).1) / c := by
    intro p
    have hcoord : ∀ i : Fin m, ⟪(walkFddVec m n ts p) i, u i⟫_ℝ
        = (u i * ∑ j ∈ Finset.range (k i), walkStepSign (p j).1) / c := by
      intro i
      have h1 : (walkFddVec m n ts p) i
          = orientedScaledSite n (orientedPath (0 : Site 2) p (k i)) := rfl
      rw [h1]
      show ⟪(((orientedPath (0 : Site 2) p (k i) : Site 2) 1 : ℝ)
            - ((orientedPath (0 : Site 2) p (k i) : Site 2) 0 : ℝ)) / (2 * Real.sqrt (n : ℝ)),
            u i⟫_ℝ = _
      rw [orientedPath_coord_sub, RCLike.inner_apply]
      simp only [starRingEnd_apply, star_trivial]
      rw [hc]
      ring
    have hswap : (∑ i : Fin m, u i * ∑ j ∈ Finset.range (k i), walkStepSign (p j).1)
        = ∑ j ∈ Finset.range K, Λ j * walkStepSign (p j).1 := by
      calc ∑ i : Fin m, u i * ∑ j ∈ Finset.range (k i), walkStepSign (p j).1
          = ∑ i : Fin m, ∑ j ∈ Finset.range K,
              if j < k i then u i * walkStepSign (p j).1 else 0 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            calc ∑ j ∈ Finset.range (k i), u i * walkStepSign (p j).1
                = ∑ j ∈ Finset.range (k i),
                    (if j < k i then u i * walkStepSign (p j).1 else 0) := by
                  refine Finset.sum_congr rfl fun j hj => ?_
                  rw [Finset.mem_range] at hj
                  exact (if_pos hj).symm
              _ = ∑ j ∈ Finset.range K,
                    (if j < k i then u i * walkStepSign (p j).1 else 0) := by
                  refine Finset.sum_subset (Finset.range_mono (hkK i)) fun j hjK hjki => ?_
                  rw [Finset.mem_range] at hjki
                  exact if_neg hjki
        _ = ∑ j ∈ Finset.range K, ∑ i : Fin m,
              if j < k i then u i * walkStepSign (p j).1 else 0 := Finset.sum_comm
        _ = ∑ j ∈ Finset.range K, Λ j * walkStepSign (p j).1 := by
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [hΛ]
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            split_ifs <;> ring
    rw [PiLp.inner_apply, Finset.sum_congr rfl (fun i _ => hcoord i), ← Finset.sum_div, hswap]
  have hmap : ∀ j : ℕ, (walkLaw 2).map (fun p : ℕ → Fin 2 × Bool => p j) = stepLaw 2 :=
    fun j => Measure.infinitePi_map_eval _ _
  have hfactor : ∀ j : Fin K, ∫ p, g (j : ℕ) (p j) ∂(walkLaw 2) = (Real.cos (Λ j / c) : ℂ) := by
    intro j
    have hgmeas : Measurable (g (j : ℕ)) := Measurable.of_discrete
    have h1 : (∫ p, g (j : ℕ) (p j) ∂(walkLaw 2))
        = ∫ b, g (j : ℕ) b ∂(stepLaw 2) := by
      rw [← hmap (j : ℕ)]
      exact (integral_map (measurable_pi_apply _).aemeasurable hgmeas.aestronglyMeasurable).symm
    rw [h1]
    have h2 : ∀ b : Fin 2 × Bool, g (j : ℕ) b
        = Complex.exp ((((Λ j / c) * walkStepSign b.1 : ℝ) : ℂ) * Complex.I) := by
      intro b
      have hrw : (Λ (j : ℕ) * walkStepSign b.1 / c : ℝ) = (Λ (j : ℕ) / c) * walkStepSign b.1 := by
        ring
      simp only [hg, hrw]
    simp_rw [h2]
    exact integral_stepLaw_cexp (Λ (j : ℕ) / c)
  have hIndep : (∫ p, ∏ j ∈ Finset.range K, g j (p j) ∂(walkLaw 2))
      = ∏ j ∈ Finset.range K, ∫ p, g j (p j) ∂(walkLaw 2) := by
    have hind : iIndepFun (fun (j : ℕ) (p : ℕ → Fin 2 × Bool) => g j (p j)) (walkLaw 2) :=
      iIndepFun_infinitePi (X := fun (j : ℕ) (b : Fin 2 × Bool) => g j b)
        (fun _ => Measurable.of_discrete)
    have hind' := hind.precomp (g := fun j : Fin K => (j : ℕ)) Fin.val_injective
    have hmeas : ∀ j : Fin K,
        AEStronglyMeasurable (fun p : ℕ → Fin 2 × Bool => g (j : ℕ) (p (j : ℕ)))
          (walkLaw 2) :=
      fun j => ((Measurable.of_discrete (f := g (j : ℕ))).comp
        (measurable_pi_apply _)).aestronglyMeasurable
    have keyL : (∫ p, ∏ j : Fin K, g (j : ℕ) (p (j : ℕ)) ∂(walkLaw 2))
        = ∏ j : Fin K, ∫ p, g (j : ℕ) (p (j : ℕ)) ∂(walkLaw 2) :=
      hind'.integral_fun_prod_eq_prod_integral hmeas
    calc ∫ p, ∏ j ∈ Finset.range K, g j (p j) ∂(walkLaw 2)
        = ∫ p, ∏ j : Fin K, g (j : ℕ) (p (j : ℕ)) ∂(walkLaw 2) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          exact (Fin.prod_univ_eq_prod_range (fun j => g j (p j)) K).symm
      _ = ∏ j : Fin K, ∫ p, g (j : ℕ) (p (j : ℕ)) ∂(walkLaw 2) := keyL
      _ = ∏ j ∈ Finset.range K, ∫ p, g j (p j) ∂(walkLaw 2) :=
          Fin.prod_univ_eq_prod_range (fun j => ∫ p, g j (p j) ∂(walkLaw 2)) K
  have hcont : Continuous
      fun x : EuclideanSpace ℝ (Fin m) => Complex.exp (↑(⟪x, u⟫_ℝ) * Complex.I) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (Continuous.inner continuous_id continuous_const)).mul continuous_const)
  show charFun ((walkLaw 2).map (walkFddVec m n ts)) u = _
  calc charFun ((walkLaw 2).map (walkFddVec m n ts)) u
      = ∫ x : EuclideanSpace ℝ (Fin m), Complex.exp (↑(⟪x, u⟫_ℝ) * Complex.I)
          ∂((walkLaw 2).map (walkFddVec m n ts)) := charFun_apply u
    _ = ∫ p, Complex.exp (↑(⟪walkFddVec m n ts p, u⟫_ℝ) * Complex.I) ∂(walkLaw 2) :=
        integral_map (measurable_walkFddVec m n ts).aemeasurable hcont.aestronglyMeasurable
    _ = ∫ p, ∏ j ∈ Finset.range K, g j (p j) ∂(walkLaw 2) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        show Complex.exp (↑(⟪walkFddVec m n ts p, u⟫_ℝ) * Complex.I)
            = ∏ j ∈ Finset.range K, g j (p j)
        rw [hinner p]
        have hexp : ((↑((∑ j ∈ Finset.range K, Λ j * walkStepSign (p j).1) / c) : ℂ) * Complex.I)
            = ∑ j ∈ Finset.range K, ((Λ j * walkStepSign (p j).1 / c : ℝ) : ℂ) * Complex.I := by
          push_cast
          rw [← Finset.sum_mul, Finset.sum_div]
        rw [hexp, Complex.exp_sum]
    _ = ∏ j ∈ Finset.range K, ∫ p, g j (p j) ∂(walkLaw 2) := hIndep
    _ = ∏ j : Fin K, (Real.cos (Λ (j : ℕ) / c) : ℂ) := by
        rw [← Fin.prod_univ_eq_prod_range (fun j => ∫ p, g j (p j) ∂(walkLaw 2)) K]
        exact Finset.prod_congr rfl fun j _ => hfactor j
    _ = ∏ j ∈ Finset.range K,
          (Real.cos ((∑ i : Fin m, if j < ⌊(n : ℝ) * ts i⌋₊ then u i else 0)
            / (2 * Real.sqrt (n : ℝ))) : ℂ) :=
        Fin.prod_univ_eq_prod_range
          (fun j => (Real.cos ((∑ i : Fin m, if j < ⌊(n : ℝ) * ts i⌋₊ then u i else 0)
            / (2 * Real.sqrt (n : ℝ))) : ℂ)) K

/-- The normalized floor `⌊n * s⌋₊ / n` converges to `s`. -/
theorem tendsto_nat_floor_div (s : ℝ) (hs : 0 ≤ s) :
    Tendsto (fun n : ℕ => (⌊(n : ℝ) * s⌋₊ : ℝ) / n) atTop (𝓝 s) := by
  have h1 : Tendsto (fun n : ℕ => s - (1 : ℝ) / n) atTop (𝓝 (s - 0)) :=
    tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat
  rw [sub_zero] at h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hn0' : (n : ℝ) ≠ 0 := hn0.ne'
    rw [le_div_iff₀ hn0]
    have h := Nat.lt_floor_add_one ((n : ℝ) * s)
    calc (s - 1 / (n : ℝ)) * (n : ℝ) = (n : ℝ) * s - 1 := by
          rw [sub_mul, one_div_mul_cancel hn0']; ring
      _ ≤ ⌊(n : ℝ) * s⌋₊ := by rw [sub_le_iff_le_add]; exact h.le
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [div_le_iff₀ hn0]
    calc (⌊(n : ℝ) * s⌋₊ : ℝ) ≤ (n : ℝ) * s :=
          Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) hs)
      _ = s * n := by ring

/-- Squaring the step coefficient `Λⱼ` and summing over `j` counts, for each pair
`(i, l)`, the number `min (k i) (k l)` of steps below both cutoffs. -/
theorem sum_sq_indicator {m : ℕ} (u : Fin m → ℝ) (k : Fin m → ℕ) (K : ℕ)
    (hK : ∀ i, k i ≤ K) :
    ∑ j ∈ Finset.range K, (∑ i : Fin m, if j < k i then u i else 0) ^ 2
      = ∑ i : Fin m, ∑ l : Fin m, u i * u l * (min (k i) (k l) : ℝ) := by
  simp only [pow_two]
  have step1 : ∑ j ∈ Finset.range K, (∑ i : Fin m, if j < k i then u i else 0)
        * (∑ l : Fin m, if j < k l then u l else 0)
      = ∑ j ∈ Finset.range K, ∑ i : Fin m, ∑ l : Fin m,
        (if j < k i then u i else 0) * (if j < k l then u l else 0) :=
    Finset.sum_congr rfl fun j _ => Fintype.sum_mul_sum _ _
  rw [step1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hite : ∀ j : ℕ, (if j < k i then u i else 0) * (if j < k l then u l else 0)
      = if j < min (k i) (k l) then u i * u l else 0 := by
    intro j
    by_cases h : j < min (k i) (k l)
    · rw [if_pos h]
      rw [lt_min_iff] at h
      rw [if_pos h.1, if_pos h.2]
    · rw [if_neg h]
      rw [lt_min_iff, not_and] at h
      by_cases hi : j < k i
      · rw [if_pos hi, if_neg (h hi), mul_zero]
      · rw [if_neg hi, zero_mul]
  have hfilter : (Finset.range K).filter (fun j => j < min (k i) (k l))
      = Finset.range (min K (min (k i) (k l))) := by
    ext j
    simp
  calc ∑ j ∈ Finset.range K, (if j < k i then u i else 0) * (if j < k l then u l else 0)
      = ∑ j ∈ Finset.range K, if j < min (k i) (k l) then u i * u l else 0 :=
        Finset.sum_congr rfl fun j _ => hite j
    _ = ∑ j ∈ (Finset.range K).filter (fun j => j < min (k i) (k l)), u i * u l := by
        rw [Finset.sum_filter]
    _ = ∑ j ∈ Finset.range (min K (min (k i) (k l))), u i * u l := by rw [hfilter]
    _ = (Finset.range (min K (min (k i) (k l)))).card • (u i * u l) := Finset.sum_const _
    _ = (min (k i) (k l) : ℝ) * (u i * u l) := by
        rw [Finset.card_range, nsmul_eq_mul,
          min_eq_right (le_trans (min_le_left _ _) (hK i)), Nat.cast_min]
    _ = u i * u l * (min (k i) (k l) : ℝ) := by ring

/-- The relative error in `log (cos x) = -x²/2 + o(x²)`, filled in by `0` at `x = 0`
to make it continuous there. -/
noncomputable def logCosEps (x : ℝ) : ℝ :=
  Function.update (fun x : ℝ => (Real.log (Real.cos x) + x ^ 2 / 2) / x ^ 2) 0 0 x

/-- The slope of `sin` at `0` tends to `1`. -/
theorem tendsto_sin_div : Tendsto (fun x : ℝ => Real.sin x / x) (𝓝[≠] 0) (𝓝 1) := by
  have h := hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_sin 0)
  rw [Real.cos_zero] at h
  have hslope_eq : slope Real.sin 0 = fun x : ℝ => Real.sin x / x := by
    funext x
    rw [slope_def_field, Real.sin_zero, sub_zero, sub_zero]
  rwa [hslope_eq] at h

/-- Halving preserves the punctured neighborhood of `0`. -/
theorem tendsto_half_punctured : Tendsto (fun x : ℝ => x / 2) (𝓝[≠] (0 : ℝ)) (𝓝[≠] 0) := by
  have h0 : Tendsto (fun x : ℝ => x / 2) (𝓝 0) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => x / 2) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) / 2)) :=
      (continuous_id'.div continuous_const fun _ => two_ne_zero).tendsto 0
    rwa [zero_div] at h
  have h1 : Tendsto (fun x : ℝ => x / 2) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    h0.mono_left nhdsWithin_le_nhds
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1 ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact div_ne_zero hx two_ne_zero

/-- `(1 - cos x) / x² → 1/2` on the punctured neighborhood of `0`. -/
theorem tendsto_one_sub_cos_div_sq :
    Tendsto (fun x : ℝ => (1 - Real.cos x) / x ^ 2) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  have hid : ∀ x : ℝ, 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    intro x
    have h1 : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
      have h := Real.cos_two_mul (x / 2)
      have hx2 : (2 : ℝ) * (x / 2) = x := by ring
      rwa [hx2] at h
    rw [h1]
    have h2 := Real.sin_sq (x / 2)
    linarith
  have hdecomp : (fun x : ℝ => (1 / 2) * (Real.sin (x / 2) / (x / 2)) ^ 2)
      =ᶠ[𝓝[≠] 0] (fun x : ℝ => (1 - Real.cos x) / x ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := hx
    have hx2 : x / 2 ≠ 0 := div_ne_zero hx0 two_ne_zero
    rw [hid]
    field_simp
  have hlim : Tendsto (fun x : ℝ => (1 / 2) * (Real.sin (x / 2) / (x / 2)) ^ 2)
      (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    have h := ((tendsto_sin_div.comp tendsto_half_punctured).pow 2).const_mul (1 / 2)
    rwa [one_pow, mul_one] at h
  exact Tendsto.congr' hdecomp hlim

/-- `-log(1 - y)/y → 1` on the punctured neighborhood of `0`. -/
theorem tendsto_neg_log_one_sub_div :
    Tendsto (fun y : ℝ => -Real.log (1 - y) / y) (𝓝[≠] 0) (𝓝 1) := by
  have hderiv : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1) 0 := by
    have h1 : HasDerivAt (fun y : ℝ => 1 - y) (0 - 1) 0 :=
      (hasDerivAt_const (c := (1 : ℝ)) (x := 0)).sub (hasDerivAt_id' (x := 0))
    simpa using h1.log (by norm_num : (1 : ℝ) - 0 ≠ 0)
  have h := hasDerivAt_iff_tendsto_slope.mp hderiv
  have hslope_eq : slope (fun y : ℝ => Real.log (1 - y)) 0
      = fun y : ℝ => Real.log (1 - y) / y := by
    funext y
    rw [slope_def_field]
    show (Real.log (1 - y) - Real.log (1 - 0)) / (y - 0) = _
    rw [sub_zero, sub_zero, Real.log_one, sub_zero]
  rw [hslope_eq] at h
  have hneg := h.neg
  rw [neg_neg] at hneg
  simpa only [neg_div] using hneg

/-- `1 - cos` preserves the punctured neighborhood of `0`. -/
theorem tendsto_one_sub_cos_punctured :
    Tendsto (fun x : ℝ => 1 - Real.cos x) (𝓝[≠] (0 : ℝ)) (𝓝[≠] 0) := by
  have h0 : Tendsto (fun x : ℝ => 1 - Real.cos x) (𝓝 0) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => 1 - Real.cos x) (𝓝 (0 : ℝ)) (𝓝 (1 - Real.cos 0)) :=
      (continuous_const.sub Real.continuous_cos).tendsto 0
    rwa [Real.cos_zero, sub_self] at h
  have h1 : Tendsto (fun x : ℝ => 1 - Real.cos x) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    h0.mono_left nhdsWithin_le_nhds
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1 ?_
  have hball : ∀ᶠ x in 𝓝[≠] (0 : ℝ), |x| < 2 * Real.pi := by
    have h : Metric.ball (0 : ℝ) (2 * Real.pi) ∈ 𝓝 0 :=
      Metric.ball_mem_nhds 0 (by positivity)
    have hb : ∀ᶠ x in 𝓝 (0 : ℝ), x ∈ Metric.ball 0 (2 * Real.pi) := h
    filter_upwards [hb.filter_mono nhdsWithin_le_nhds] with x hx
    rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  filter_upwards [hball, self_mem_nhdsWithin] with x hxball hx0
  have hcos : Real.cos x ≠ 1 := by
    intro hcos1
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff x).mp hcos1
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have habs : |(n : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
      calc |(n : ℝ)| * (2 * Real.pi) = |x| := by
            rw [← hn, abs_mul, abs_of_pos h2pi]
        _ < 2 * Real.pi := hxball
    have hn1 : |(n : ℝ)| < 1 := by nlinarith [habs, h2pi]
    have hn0 : n = 0 := by
      rw [abs_lt] at hn1
      have h1 : (-1 : ℤ) < n := by exact_mod_cast hn1.1
      have h2 : n < 1 := by exact_mod_cast hn1.2
      omega
    rw [hn0, Int.cast_zero, zero_mul] at hn
    exact hx0 hn.symm
  exact sub_ne_zero.mpr (fun h => hcos h.symm)

/-- The punctured limit defining the continuity of `logCosEps` at `0`:
`(log (cos x) + x²/2)/x² → 0`. -/
theorem tendsto_log_cos_punctured :
    Tendsto (fun x : ℝ => (Real.log (Real.cos x) + x ^ 2 / 2) / x ^ 2) (𝓝[≠] 0) (𝓝 0) := by
  have hA := tendsto_neg_log_one_sub_div.comp tendsto_one_sub_cos_punctured
  have hAB := (hA.mul tendsto_one_sub_cos_div_sq).neg
  have hconst : Tendsto (fun _ : ℝ => (1 : ℝ) / 2) (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2)) :=
    tendsto_const_nhds
  have hABc := hAB.add hconst
  have hval : -(1 * (1 / 2 : ℝ)) + 1 / 2 = 0 := by norm_num
  rw [hval] at hABc
  have hABc' : Tendsto (fun x : ℝ =>
        -((-Real.log (1 - (1 - Real.cos x)) / (1 - Real.cos x)) * ((1 - Real.cos x) / x ^ 2))
          + 1 / 2) (𝓝[≠] 0) (𝓝 0) :=
    Tendsto.congr (fun _ => rfl) hABc
  have hdecomp : (fun x : ℝ =>
        -((-Real.log (1 - (1 - Real.cos x)) / (1 - Real.cos x)) * ((1 - Real.cos x) / x ^ 2))
          + 1 / 2)
      =ᶠ[𝓝[≠] 0] (fun x : ℝ => (Real.log (Real.cos x) + x ^ 2 / 2) / x ^ 2) := by
    filter_upwards [(tendsto_nhdsWithin_iff.mp tendsto_one_sub_cos_punctured).2,
      self_mem_nhdsWithin] with x hx1 hx0
    have hx0' : x ≠ 0 := hx0
    have hx1' : 1 - Real.cos x ≠ 0 := hx1
    have hrw : 1 - (1 - Real.cos x) = Real.cos x := by ring
    rw [hrw]
    field_simp [hx1', pow_ne_zero 2 hx0']
  exact Tendsto.congr' hdecomp hABc'

/-- `logCosEps` is continuous at `0`. -/
theorem continuousAt_logCosEps : ContinuousAt logCosEps 0 :=
  continuousAt_update_same.mpr tendsto_log_cos_punctured

/-- `logCosEps` tends to `0` at `0`. -/
theorem tendsto_logCosEps : Tendsto logCosEps (𝓝 0) (𝓝 0) := by
  have h := continuousAt_logCosEps.tendsto
  rw [show logCosEps 0 = 0 by simp [logCosEps]] at h
  exact h

/-- The exact expansion `log (cos x) = ε(x) x² - x²/2` for all `x`. -/
theorem log_cos_eq_logCosEps (x : ℝ) :
    Real.log (Real.cos x) = logCosEps x * x ^ 2 - x ^ 2 / 2 := by
  by_cases hx : x = 0
  · subst hx
    simp [logCosEps]
  · have h1 : logCosEps x = (Real.log (Real.cos x) + x ^ 2 / 2) / x ^ 2 := by
      simp only [logCosEps, Function.update_of_ne hx]
    rw [h1, div_mul_cancel₀ _ (pow_ne_zero 2 hx)]
    ring

/-- The characteristic functions of the rescaled walk converge to the Gaussian one
`exp(-Q/8)` with `Q = ∑ᵢ ∑ₗ uᵢ uₗ min (tᵢ) (tₗ)`. -/
theorem tendsto_charFun_walkFddLaw (m : ℕ) (ts : Fin m → ℝ) {T : ℝ}
    (hts : ∀ i, ts i ∈ Set.Icc (0 : ℝ) T) (u : EuclideanSpace ℝ (Fin m)) :
    Tendsto (fun n : ℕ => charFun ((walkFddLaw m n ts : ProbabilityMeasure
        (EuclideanSpace ℝ (Fin m))) : Measure (EuclideanSpace ℝ (Fin m))) u)
      atTop (𝓝 (Complex.exp (-(↑(∑ i : Fin m, ∑ l : Fin m,
        u i * u l * min (ts i) (ts l)) : ℂ) / 8))) := by
  classical
  set S : ℝ := ∑ i : Fin m, |u i| with hS
  set Q : ℝ := ∑ i : Fin m, ∑ l : Fin m, u i * u l * min (ts i) (ts l) with hQ
  set k : ℕ → Fin m → ℕ := fun n i => ⌊(n : ℝ) * ts i⌋₊ with hk
  set K : ℕ → ℕ := fun n => ⌊(n : ℝ) * T⌋₊ with hKn
  set c : ℕ → ℝ := fun n => 2 * Real.sqrt (n : ℝ) with hc
  set Λ : ℕ → ℕ → ℝ := fun n j => ∑ i : Fin m, if j < k n i then u i else 0 with hΛ
  have hfloor : ∀ i l : Fin m, Tendsto (fun n : ℕ =>
      ((min (k n i) (k n l) : ℕ) : ℝ) / n) atTop (𝓝 (min (ts i) (ts l))) := by
    intro i l
    have hmin : ∀ n : ℕ, ((min (k n i) (k n l) : ℕ) : ℝ) / n
        = (⌊(n : ℝ) * min (ts i) (ts l)⌋₊ : ℝ) / n := by
      intro n
      congr 1
      congr 1
      simp only [hk]
      rw [← Monotone.map_min Nat.floor_mono]
      congr 1
      exact (mul_min_of_nonneg (ts i) (ts l) (Nat.cast_nonneg n)).symm
    exact (tendsto_nat_floor_div (min (ts i) (ts l))
      (le_min (hts i).1 (hts l).1)).congr'
      (Filter.Eventually.of_forall fun n => (hmin n).symm)
  have hR : Tendsto (fun n : ℕ => ∑ i : Fin m, ∑ l : Fin m,
      u i * u l * (((min (k n i) (k n l) : ℕ) : ℝ) / n)) atTop (𝓝 Q) := by
    refine tendsto_finsetSum Finset.univ fun i _ => ?_
    refine tendsto_finsetSum Finset.univ fun l _ => ?_
    exact (hfloor i l).const_mul (u i * u l)
  have hX2eq : (fun n : ℕ => ∑ j ∈ Finset.range (K n), (Λ n j / c n) ^ 2)
      =ᶠ[atTop] (fun n : ℕ => (1 / 4) * ∑ i : Fin m, ∑ l : Fin m,
        u i * u l * (((min (k n i) (k n l) : ℕ) : ℝ) / n)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hkK : ∀ i, k n i ≤ K n := fun i =>
      Nat.floor_mono (mul_le_mul_of_nonneg_left (hts i).2 (Nat.cast_nonneg n))
    have hc2 : (c n) ^ 2 = 4 * (n : ℝ) := by
      simp only [hc]
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      ring
    have step1 : ∑ j ∈ Finset.range (K n), (Λ n j / c n) ^ 2
        = (∑ j ∈ Finset.range (K n), (Λ n j) ^ 2) / (c n) ^ 2 := by
      calc ∑ j ∈ Finset.range (K n), (Λ n j / c n) ^ 2
          = ∑ j ∈ Finset.range (K n), (Λ n j) ^ 2 / (c n) ^ 2 :=
            Finset.sum_congr rfl fun j _ => by rw [div_pow]
        _ = (∑ j ∈ Finset.range (K n), (Λ n j) ^ 2) / (c n) ^ 2 := (Finset.sum_div _ _ _).symm
    have step2 : (∑ j ∈ Finset.range (K n), (Λ n j) ^ 2)
        = ∑ i : Fin m, ∑ l : Fin m, u i * u l * ((min (k n i) (k n l) : ℕ) : ℝ) := by
      have h := sum_sq_indicator u (k n) (K n) hkK
      simpa only [← Nat.cast_min] using h
    have step4 : (∑ i : Fin m, ∑ l : Fin m,
          u i * u l * ((min (k n i) (k n l) : ℕ) : ℝ)) / (n : ℝ)
        = ∑ i : Fin m, ∑ l : Fin m,
          u i * u l * (((min (k n i) (k n l) : ℕ) : ℝ) / n) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [step1, step2, hc2, ← step4]
    field_simp
  have hX2 : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (K n), (Λ n j / c n) ^ 2)
      atTop (𝓝 (Q / 4)) := by
    have h := hR.const_mul (1 / 4)
    have hQ4 : (1 / 4 : ℝ) * Q = Q / 4 := by ring
    rw [hQ4] at h
    exact Tendsto.congr' hX2eq.symm h
  have hbound : ∀ n : ℕ, ∀ j : ℕ, |Λ n j / c n| ≤ S / c n := by
    intro n j
    rw [abs_div]
    have hc0 : 0 ≤ c n := by
      simp only [hc]
      positivity
    rw [abs_of_nonneg hc0]
    by_cases hcn : c n = 0
    · simp [hcn]
    · have hSj : |Λ n j| ≤ S := by
        calc |Λ n j| ≤ ∑ i : Fin m, |if j < k n i then u i else 0| := by
              simp only [hΛ]
              exact Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i : Fin m, |u i| := by
              refine Finset.sum_le_sum fun i _ => ?_
              split_ifs <;> simp
          _ = S := rfl
      exact (div_le_div_iff_of_pos_right (lt_of_le_of_ne' hc0 hcn)).mpr hSj
  have hSc : Tendsto (fun n : ℕ => S / c n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have h2 : ∀ n : ℕ, S / c n = (S / 2) * (Real.sqrt (n : ℝ))⁻¹ := by
      intro n
      simp only [hc]
      rw [div_eq_mul_inv S (2 * Real.sqrt (n : ℝ)), mul_inv]
      ring
    have h3 := h1.const_mul (S / 2)
    rw [mul_zero] at h3
    exact h3.congr' (Filter.Eventually.of_forall fun n => (h2 n).symm)
  have hErr : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (K n),
      logCosEps (Λ n j / c n) * (Λ n j / c n) ^ 2) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hBndpos : (0 : ℝ) < |Q| / 4 + 1 := by positivity
    have hηpos : (0 : ℝ) < ε / (2 * (|Q| / 4 + 1)) := by positivity
    obtain ⟨δ, hδpos, hδbound⟩ := Metric.eventually_nhds_iff.mp
      (Metric.tendsto_nhds.mp tendsto_logCosEps _ hηpos)
    have hQB : Q / 4 < |Q| / 4 + 1 :=
      lt_of_le_of_lt ((div_le_div_iff_of_pos_right (show (0 : ℝ) < 4 by norm_num)).mpr
        (le_abs_self Q)) (lt_add_of_pos_right _ zero_lt_one)
    filter_upwards [hSc.eventually (eventually_lt_nhds hδpos),
      hX2.eventually (eventually_lt_nhds hQB)] with n hnδ hnB
    rw [dist_zero_right, Real.norm_eq_abs]
    have hterm : ∀ j ∈ Finset.range (K n),
        |logCosEps (Λ n j / c n) * (Λ n j / c n) ^ 2|
          ≤ (ε / (2 * (|Q| / 4 + 1))) * (Λ n j / c n) ^ 2 := by
      intro j _
      rw [abs_mul, abs_of_nonneg (sq_nonneg (Λ n j / c n))]
      have h2 : dist (Λ n j / c n) 0 < δ := by
        rw [dist_zero_right, Real.norm_eq_abs]
        exact lt_of_le_of_lt (hbound n j) hnδ
      have h3 := hδbound h2
      rw [dist_zero_right, Real.norm_eq_abs] at h3
      exact mul_le_mul_of_nonneg_right h3.le (sq_nonneg _)
    calc |∑ j ∈ Finset.range (K n), logCosEps (Λ n j / c n) * (Λ n j / c n) ^ 2|
        ≤ ∑ j ∈ Finset.range (K n),
            |logCosEps (Λ n j / c n) * (Λ n j / c n) ^ 2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range (K n), (ε / (2 * (|Q| / 4 + 1))) * (Λ n j / c n) ^ 2 :=
          Finset.sum_le_sum hterm
      _ = (ε / (2 * (|Q| / 4 + 1)))
            * ∑ j ∈ Finset.range (K n), (Λ n j / c n) ^ 2 := (Finset.mul_sum _ _ _).symm
      _ < ε := by
          have hle : (ε / (2 * (|Q| / 4 + 1)))
                * ∑ j ∈ Finset.range (K n), (Λ n j / c n) ^ 2
              ≤ (ε / (2 * (|Q| / 4 + 1))) * (|Q| / 4 + 1) :=
            mul_le_mul_of_nonneg_left hnB.le (by positivity)
          have heq : (ε / (2 * (|Q| / 4 + 1))) * (|Q| / 4 + 1) = ε / 2 := by
            have hB0 : (|Q| / 4 + 1 : ℝ) ≠ 0 := hBndpos.ne'
            field_simp
          rw [heq] at hle
          linarith [hε]
  have hLsum : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (K n),
      Real.log (Real.cos (Λ n j / c n))) atTop (𝓝 (-(Q / 8))) := by
    have hdec : ∀ n : ℕ, (∑ j ∈ Finset.range (K n), Real.log (Real.cos (Λ n j / c n)))
        = (∑ j ∈ Finset.range (K n), logCosEps (Λ n j / c n) * (Λ n j / c n) ^ 2)
          - (1 / 2) * (∑ j ∈ Finset.range (K n), (Λ n j / c n) ^ 2) := by
      intro n
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [log_cos_eq_logCosEps]
      ring
    have h := hErr.sub (hX2.const_mul (1 / 2))
    have hval : (0 : ℝ) - (1 / 2) * (Q / 4) = -(Q / 8) := by ring
    rw [hval] at h
    exact h.congr' (Filter.Eventually.of_forall fun n => (hdec n).symm)
  have hprod : ∀ᶠ n : ℕ in atTop, ∏ j ∈ Finset.range (K n), Real.cos (Λ n j / c n)
      = Real.exp (∑ j ∈ Finset.range (K n), Real.log (Real.cos (Λ n j / c n))) := by
    have hsmall : ∀ᶠ n : ℕ in atTop, S / c n < Real.pi / 2 :=
      hSc.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < Real.pi / 2))
    filter_upwards [hsmall] with n hn
    have hcospos : ∀ j : ℕ, 0 < Real.cos (Λ n j / c n) := by
      intro j
      have hmem : Λ n j / c n ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        rw [Set.mem_Ioo, ← abs_lt]
        exact lt_of_le_of_lt (hbound n j) hn
      exact Real.cos_pos_of_mem_Ioo hmem
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => (Real.exp_log (hcospos j)).symm
  have hcf : (fun n : ℕ => charFun ((walkFddLaw m n ts : ProbabilityMeasure
        (EuclideanSpace ℝ (Fin m))) : Measure (EuclideanSpace ℝ (Fin m))) u)
      =ᶠ[atTop] (fun n : ℕ =>
        (Real.exp (∑ j ∈ Finset.range (K n), Real.log (Real.cos (Λ n j / c n))) : ℂ)) := by
    filter_upwards [hprod] with n hn
    rw [charFun_walkFddLaw m ts hts n u]
    show (∏ j ∈ Finset.range (K n), (Real.cos (Λ n j / c n) : ℂ)) = _
    rw [← Complex.ofReal_prod, hn]
  have hfinal : Tendsto (fun n : ℕ =>
      (Real.exp (∑ j ∈ Finset.range (K n), Real.log (Real.cos (Λ n j / c n))) : ℂ))
      atTop (𝓝 (Complex.exp (-(↑Q : ℂ) / 8))) := by
    have hofr : Tendsto (fun n : ℕ =>
        (Real.exp (∑ j ∈ Finset.range (K n), Real.log (Real.cos (Λ n j / c n))) : ℂ))
        atTop (𝓝 ((Real.exp (-(Q / 8)) : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp
        ((Real.continuous_exp.tendsto _).comp hLsum)
    have hval : ((Real.exp (-(Q / 8)) : ℝ) : ℂ) = Complex.exp (-(↑Q : ℂ) / 8) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rwa [hval] at hofr
  exact hfinal.congr' hcf.symm

end Parking
