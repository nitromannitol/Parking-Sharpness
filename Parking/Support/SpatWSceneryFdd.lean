/-
**The finite-dimensional convergence of the rescaled scenery pairings to the canonical spatial
white noise**, `Parking.tendsto_scenePair_fdd`.  This is the capstone assembly of four
general-purpose modules (`SpatCLTFilter.lean`, `RiemannLattice.lean`, `CramerWoldFilter.lean`,
`SceneryFdd.lean`).

Route: for `R : ℝ`, `X R w i := scenePair w (max R 1) (φ i)` is measurable for every real `R`
(`max R 1 ≥ 1` always, so `scenePair_linearCombination_eq_sum`'s box reduction applies).  For a
fixed linear combination `t : Fin m → ℝ`, `∑ᵢ tᵢ · X R w i` is, by
`Parking.scenePair_linearCombination_eq_sum`, ONE finite weighted sum of the i.i.d. scenery at the
combined test function `ψ := ∑ᵢ tᵢφᵢ`; pushed through `Parking.law_map_confReal` this is exactly
the shape `Parking.tendsto_charFun_weighted_scenery_sum_filter` consumes, whose limiting variance
`v·∫ψ²` is identified by the real-parameter Riemann sum `Parking.tendsto_latticeSum_mul_rpow`.  On
the limit side, the finite linear combination `∑ᵢ tᵢ·contW v (φ i)` has Gaussian law by
Mathlib's own `IsGaussianProcess`/`HasGaussianLaw` combinators (`Parking.isGaussianProcess_contW`
composed with `.comp_right`, `.smul`, `.hasGaussianLaw_fun_sum`), with mean `0`
(`Parking.contW_integral`, summed) and variance `v·∫ψ²` (`Parking.integral_contW_mul`, expanded
bilinearly against the SAME expansion of `∫ψ²`), so its characteristic function at `1` is the same
Gaussian exponential by `HasGaussianLaw.charFun_map_eq`.  The real-parameter Cramer-Wold theorem
(`Parking.Generic.CramerWold.tendstoInDistribution_of_tendsto_charFun_linearCombination_filter`)
assembles the finitely many scalar limits into finite-dimensional convergence in law, and
`Parking.Generic.CramerWold.tendsto_integral_of_tendstoInDistribution` reads it off against every
bounded continuous test function.
-/
import Parking.Support.SceneryFdd
import Parking.Support.UpperTarget

open MeasureTheory ProbabilityTheory Filter Topology LatticeProb
open scoped ENNReal NNReal

noncomputable section
namespace Parking

open Parking.Generic.CramerWold

variable {d : ℕ}

/-! ### Measurability of `scenePair` at every scale `R ≥ 1`, and hence at `max R 1` for every
real `R` -/

/-- **`scenePair` at a single test function reduces to the finite box sum**, the `m = 1` case of
`scenePair_linearCombination_eq_sum`'s own reduction, extracted for measurability. -/
theorem scenePair_eq_sceneryBox_sum {φ : (Fin d → ℝ) → ℝ} {B : ℝ} (hB : 0 < B)
    (hbound : ∀ x : Fin d → ℝ, φ x ≠ 0 → ‖x‖ ≤ B) {R : ℝ} (hR : 1 ≤ R) (w : Data d) :
    scenePair w R φ
      = ∑ y ∈ sceneryBox d B R, R ^ (-(d : ℝ) / 2) * (confReal w y * φ (fun j => (y j : ℝ) / R)) := by
  show R ^ (-(d : ℝ) / 2) * ∑' y : Site d, (w.1 y : ℝ) * φ (fun j => (y j : ℝ) / R) = _
  rw [← Finset.mul_sum]
  congr 1
  apply tsum_eq_sum
  intro y hy
  by_contra hne
  apply hy
  apply mem_sceneryBox_of_ne_zero hB hbound hR
  intro hz
  exact hne (by rw [hz, mul_zero])

theorem measurable_scenePair {φ : (Fin d → ℝ) → ℝ} {B : ℝ} (hB : 0 < B)
    (hbound : ∀ x : Fin d → ℝ, φ x ≠ 0 → ‖x‖ ≤ B) {R : ℝ} (hR : 1 ≤ R) :
    Measurable (fun w : Data d => scenePair w R φ) := by
  have heq : (fun w : Data d => scenePair w R φ) = fun w =>
      ∑ y ∈ sceneryBox d B R, R ^ (-(d : ℝ) / 2) * (confReal w y * φ (fun j => (y j : ℝ) / R)) :=
    funext fun w => scenePair_eq_sceneryBox_sum hB hbound hR w
  rw [heq]
  exact Finset.measurable_sum _ fun y _ =>
    measurable_const.mul (((measurable_pi_apply y).comp measurable_confReal).mul measurable_const)

/-- **`scenePair` is measurable at EVERY real `R`, with no bound on `φ`'s support and no
`1 ≤ R` hypothesis** (unlike `Parking.measurable_scenePair` above, whose box-reduction route
genuinely needs `1 ≤ R`): the same `Measurable.tsum` route `Parking.measurable_signedPair`
already uses, applied to `scenePair`'s own summand, which needs no reduction to a finite box at
all. Needed for `TendstoInDistribution`'s own measurability field, which ranges over literally
every index (`Parking/Generic/Slutsky.lean`), avoiding the `max R 1` device that
`Parking.tendsto_scenePair_fdd`'s own proof needs for the SAME purpose one level up. -/
theorem measurable_scenePair_any_R {φ : (Fin d → ℝ) → ℝ} (R : ℝ) :
    Measurable (fun w : Data d => scenePair w R φ) := by
  unfold scenePair
  apply Measurable.const_mul
  apply Measurable.tsum
  intro y
  exact ((measurable_pi_apply y).comp measurable_confReal).mul_const _

/-! ### The exact `Real.rpow`-vs-`Monoid.npow` identity for the discrete variance -/

theorem rpow_neg_half_sq {a : ℝ} (ha : 0 ≤ a) (d : ℕ) :
    (a ^ (-(d : ℝ) / 2)) ^ (2 : ℕ) = (1 / a) ^ d := by
  rw [← Real.rpow_natCast (a ^ (-(d : ℝ) / 2)) 2, ← Real.rpow_mul ha]
  have hexp : (-(d : ℝ) / 2) * ((2 : ℕ) : ℝ) = -(d : ℝ) := by push_cast; ring
  rw [hexp, Real.rpow_neg ha, Real.rpow_natCast, one_div, inv_pow]

/-! ### The Gaussian law of a finite linear combination of `contW`, and its characteristic
function at `1` -/

/-- **The characteristic function, at argument `1`, of a finite linear combination of the
canonical spatial white noise at finitely many test functions.** -/
theorem charFun_contW_linearCombination {v : ℝ} (hv : 0 ≤ v) {m : ℕ} (t : Fin m → ℝ)
    (φ : Fin m → (Fin d → ℝ) → ℝ) (hφ : ∀ i, IsTestFun (φ i)) :
    charFun ((whiteNoiseLaw (volume : Measure (Fin d → ℝ))).map
        (fun ω => ∑ k, t k * contW (d := d) v (φ k) ω)) 1
      = Complex.exp (-((v * ∫ x, (∑ k, t k * φ k x) ^ 2 : ℝ) : ℂ) / 2) := by
  set μ := whiteNoiseLaw (volume : Measure (Fin d → ℝ)) with hμdef
  set Y := fun ω : (↥(l2Basis (volume : Measure (Fin d → ℝ))) → ℝ) =>
    ∑ k, t k * contW (d := d) v (φ k) ω with hYdef
  -- `Y` has Gaussian law, via Mathlib's Gaussian-process combinators.
  have hGauss : HasGaussianLaw Y μ := by
    have h1 := (isGaussianProcess_contW (d := d) hv).comp_right φ |>.smul t
    have h2 := h1.hasGaussianLaw_fun_sum (I := (Finset.univ : Finset (Fin m)))
    simpa [hYdef, smul_eq_mul, Function.comp] using h2
  -- Mean zero.
  have hInt : ∀ k : Fin m, Integrable (fun ω => t k * contW (d := d) v (φ k) ω) μ :=
    fun k => (contW_integral hv (φ k) (hφ k)).1.const_mul (t k)
  have hmean : ∫ ω, Y ω ∂μ = 0 := by
    have hsum : ∫ ω, Y ω ∂μ = ∑ k, ∫ ω, t k * contW (d := d) v (φ k) ω ∂μ := by
      rw [hYdef]; exact integral_finsetSum Finset.univ (fun k _ => hInt k)
    rw [hsum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [integral_const_mul, (contW_integral hv (φ k) (hφ k)).2, mul_zero]
  -- Variance, by bilinear expansion against the covariance `Parking.integral_contW_mul`.
  have hAEmeas : AEMeasurable Y μ := by
    apply Measurable.aemeasurable
    rw [hYdef]
    exact Finset.measurable_sum _ fun k _ => (measurable_contW v (φ k)).const_mul (t k)
  have hvarEq : Var[Y; μ] = ∫ ω, Y ω ^ 2 ∂μ := variance_of_integral_eq_zero hAEmeas hmean
  have hYsq : ∀ ω, Y ω ^ 2
      = ∑ k, ∑ l, (t k * contW (d := d) v (φ k) ω) * (t l * contW (d := d) v (φ l) ω) := by
    intro ω; rw [hYdef, sq, Fintype.sum_mul_sum]
  have hpairInt : ∀ k l : Fin m,
      Integrable (fun ω => (t k * contW (d := d) v (φ k) ω) * (t l * contW (d := d) v (φ l) ω)) μ := by
    intro k l
    have hmul : Integrable (fun ω => contW (d := d) v (φ k) ω * contW (d := d) v (φ l) ω) μ :=
      (memLp_contW v (φ k)).integrable_mul (memLp_contW v (φ l))
    have heq : (fun ω => (t k * contW (d := d) v (φ k) ω) * (t l * contW (d := d) v (φ l) ω))
        = fun ω => (t k * t l) * (contW (d := d) v (φ k) ω * contW (d := d) v (φ l) ω) := by
      funext ω; ring
    rw [heq]; exact hmul.const_mul _
  have hYsqInt : ∫ ω, Y ω ^ 2 ∂μ
      = ∑ k, ∑ l, ∫ ω, (t k * contW (d := d) v (φ k) ω) * (t l * contW (d := d) v (φ l) ω) ∂μ := by
    have hcongr : (fun ω => Y ω ^ 2)
        = fun ω => ∑ k, ∑ l, (t k * contW (d := d) v (φ k) ω) * (t l * contW (d := d) v (φ l) ω) :=
      funext hYsq
    rw [hcongr, integral_finsetSum Finset.univ
      (fun k _ => integrable_finsetSum Finset.univ (fun l _ => hpairInt k l))]
    exact Finset.sum_congr rfl fun k _ => integral_finsetSum Finset.univ (fun l _ => hpairInt k l)
  have hpairTerm : ∀ k l : Fin m,
      ∫ ω, (t k * contW (d := d) v (φ k) ω) * (t l * contW (d := d) v (φ l) ω) ∂μ
        = t k * t l * (v * ∫ x, φ k x * φ l x) := by
    intro k l
    have heq : (fun ω => (t k * contW (d := d) v (φ k) ω) * (t l * contW (d := d) v (φ l) ω))
        = fun ω => (t k * t l) * (contW (d := d) v (φ k) ω * contW (d := d) v (φ l) ω) := by
      funext ω; ring
    rw [heq, integral_const_mul, integral_contW_mul hv (φ k) (φ l) (hφ k) (hφ l)]
  have hvarFinal : Var[Y; μ] = ∑ k, ∑ l, t k * t l * (v * ∫ x, φ k x * φ l x) := by
    rw [hvarEq, hYsqInt]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hpairTerm k l
  -- The same double sum, over `volume`, for `∫ ψ²`.
  have hφpairInt : ∀ k l : Fin m,
      Integrable (fun x : Fin d → ℝ => (t k * φ k x) * (t l * φ l x)) (volume : Measure (Fin d → ℝ)) := by
    intro k l
    have heq : (fun x : Fin d → ℝ => (t k * φ k x) * (t l * φ l x))
        = fun x => (t k * t l) * (φ k x * φ l x) := by funext x; ring
    rw [heq]
    exact (((hφ k).1.continuous.mul (hφ l).1.continuous).integrable_of_hasCompactSupport
      ((hφ k).2.mul_right)).const_mul _
  have hψsq : ∀ x : Fin d → ℝ, (∑ k, t k * φ k x) ^ 2 = ∑ k, ∑ l, (t k * φ k x) * (t l * φ l x) :=
    fun x => by rw [sq, Fintype.sum_mul_sum]
  have hψsqInt : ∫ x, (∑ k, t k * φ k x) ^ 2 ∂(volume : Measure (Fin d → ℝ))
      = ∑ k, ∑ l, t k * t l * ∫ x, φ k x * φ l x ∂(volume : Measure (Fin d → ℝ)) := by
    have hcongr : (fun x : Fin d → ℝ => (∑ k, t k * φ k x) ^ 2)
        = fun x => ∑ k, ∑ l, (t k * φ k x) * (t l * φ l x) := funext hψsq
    have hpairTerm' : ∀ k l : Fin m,
        ∫ x, (t k * φ k x) * (t l * φ l x) ∂(volume : Measure (Fin d → ℝ))
          = t k * t l * ∫ x, φ k x * φ l x ∂(volume : Measure (Fin d → ℝ)) := by
      intro k l
      have heq : (fun x : Fin d → ℝ => (t k * φ k x) * (t l * φ l x))
          = fun x => (t k * t l) * (φ k x * φ l x) := by funext x; ring
      rw [heq, integral_const_mul]
    rw [hcongr, integral_finsetSum Finset.univ
      (fun k _ => integrable_finsetSum Finset.univ (fun l _ => hφpairInt k l))]
    exact Finset.sum_congr rfl fun k _ => by
      rw [integral_finsetSum Finset.univ (fun l _ => hφpairInt k l)]
      exact Finset.sum_congr rfl fun l _ => hpairTerm' k l
  have hvarv : Var[Y; μ] = v * ∫ x, (∑ k, t k * φ k x) ^ 2 ∂(volume : Measure (Fin d → ℝ)) := by
    rw [hvarFinal, hψsqInt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  -- Assemble via `HasGaussianLaw.charFun_map_eq` at `t = 1`.
  have hone : ∀ x : ℝ, (inner ℝ (1 : ℝ) x : ℝ) = x := by
    intro x; rw [RCLike.inner_apply]; simp
  have hchar := hGauss.charFun_map_eq (1 : ℝ)
  have hinnerfun : (fun ω => (inner ℝ (1 : ℝ) (Y ω) : ℝ)) = Y := funext fun ω => hone (Y ω)
  rw [hinnerfun, hmean, hvarv] at hchar
  rw [hchar]
  congr 1
  push_cast
  ring

/-! ### The capstone assembly -/

/-- **The finite-dimensional convergence in law of the rescaled scenery pairings to the canonical
spatial white noise**, at the real-parameter filter `R → ∞`, tested against every bounded
continuous function of finitely many test-function pairings.  This is the
`scenePair`/`W`-coordinates half of the `hjoint` clause of `Parking.Frozen.spatial_scaling`. -/
theorem tendsto_scenePair_fdd (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν) {m : ℕ}
    (φ : Fin m → (Fin d → ℝ) → ℝ) (hφ : ∀ i, IsTestFun (φ i))
    (F : BoundedContinuousFunction (Fin m → ℝ) ℝ) :
    Tendsto (fun R : ℝ => ∫ w, F (fun i => scenePair w R (φ i)) ∂(law d ν)) atTop
      (𝓝 (∫ ω, F (fun i => contW (variance (fun k : ℤ => (k : ℝ)) ν) (φ i) ω)
            ∂(whiteNoiseLaw (volume : Measure (Fin d → ℝ))))) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  set v : ℝ := variance (fun k : ℤ => (k : ℝ)) ν with hvdef
  have hv : 0 ≤ v := variance_nonneg _ _
  obtain ⟨B, hB, hbound⟩ := exists_uniform_norm_bound hφ
  set X : ℝ → Data d → Fin m → ℝ := fun R w i => scenePair w (max R 1) (φ i) with hXdef
  set Z := fun (ω : ↥(l2Basis (volume : Measure (Fin d → ℝ))) → ℝ) (i : Fin m) =>
    contW (d := d) v (φ i) ω with hZdef
  have hXm : ∀ R : ℝ, Measurable (X R) := fun R =>
    measurable_pi_lambda _ fun i => measurable_scenePair hB (hbound i) (le_max_right R 1)
  have hZm : Measurable Z := measurable_pi_lambda _ fun i => measurable_contW v (φ i)
  -- A single reusable fact: `(max R 1) ^ (-(d:ℝ)/2) → 0`.
  have hRpow0 : Tendsto (fun R : ℝ => (max R 1) ^ (-(d : ℝ) / 2)) atTop (𝓝 0) := by
    have hcompose : Tendsto (fun R : ℝ => max R 1) atTop atTop :=
      tendsto_atTop_mono (fun R => le_max_left R 1) tendsto_id
    have hdpos : (0 : ℝ) < (d : ℝ) / 2 := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
      linarith
    have hbase : Tendsto (fun x : ℝ => x ^ (-((d : ℝ) / 2))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop hdpos
    have hexpeq : (-(d : ℝ) / 2 : ℝ) = -((d : ℝ) / 2) := by ring
    rw [hexpeq]
    exact hbase.comp hcompose
  -- The scalar characteristic-function hypothesis of Cramer-Wold, for a fixed `t`.
  have hcomb : ∀ t : Fin m → ℝ,
      Tendsto (fun R : ℝ => charFun ((law d ν).map (fun w => ∑ k, t k * X R w k)) 1) atTop
        (𝓝 (charFun ((whiteNoiseLaw (volume : Measure (Fin d → ℝ))).map
              (fun ω => ∑ k, t k * Z ω k)) 1)) := by
    intro t
    set ψ : (Fin d → ℝ) → ℝ := fun x => ∑ i, t i * φ i x with hψdef
    have hboundψ : ∀ x : Fin d → ℝ, ψ x ≠ 0 → ‖x‖ ≤ B := by
      intro x hx
      by_contra hxB
      apply hx
      refine Finset.sum_eq_zero fun i _ => ?_
      have hφi0 : φ i x = 0 := by
        by_contra hφi
        exact hxB (hbound i x hφi)
      rw [hφi0, mul_zero]
    set S : ℝ → Finset (Site d) := fun R => sceneryBox d B (max R 1) with hSdef
    set c : ℝ → Site d → ℝ :=
      fun R y => (max R 1) ^ (-(d : ℝ) / 2) * ψ (fun j => (y j : ℝ) / (max R 1)) with hcdef
    -- The discrete-side equality, exact for every `R`.
    have heqLHS : ∀ R : ℝ,
        charFun ((law d ν).map (fun w => ∑ k, t k * X R w k)) 1
          = charFun ((iidLaw d (realLaw ν)).map (fun η => ∑ y ∈ S R, c R y * η y)) 1 := by
      intro R
      have hR1 : (1 : ℝ) ≤ max R 1 := le_max_right R 1
      have hsumMeasurable : Measurable (fun η : Site d → ℝ => ∑ y ∈ S R, c R y * η y) :=
        Finset.measurable_sum _ fun y _ => measurable_const.mul (measurable_pi_apply y)
      have hsumeq : (fun w : Data d => ∑ k, t k * X R w k)
          = (fun η : Site d → ℝ => ∑ y ∈ S R, c R y * η y) ∘ confReal := by
        funext w
        show ∑ k, t k * scenePair w (max R 1) (φ k) = ∑ y ∈ S R, c R y * confReal w y
        exact scenePair_linearCombination_eq_sum t hB hbound hR1 w
      have hmap : (law d ν).map confReal = iidLaw d (realLaw ν) := law_map_confReal hd ν
      rw [hsumeq, ← Measure.map_map hsumMeasurable measurable_confReal, hmap]
    -- The Riemann-sum limits `hV`, `hM`, `hMd` for the scalar CLT.
    have hψtest : IsTestFun ψ := isTestFun_finset_sum t hφ
    have hψ2test : IsTestFun (fun x => ψ x * ψ x) :=
      ⟨hψtest.1.mul hψtest.1, HasCompactSupport.mul_right hψtest.2⟩
    have hboundψ2 : ∀ x : Fin d → ℝ, ψ x * ψ x ≠ 0 → ‖x‖ ≤ B := by
      intro x hx
      exact hboundψ x (fun h => hx (by rw [h, mul_zero]))
    have hV : Tendsto (fun R : ℝ => ∑ y ∈ S R, (c R y) ^ 2) atTop
        (𝓝 (∫ x, ψ x * ψ x)) := by
      have hbase : Tendsto (fun R' : ℝ =>
          (∑' y : Site d, (fun x => ψ x * ψ x) (fun j => (y j : ℝ) / R')) * (1 / R') ^ d) atTop
          (𝓝 (∫ x, ψ x * ψ x)) :=
        tendsto_latticeSum_mul_rpow hψ2test.1.continuous hψ2test.2
      have hcompose : Tendsto (fun R : ℝ => max R 1) atTop atTop :=
        tendsto_atTop_mono (fun R => le_max_left R 1) tendsto_id
      have hcomposed : Tendsto (fun R : ℝ =>
          (∑' y : Site d, (fun x => ψ x * ψ x) (fun j => (y j : ℝ) / (max R 1)))
            * (1 / (max R 1)) ^ d) atTop (𝓝 (∫ x, ψ x * ψ x)) :=
        hbase.comp hcompose
      have hident : (fun R : ℝ => ∑ y ∈ S R, (c R y) ^ 2)
          =ᶠ[atTop] (fun R : ℝ =>
            (∑' y : Site d, (fun x => ψ x * ψ x) (fun j => (y j : ℝ) / (max R 1)))
              * (1 / (max R 1)) ^ d) := by
        filter_upwards with R
        have hRpos : (0 : ℝ) ≤ max R 1 := le_trans zero_le_one (le_max_right R 1)
        have hRe1 : (1 : ℝ) ≤ max R 1 := le_max_right R 1
        have hcterm : ∀ y : Site d, (c R y) ^ 2
            = (1 / (max R 1)) ^ d
                * (ψ (fun j => (y j : ℝ) / (max R 1)) * ψ (fun j => (y j : ℝ) / (max R 1))) := by
          intro y
          show ((max R 1) ^ (-(d : ℝ) / 2) * ψ (fun j => (y j : ℝ) / (max R 1))) ^ 2 = _
          have hrp := rpow_neg_half_sq hRpos d
          calc ((max R 1) ^ (-(d : ℝ) / 2) * ψ (fun j => (y j : ℝ) / (max R 1))) ^ 2
              = ((max R 1) ^ (-(d : ℝ) / 2)) ^ 2
                  * (ψ (fun j => (y j : ℝ) / (max R 1)) * ψ (fun j => (y j : ℝ) / (max R 1))) := by
                ring
            _ = (1 / (max R 1)) ^ d
                  * (ψ (fun j => (y j : ℝ) / (max R 1)) * ψ (fun j => (y j : ℝ) / (max R 1))) := by
                rw [hrp]
        show ∑ y ∈ sceneryBox d B (max R 1), (c R y) ^ 2 = _
        rw [Finset.sum_congr rfl (fun y _ => hcterm y), ← Finset.mul_sum,
          ← tsum_eq_sceneryBox_sum hB hboundψ2 hRe1]
        ring
      exact hcomposed.congr' hident.symm
    obtain ⟨Msup, hMsup0, hMsupbound⟩ :=
      exists_norm_le_of_hasCompactSupport hψtest.1.continuous hψtest.2
    have hMd : ∀ R : ℝ, ∀ y ∈ S R, |c R y| ≤ (max R 1) ^ (-(d : ℝ) / 2) * Msup := by
      intro R y _
      have hRnn : (0 : ℝ) ≤ (max R 1) ^ (-(d : ℝ) / 2) :=
        Real.rpow_nonneg (zero_le_one.trans (le_max_right R 1)) _
      show |(max R 1) ^ (-(d : ℝ) / 2) * ψ (fun j => (y j : ℝ) / (max R 1))|
          ≤ (max R 1) ^ (-(d : ℝ) / 2) * Msup
      rw [abs_mul, abs_of_nonneg hRnn]
      exact mul_le_mul_of_nonneg_left (hMsupbound _) hRnn
    have hMtendsto : Tendsto (fun R : ℝ => (max R 1) ^ (-(d : ℝ) / 2) * Msup) atTop (𝓝 0) := by
      simpa using hRpow0.mul_const Msup
    have hCLT := tendsto_charFun_weighted_scenery_sum_filter (l := (atTop : Filter ℝ)) ν hν
      S c (1 : ℝ) hV (fun R => (max R 1) ^ (-(d : ℝ) / 2) * Msup) hMtendsto hMd
    have hσ2 : (∫ x : ℝ, x ^ 2 ∂(realLaw ν) : ℝ) = v := (variance_eq_integral_sq_realLaw ν hν).symm
    rw [hσ2] at hCLT
    have hlimit : Complex.exp (-((v : ℝ) : ℂ) * ((∫ x, ψ x * ψ x : ℝ) : ℂ) * ((1 : ℝ) : ℂ) ^ 2 / 2)
        = charFun ((whiteNoiseLaw (volume : Measure (Fin d → ℝ))).map
              (fun ω => ∑ k, t k * Z ω k)) 1 := by
      have heqZ : (fun ω : ↥(l2Basis (volume : Measure (Fin d → ℝ))) → ℝ => ∑ k, t k * Z ω k)
          = fun ω => ∑ k, t k * contW (d := d) v (φ k) ω := rfl
      rw [heqZ, charFun_contW_linearCombination (d := d) hv t φ hφ]
      have hψeq : (∫ x, ψ x * ψ x : ℝ) = ∫ x, (∑ k, t k * φ k x) ^ 2 := by
        have : (fun x : Fin d → ℝ => ψ x * ψ x) = fun x => (∑ k, t k * φ k x) ^ 2 := by
          funext x
          show (∑ i, t i * φ i x) * (∑ i, t i * φ i x) = (∑ k, t k * φ k x) ^ 2
          ring
        rw [this]
      rw [hψeq]
      congr 1
      push_cast
      ring
    rw [← hlimit]
    exact hCLT.congr' (Filter.Eventually.of_forall fun R => (heqLHS R).symm)
  -- Assemble via Cramer-Wold and read off against bounded continuous functions.
  have hTID : TendstoInDistribution X atTop Z (fun _ : ℝ => law d ν)
      (whiteNoiseLaw (volume : Measure (Fin d → ℝ))) :=
    tendstoInDistribution_of_tendsto_charFun_linearCombination_filter hXm hZm hcomb
  have hread := tendsto_integral_of_tendstoInDistribution hTID F
  refine hread.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have hfun : (fun w : Data d => F (X R w)) = fun w => F (fun i => scenePair w R (φ i)) := by
    funext w
    congr 1
    funext i
    show scenePair w (max R 1) (φ i) = scenePair w R (φ i)
    rw [max_eq_left hR]
  show (∫ w, F (X R w) ∂(law d ν)) = ∫ w, F (fun i => scenePair w R (φ i)) ∂(law d ν)
  rw [hfun]

end Parking
end
