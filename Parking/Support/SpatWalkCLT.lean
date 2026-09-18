/-
The finite-dimensional characteristic-function limit of the `d`-dimensional simple random
walk's own rescaled path: the scalar core of `hWalk`, the hypothesis
`Parking.External.SpatialStoppingStability` needs.  This is the analogue, for the SIMPLE
(undirected, lazy) random walk on `Site d`, of the oriented node's `TightWalk.lean`
(`charFun_walkFddLaw`/`tendsto_charFun_walkFddLaw`).  The walk's `d` coordinate PROCESSES are
not independent at any finite horizon (a step touches exactly one coordinate), so the general
linear combination `∑ᵢℓ t(i,ℓ)·X(i,ℓ)` over BOTH the `m` evaluation times and the `d` coordinates
is computed directly, rather than handled coordinate-by-coordinate.

THE ONE-STEP LAW. `Parking.stepLaw d` is uniform on `Fin d × Bool` (mass `1/(2d)` at each
point): a step touches a fixed coordinate `ℓ` with probability `1/d`, moving it by `±1`
(probability `1/2` each) when it does. So, unlike the oriented walk's `±1` steps (a single
cosine), the characteristic function of one step of a general linear combination is an
AVERAGE OF `d` COSINES (`spat_integral_stepLaw_cexp`): for `Λ : Fin d → ℝ` the "active
coefficient" of each coordinate at a fixed step,
`∫ b, exp(i·x·Λ(b.1)·sign(b.2)) ∂(stepLaw d) = (1/d)·∑ℓ cos(x·Λ(ℓ))`.

THE PRODUCT FORMULA (`charFun_spatWalkFdd`), the `d`-dimensional analogue of
`charFun_walkFddLaw`: for weights `t : Fin m → Fin d → ℝ` and times `ts : Fin m → ℝ` in
`[0,T]`, the characteristic function of `∑ᵢℓ t(i,ℓ)·spatialScaledSite n (walkPath 0 p
⌊n·tsᵢ⌋) ℓ` at argument `1` is `∏_{j<⌊nT⌋} (1/d)·∑ℓ cos(Λ(n,j,ℓ)/√n)`, where
`Λ(n,j,ℓ) := ∑ᵢ [j < ⌊n·tsᵢ⌋]·t(i,ℓ)` is the coefficient of coordinate `ℓ` still "active" at
step `j`; `coordStep`'s vanishing off its own coordinate (`coordStep_eq`) collapses the
`d`-fold sum over coordinates to the ONE touched at each step, and step-independence
(`iIndepFun_infinitePi`, `Parking.Support.WalkMaximal`) gives the product over steps.

THE LIMIT (`tendsto_charFun_spatWalkFdd`), the `d`-dimensional analogue of
`tendsto_charFun_walkFddLaw`: as `n → ∞`, this product converges to
`exp(-Q/(2d))`, `Q := ∑ℓ∑ᵢᵢ' t(i,ℓ)·t(i',ℓ)·min(tsᵢ,tsᵢ')` — matching the covariance of `d`
INDEPENDENT copies of a real Brownian motion of variance rate `1/d`, exactly
`LatticeProb.IsBrownianSpace`'s own normalization (`√d·(coordinate - x)` a standard real
Brownian motion). The proof avoids the oriented node's Landau-notation apparatus
(`logCosEps`) entirely, using instead two QUANTITATIVE Mathlib bounds throughout: the exact
quartic Taylor remainder for cosine, `Real.cos_bound`, and the exact logarithm remainder,
`Real.abs_log_sub_add_sum_range_le` (at range `1`), combined into a single pointwise
remainder bound `hrbound`: `|log((1/d)∑ℓcos(Λ(n,j,ℓ)/√n)) + X2(n,j)| ≤ 3·W(n)·X2(n,j)`, where
`X2(n,j) := (1/(2dn))·∑ℓΛ(n,j,ℓ)²` is the EXACT quadratic leading term (its own sum over `j`
computed in closed form by the general combinatorial identity `sum_sq_indicator`, the same as
in the oriented node) and `W(n) := (S/√n)²/2 → 0` (`S` a fixed bound on the
weights) is the uniform smallness rate. Summing the remainder bound over `j`, using that
`∑_j X2(n,j)` is eventually bounded (it converges to `Q/(2d)`) while `W(n) → 0`, gives the
sum of logs converging to `-Q/(2d)`; lifting through `Real.exp_sum`/`Real.exp_log` (valid once
`W(n) < 1/2` makes every factor positive) and casting to `ℂ` gives the stated limit.

`one_sub_cos_le_sq_div_two`, `one_sub_cos_nonneg`, `tendsto_nat_floor_div`,
`sum_sq_indicator` and `sum_range_swap_indicator` are general-purpose real-analysis and
finite-sum lemmas, no Parking content (`Parking/Generic/WalkCLT.lean`).  `tendsto_nat_floor_div`
and `sum_sq_indicator` match the oriented node's own `TightWalk.lean` lemmas of the same
mathematical content, since their proofs use nothing about the driving distribution, and
`sum_range_swap_indicator` is the same "successive-increments" swap argument generalized from a
single weight function to an arbitrary one, used once per coordinate inside the product-formula
proof.

`hWalk` ITSELF (the bounded-continuous-function form of the finite-dimensional convergence,
matching `Parking.External.SpatialStoppingStability`'s own hypothesis exactly): `Parking.
hWalk_of_isBrownianSpace`, below. The bridge from the scalar combination limit above reindexes
`Fin m → (Fin d → ℝ)` against `Fin (m * d) → ℝ` via `finProdFinEquiv` (`Equiv.sum_comp`,
`Fintype.sum_prod_type`) and applies `Parking.Generic.CramerWold`'s
`tendstoInDistribution_of_tendsto_charFun_linearCombination` (general in the target dimension,
no transposition needed) at that reindexed dimension, composing back to `Fin m → (Fin d → ℝ)`
through the continuous "un-reindexing" map (`TendstoInDistribution.continuous_comp`, the SAME
pattern `Parking.Generic.CramerWold`'s own proof uses to pass from `EuclideanSpace ℝ (Fin m)`
back to the plain product type), then unwinding through Portmanteau
(`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`). The continuum-side scalar
characteristic function is matched against `LatticeProb.IsBrownianSpace`'s own covariance by
`Parking.Generic.WalkCLT.charFun_isBrownianSpace_linearCombination` (`Parking/Generic/
BrownianFdd.lean`, general-purpose, no Parking content): `IsBrownianSpace.coord` gives
`√d · B(·)(·)(ℓ)` a genuine Mathlib `IsBrownianReal`, so `Var(B_t(ℓ)) = t/d`, matching `Q/(2d)`'s
own block-diagonal-in-`ℓ` structure exactly, since the discrete walk's own cross-`ℓ` covariance
is identically zero too. One genuine subtlety: `LatticeProb.IsBrownianSpace.coord` gives only
`AEMeasurable` coordinates (Mathlib's own Brownian-motion library separates "has the right
finite-dimensional laws" from genuine pointwise measurability, matching `IsPreBrownianReal`'s
own `mk'`/`.mk` naming convention), so the continuum process is compared against its measurable
modification (`AEMeasurable.mk`) throughout the Cramer-Wold/Portmanteau machinery and related
back to the true process by the a.e. equality at the very end (`Measure.map_congr`,
`integral_congr_ae`), exactly as a modification of a pre-Brownian motion is itself pre-Brownian.
-/
import Parking.Support.WalkMaximal
import Parking.Support.ContSpatialValue
import Parking.Generic.CramerWold
import Parking.Generic.BrownianFdd
import Parking.Generic.WalkCLT

open MeasureTheory Finset ProbabilityTheory Filter Topology LatticeProb
open Parking.Generic.WalkCLT
open scoped NNReal ENNReal
noncomputable section
namespace Parking

/-- **The one-step characteristic function of the `d`-dimensional simple random walk, at a
general "active coefficient" `Λ : Fin d → ℝ`**: `∫ b, exp(i·x·Λ(b.1)·sign(b.2)) ∂(stepLaw d)
= (1/d)·∑ℓ cos(x·Λ(ℓ))`. -/
theorem spat_integral_stepLaw_cexp (d : ℕ) (hd : 1 ≤ d) (x : ℝ) (Λ : Fin d → ℝ) :
    ∫ b : Fin d × Bool, Complex.exp (((x * Λ b.1 * (if b.2 then (1:ℝ) else -1) : ℝ) : ℂ) * Complex.I)
        ∂(stepLaw d)
      = ((1 / d : ℝ) * ∑ ℓ : Fin d, Real.cos (x * Λ ℓ) : ℂ) := by
  haveI := stepLaw_isProbability hd
  have hfin : ∀ b : Fin d × Bool,
      Integrable (fun b' => Complex.exp (((x * Λ b'.1 * (if b'.2 then (1:ℝ) else -1) : ℝ) : ℂ) * Complex.I))
        (Measure.dirac b) := fun b => integrable_dirac (by simp)
  rw [stepLaw, integral_smul_measure, integral_finsetSum_measure (fun b _ => hfin b)]
  simp only [integral_dirac]
  rw [Complex.real_smul, Fintype.sum_prod_type]
  rw [ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  have hcos2 : ∀ z : ℂ, Complex.cos z = (Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)) / 2 :=
    fun z => Complex.ext rfl rfl
  have hterm : ∀ ℓ : Fin d,
      (∑ s : Bool, Complex.exp (((x * Λ ℓ * (if s then (1:ℝ) else -1) : ℝ) : ℂ) * Complex.I))
      = (2 * Real.cos (x * Λ ℓ) : ℂ) := by
    intro ℓ
    rw [Fintype.sum_bool]
    have et : ((x * Λ ℓ * (1:ℝ) : ℝ) : ℂ) * Complex.I = (↑(x * Λ ℓ) : ℂ) * Complex.I := by
      norm_num
    have ef : ((x * Λ ℓ * (-1:ℝ) : ℝ) : ℂ) * Complex.I = (-(↑(x * Λ ℓ) : ℂ)) * Complex.I := by
      push_cast; ring
    show Complex.exp (((x * Λ ℓ * (if (true:Bool) then (1:ℝ) else -1) : ℝ) : ℂ) * Complex.I)
        + Complex.exp (((x * Λ ℓ * (if (false:Bool) then (1:ℝ) else -1) : ℝ) : ℂ) * Complex.I)
        = (2 * Real.cos (x * Λ ℓ) : ℂ)
    rw [if_pos rfl, if_neg (by decide), et, ef]
    have hkey := hcos2 (↑(x * Λ ℓ) : ℂ)
    have hcr : Complex.cos (↑(x * Λ ℓ) : ℂ) = (↑(Real.cos (x * Λ ℓ)) : ℂ) := by
      rw [Complex.ofReal_cos]
    rw [hcr] at hkey
    linear_combination -2 * hkey
  rw [show (∑ x_1 : Fin d, ∑ s : Bool, Complex.exp (((x * Λ x_1 * (if s then (1:ℝ) else -1) : ℝ) : ℂ) * Complex.I))
      = ∑ ℓ : Fin d, (2 * Real.cos (x * Λ ℓ) : ℂ) from Finset.sum_congr rfl (fun ℓ _ => hterm ℓ)]
  rw [← Finset.mul_sum]
  push_cast
  have hd0 : (d:ℂ) ≠ 0 := by
    have : (d:ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    exact_mod_cast this
  field_simp

/-- **The characteristic function of a general linear combination of the rescaled `d`-
dimensional simple random walk, over both times and coordinates, is the cosine-average
product over steps.** The `d`-dimensional analogue of `charFun_walkFddLaw`. -/
theorem charFun_spatWalkFdd (d m : ℕ) (hd : 1 ≤ d) (t : Fin m → Fin d → ℝ) (ts : Fin m → ℝ) (T : ℝ)
    (hts : ∀ i, ts i ∈ Set.Icc (0:ℝ) T) (n : ℕ) :
    charFun ((walkLaw d).map (fun p => ∑ i, ∑ ℓ, t i ℓ *
        spatialScaledSite n (walkPath (0:Site d) p ⌊(n:ℝ)*ts i⌋₊) ℓ)) (1:ℝ)
      = ∏ j ∈ Finset.range ⌊(n:ℝ)*T⌋₊, ((1/d:ℝ) * ∑ ℓ : Fin d,
          Real.cos ((∑ i, if j < ⌊(n:ℝ)*ts i⌋₊ then t i ℓ else 0) / Real.sqrt n) : ℂ) := by
  classical
  haveI := stepLaw_isProbability hd
  haveI : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  set k : Fin m → ℕ := fun i => ⌊(n:ℝ)*ts i⌋₊ with hk
  set K : ℕ := ⌊(n:ℝ)*T⌋₊ with hK
  set Λ : ℕ → Fin d → ℝ := fun j ℓ => ∑ i, if j < k i then t i ℓ else 0 with hΛdef
  have hkK : ∀ i, k i ≤ K := fun i => Nat.floor_mono (mul_le_mul_of_nonneg_left (hts i).2 (Nat.cast_nonneg n))
  have hcomb : ∀ p : ℕ → Fin d × Bool,
      (∑ i, ∑ ℓ, t i ℓ * spatialScaledSite n (walkPath (0:Site d) p (k i)) ℓ)
        = (∑ j ∈ Finset.range K, ∑ ℓ : Fin d, Λ j ℓ * coordStep ℓ (p j)) / Real.sqrt n := by
    intro p
    have hstep : ∀ i ℓ, spatialScaledSite n (walkPath (0:Site d) p (k i)) ℓ = coordSum ℓ (k i) p / Real.sqrt n := by
      intro i ℓ; unfold spatialScaledSite; rw [coordSum_eq_walkPath]
    calc ∑ i, ∑ ℓ, t i ℓ * spatialScaledSite n (walkPath (0:Site d) p (k i)) ℓ
        = ∑ i, ∑ ℓ, t i ℓ * (coordSum ℓ (k i) p / Real.sqrt n) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ℓ _ => by rw [hstep i ℓ]
      _ = (∑ i, ∑ ℓ, t i ℓ * coordSum ℓ (k i) p) / Real.sqrt n := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun ℓ _ => by ring
      _ = (∑ ℓ : Fin d, ∑ i, t i ℓ * coordSum ℓ (k i) p) / Real.sqrt n := by rw [Finset.sum_comm]
      _ = (∑ ℓ : Fin d, ∑ j ∈ Finset.range K, Λ j ℓ * coordStep ℓ (p j)) / Real.sqrt n := by
          congr 1
          exact Finset.sum_congr rfl fun ℓ _ =>
            sum_range_swap_indicator k K hkK (fun i => t i ℓ) (fun j => coordStep ℓ (p j))
      _ = (∑ j ∈ Finset.range K, ∑ ℓ : Fin d, Λ j ℓ * coordStep ℓ (p j)) / Real.sqrt n := by
          rw [Finset.sum_comm]
  have hcoordvan : ∀ (j : ℕ) (b : Fin d × Bool),
      (∑ ℓ : Fin d, Λ j ℓ * coordStep ℓ b) = Λ j b.1 * (if b.2 then (1:ℝ) else -1) := by
    intro j b
    rw [Finset.sum_eq_single b.1]
    · rw [coordStep_eq, if_pos rfl]
    · intro ℓ _ hne
      rw [coordStep_eq, if_neg hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ b.1) h
  have hcombY : ∀ p : ℕ → Fin d × Bool,
      (∑ i, ∑ ℓ, t i ℓ * spatialScaledSite n (walkPath (0:Site d) p (k i)) ℓ)
        = (∑ j ∈ Finset.range K, Λ j (p j).1 * (if (p j).2 then (1:ℝ) else -1)) / Real.sqrt n := by
    intro p
    rw [hcomb p]
    congr 1
    exact Finset.sum_congr rfl fun j _ => hcoordvan j (p j)
  have hmapeq : ((walkLaw d).map (fun p => ∑ i, ∑ ℓ, t i ℓ *
        spatialScaledSite n (walkPath (0:Site d) p (k i)) ℓ))
      = (walkLaw d).map (fun p =>
        (∑ j ∈ Finset.range K, Λ j (p j).1 * (if (p j).2 then (1:ℝ) else -1)) / Real.sqrt n) := by
    apply Measure.map_congr
    filter_upwards with p
    exact hcombY p
  rw [hmapeq]
  have hgmeas : ∀ j : ℕ, Measurable (fun b : Fin d × Bool => Λ j b.1 * (if b.2 then (1:ℝ) else -1)) :=
    fun j => Measurable.of_discrete
  have hcont : Continuous
      (fun x : ℝ => Complex.exp ((↑x : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hone : ∀ x : ℝ, (inner ℝ x (1 : ℝ) : ℝ) = x := by
    intro x; rw [RCLike.inner_apply]; simp
  have hfdep : Measurable (fun p : ℕ → Fin d × Bool =>
      (∑ j ∈ Finset.range K, Λ j (p j).1 * (if (p j).2 then (1:ℝ) else -1)) / Real.sqrt n) := by
    refine measurable_of_finite_dependence hd K _ fun p q hpq => ?_
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [hpq j hj]
  rw [charFun_apply]
  simp_rw [hone]
  rw [integral_map hfdep.aemeasurable hcont.aestronglyMeasurable]
  have hexpand : ∀ p : ℕ → Fin d × Bool,
      Complex.exp (((((∑ j ∈ Finset.range K, Λ j (p j).1 * (if (p j).2 then (1:ℝ) else -1)) / Real.sqrt n) : ℝ) : ℂ)
          * Complex.I)
        = ∏ j ∈ Finset.range K, Complex.exp
          (((Λ j (p j).1 * (if (p j).2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) * Complex.I) := by
    intro p
    have hcast : ((((∑ j ∈ Finset.range K, Λ j (p j).1 * (if (p j).2 then (1:ℝ) else -1)) / Real.sqrt n) : ℝ) : ℂ)
        = ∑ j ∈ Finset.range K, ((Λ j (p j).1 * (if (p j).2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) := by
      rw [Finset.sum_div]
      push_cast
      rfl
    rw [hcast, Finset.sum_mul, Complex.exp_sum]
  simp_rw [hexpand]
  have hIndep : (∫ p, ∏ j ∈ Finset.range K, Complex.exp
        (((Λ j (p j).1 * (if (p j).2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) * Complex.I) ∂(walkLaw d))
      = ∏ j ∈ Finset.range K, ∫ p, Complex.exp
        (((Λ j (p j).1 * (if (p j).2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) * Complex.I) ∂(walkLaw d) := by
    have hind : iIndepFun (fun (j : ℕ) (p : ℕ → Fin d × Bool) =>
        Complex.exp (((Λ j (p j).1 * (if (p j).2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) * Complex.I))
        (walkLaw d) :=
      iIndepFun_infinitePi (X := fun (j : ℕ) (b : Fin d × Bool) =>
        Complex.exp (((Λ j b.1 * (if b.2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) * Complex.I))
        (fun _ => Measurable.of_discrete)
    have hind' := hind.precomp (g := fun jj : Fin K => (jj : ℕ)) Fin.val_injective
    have hmeas : ∀ jj : Fin K, AEStronglyMeasurable (fun p : ℕ → Fin d × Bool =>
        Complex.exp (((Λ (jj:ℕ) (p (jj:ℕ)).1 * (if (p (jj:ℕ)).2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ)
          * Complex.I)) (walkLaw d) :=
      fun jj => ((Measurable.of_discrete (f := fun b : Fin d × Bool =>
          Complex.exp (((Λ (jj:ℕ) b.1 * (if b.2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) * Complex.I))).comp
        (measurable_pi_apply (jj:ℕ))).aestronglyMeasurable
    have keyL := hind'.integral_fun_prod_eq_prod_integral hmeas
    calc ∫ p, ∏ j ∈ Finset.range K, Complex.exp
          (((Λ j (p j).1 * (if (p j).2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) * Complex.I) ∂(walkLaw d)
        = ∫ p, ∏ jj : Fin K, Complex.exp
          (((Λ (jj:ℕ) (p (jj:ℕ)).1 * (if (p (jj:ℕ)).2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) * Complex.I)
          ∂(walkLaw d) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          exact (Fin.prod_univ_eq_prod_range (fun j => Complex.exp
            (((Λ j (p j).1 * (if (p j).2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) * Complex.I)) K).symm
      _ = ∏ jj : Fin K, ∫ p, Complex.exp
          (((Λ (jj:ℕ) (p (jj:ℕ)).1 * (if (p (jj:ℕ)).2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) * Complex.I)
          ∂(walkLaw d) := keyL
      _ = ∏ j ∈ Finset.range K, ∫ p, Complex.exp
          (((Λ j (p j).1 * (if (p j).2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) * Complex.I) ∂(walkLaw d) :=
          Fin.prod_univ_eq_prod_range (fun j => ∫ p, Complex.exp
            (((Λ j (p j).1 * (if (p j).2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) * Complex.I) ∂(walkLaw d)) K
  rw [hIndep]
  have hfactor : ∀ j : ℕ, (∫ p, Complex.exp
        (((Λ j (p j).1 * (if (p j).2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) * Complex.I) ∂(walkLaw d))
      = ((1/d:ℝ) * ∑ ℓ : Fin d, Real.cos ((Λ j ℓ) / Real.sqrt n) : ℂ) := by
    intro j
    have hmap : (walkLaw d).map (fun p : ℕ → Fin d × Bool => p j) = stepLaw d :=
      Measure.infinitePi_map_eval _ _
    have hgmeas' : Measurable (fun b : Fin d × Bool =>
        Complex.exp (((Λ j b.1 * (if b.2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) * Complex.I)) :=
      Measurable.of_discrete
    have hpull : (∫ b, Complex.exp
          (((Λ j b.1 * (if b.2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) * Complex.I)
          ∂((walkLaw d).map (fun p : ℕ → Fin d × Bool => p j)))
        = ∫ p, Complex.exp
          (((Λ j (p j).1 * (if (p j).2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) * Complex.I) ∂(walkLaw d) :=
      integral_map (measurable_pi_apply j).aemeasurable hgmeas'.aestronglyMeasurable
    rw [hmap] at hpull
    have h1 : (∫ p, Complex.exp
          (((Λ j (p j).1 * (if (p j).2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) * Complex.I) ∂(walkLaw d))
        = ∫ b, Complex.exp (((Λ j b.1 * (if b.2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) * Complex.I)
          ∂(stepLaw d) := hpull.symm
    rw [h1]
    have hrw : ∀ b : Fin d × Bool, ((Λ j b.1 * (if b.2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ)
        = ((((1/Real.sqrt n) * Λ j b.1 * (if b.2 then (1:ℝ) else -1) : ℝ)) : ℂ) := by
      intro b; push_cast; ring
    simp_rw [hrw]
    have hkey := spat_integral_stepLaw_cexp d hd (1/Real.sqrt n) (Λ j)
    rw [hkey]
    congr 2
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    congr 1
    ring
  rw [show (∏ j ∈ Finset.range K, ((1/d:ℝ) * ∑ ℓ : Fin d, Real.cos ((Λ j ℓ) / Real.sqrt n) : ℂ))
      = ∏ j ∈ Finset.range K, ∫ p, Complex.exp
        (((Λ j (p j).1 * (if (p j).2 then (1:ℝ) else -1) / Real.sqrt n : ℝ) : ℂ) * Complex.I) ∂(walkLaw d) from
    Finset.prod_congr rfl fun j _ => (hfactor j).symm]

/-- **The finite-dimensional characteristic function of the rescaled `d`-dimensional simple
random walk converges, at every linear combination over evaluation times and coordinates,
to that of `d` independent real Brownian motions of variance rate `1/d`.** The `d`-
dimensional analogue of `tendsto_charFun_walkFddLaw`; matches, via `Q`, the covariance
`LatticeProb.IsBrownianSpace`'s own coordinates carry. -/
theorem tendsto_charFun_spatWalkFdd (d m : ℕ) (hd : 1 ≤ d) (t : Fin m → Fin d → ℝ) (ts : Fin m → ℝ) (T : ℝ)
    (hts : ∀ i, ts i ∈ Set.Icc (0:ℝ) T) :
    Tendsto (fun n : ℕ => charFun ((walkLaw d).map (fun p => ∑ i, ∑ ℓ, t i ℓ *
        spatialScaledSite n (walkPath (0:Site d) p ⌊(n:ℝ)*ts i⌋₊) ℓ)) (1:ℝ)) atTop
      (𝓝 (Complex.exp (-((∑ ℓ : Fin d, ∑ i, ∑ i', t i ℓ * t i' ℓ * min (ts i) (ts i') : ℝ) : ℂ) / (2*d)))) := by
  classical
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  set k : ℕ → Fin m → ℕ := fun n i => ⌊(n:ℝ)*ts i⌋₊ with hk
  set K : ℕ → ℕ := fun n => ⌊(n:ℝ)*T⌋₊ with hK
  set Λ : ℕ → ℕ → Fin d → ℝ := fun n j ℓ => ∑ i, if j < k n i then t i ℓ else 0 with hΛ
  set S : ℝ := ∑ ℓ : Fin d, ∑ i, |t i ℓ| with hS
  set Q : ℝ := ∑ ℓ : Fin d, ∑ i, ∑ i', t i ℓ * t i' ℓ * min (ts i) (ts i') with hQ
  set X2 : ℕ → ℕ → ℝ := fun n j => (1/(2*d):ℝ) * ∑ ℓ : Fin d, (Λ n j ℓ / Real.sqrt n)^2 with hX2
  have hkK : ∀ n i, k n i ≤ K n := fun n i =>
    Nat.floor_mono (mul_le_mul_of_nonneg_left (hts i).2 (Nat.cast_nonneg n))
  -- 1. uniform bound on Λ
  have hLbound : ∀ n j ℓ, |Λ n j ℓ| ≤ S := by
    intro n j ℓ
    calc |Λ n j ℓ| ≤ ∑ i, |if j < k n i then t i ℓ else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |t i ℓ| := Finset.sum_le_sum fun i _ => by split_ifs <;> simp
      _ ≤ S := Finset.single_le_sum (f := fun ℓ' => ∑ i, |t i ℓ'|)
          (fun ℓ' _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ ℓ)
  have hSnonneg : 0 ≤ S := Finset.sum_nonneg fun ℓ _ => Finset.sum_nonneg fun i _ => abs_nonneg _
  -- 2. exact combinatorial identity for X2 sum
  have hX2sum : ∀ n : ℕ, 0 < n → ∑ j ∈ Finset.range (K n), X2 n j
      = (1/(2*d):ℝ) * ∑ ℓ : Fin d, ∑ i, ∑ i', t i ℓ * t i' ℓ * (((min (k n i) (k n i') : ℕ):ℝ)/n) := by
    intro n hn0
    have hnR : (0:ℝ) < n := by exact_mod_cast hn0
    have hsqn : (Real.sqrt n)^2 = n := Real.sq_sqrt (le_of_lt hnR)
    rw [hX2]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    have hdiv : ∀ j : ℕ, (Λ n j ℓ / Real.sqrt n)^2 = (Λ n j ℓ)^2 / n := by
      intro j; rw [div_pow, hsqn]
    simp_rw [hdiv]
    rw [← Finset.sum_div, sum_sq_indicator (fun i => t i ℓ) (k n) (K n) (hkK n)]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Nat.cast_min, mul_div_assoc]
  -- 3. limit of X2 sum
  have hX2lim : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (K n), X2 n j) atTop (𝓝 ((1/(2*d):ℝ)*Q)) := by
    have heq : (fun n : ℕ => ∑ j ∈ Finset.range (K n), X2 n j) =ᶠ[atTop]
        (fun n : ℕ => (1/(2*d):ℝ) * ∑ ℓ : Fin d, ∑ i, ∑ i',
          t i ℓ * t i' ℓ * (((min (k n i) (k n i') : ℕ):ℝ)/n)) := by
      filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
      exact hX2sum n hn
    refine Tendsto.congr' heq.symm ?_
    have hminlim : ∀ i i', Tendsto (fun n : ℕ => (((min (k n i) (k n i') : ℕ):ℝ)/n)) atTop (𝓝 (min (ts i) (ts i'))) := by
      intro i i'
      have hm : ∀ n : ℕ, ((min (k n i) (k n i') : ℕ):ℝ)/n = (⌊(n:ℝ)*min (ts i) (ts i')⌋₊ : ℝ)/n := by
        intro n
        congr 2
        rw [← Monotone.map_min Nat.floor_mono, mul_min_of_nonneg (ts i) (ts i') (Nat.cast_nonneg n)]
      refine (tendsto_nat_floor_div (min (ts i) (ts i')) (le_min (hts i).1 (hts i').1)).congr' ?_
      filter_upwards with n
      exact (hm n).symm
    have hsum : Tendsto (fun n : ℕ => ∑ ℓ : Fin d, ∑ i, ∑ i',
        t i ℓ * t i' ℓ * (((min (k n i) (k n i') : ℕ):ℝ)/n)) atTop (𝓝 Q) := by
      rw [hQ]
      refine tendsto_finsetSum Finset.univ fun ℓ _ => ?_
      refine tendsto_finsetSum Finset.univ fun i _ => ?_
      refine tendsto_finsetSum Finset.univ fun i' _ => ?_
      exact (hminlim i i').const_mul (t i ℓ * t i' ℓ)
    exact hsum.const_mul (1/(2*d):ℝ)
  -- 4. the remainder-to-zero argument
  set δ : ℕ → ℝ := fun n => S / Real.sqrt n with hδ
  set W : ℕ → ℝ := fun n => δ n ^ 2 / 2 with hW
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (Real.sqrt (n:ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have h2 := h1.const_mul S
    rw [mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards with n
    rw [hδ]; ring
  have hWlim : Tendsto W atTop (𝓝 0) := by
    have := (hδlim.pow 2).div_const (2:ℝ)
    simpa [hW] using this
  have hw_le_X2 : ∀ n j, 0 < n →
      (1/d:ℝ) * ∑ ℓ : Fin d, (1 - Real.cos (Λ n j ℓ / Real.sqrt n)) ≤ X2 n j := by
    intro n j hn0
    rw [hX2]
    have hd0 : (0:ℝ) < d := hdR
    have hkey : ∑ ℓ : Fin d, (1 - Real.cos (Λ n j ℓ / Real.sqrt n))
        ≤ ∑ ℓ : Fin d, (Λ n j ℓ / Real.sqrt n) ^ 2 / 2 :=
      Finset.sum_le_sum fun ℓ _ => one_sub_cos_le_sq_div_two (Λ n j ℓ / Real.sqrt n)
    calc (1/d:ℝ) * ∑ ℓ : Fin d, (1 - Real.cos (Λ n j ℓ / Real.sqrt n))
        ≤ (1/d:ℝ) * ∑ ℓ : Fin d, (Λ n j ℓ / Real.sqrt n) ^ 2 / 2 :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = (1/(2*d):ℝ) * ∑ ℓ : Fin d, (Λ n j ℓ / Real.sqrt n) ^ 2 := by
          rw [← Finset.sum_div]; ring
  have hw_nonneg : ∀ n j, 0 ≤ (1/d:ℝ) * ∑ ℓ : Fin d, (1 - Real.cos (Λ n j ℓ / Real.sqrt n)) := by
    intro n j
    have : (0:ℝ) ≤ 1/d := by positivity
    exact mul_nonneg this (Finset.sum_nonneg fun ℓ _ => one_sub_cos_nonneg _)
  have hX2_le_W : ∀ n j, 0 < n → X2 n j ≤ W n := by
    intro n j hn0
    have hnR : (0:ℝ) < n := by exact_mod_cast hn0
    rw [hX2, hW]
    have hterm : ∀ ℓ : Fin d, (Λ n j ℓ / Real.sqrt n)^2 ≤ δ n ^ 2 := by
      intro ℓ
      rw [hδ]
      have h1 : |Λ n j ℓ / Real.sqrt n| ≤ S / Real.sqrt n := by
        rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact div_le_div_of_nonneg_right (hLbound n j ℓ) (Real.sqrt_pos.mpr hnR).le
      calc (Λ n j ℓ / Real.sqrt n)^2 = |Λ n j ℓ / Real.sqrt n|^2 := (sq_abs _).symm
        _ ≤ (S / Real.sqrt n)^2 := by
            have h2 : 0 ≤ S / Real.sqrt n := by positivity
            exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    calc (1/(2*d):ℝ) * ∑ ℓ : Fin d, (Λ n j ℓ / Real.sqrt n)^2
        ≤ (1/(2*d):ℝ) * ∑ _ℓ : Fin d, δ n ^ 2 := by
          have hpos : (0:ℝ) ≤ 1/(2*d) := by positivity
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ℓ _ => hterm ℓ) hpos
      _ = δ n ^ 2 / 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          field_simp
          ring
  -- 5. the pointwise remainder bound, valid once δ n ≤ 1
  have hrbound : ∀ n j : ℕ, δ n ≤ 1 →
      |Real.log ((1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n)) + X2 n j|
        ≤ 3 * W n * X2 n j := by
    intro n j hδ1
    set w : ℝ := (1/d:ℝ) * ∑ ℓ : Fin d, (1 - Real.cos (Λ n j ℓ / Real.sqrt n)) with hwdef
    have hcoseq : (1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n) = 1 - w := by
      have hsumeq : (1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n)
          + (1/d:ℝ) * ∑ ℓ : Fin d, (1 - Real.cos (Λ n j ℓ / Real.sqrt n)) = 1 := by
        rw [← mul_add, ← Finset.sum_add_distrib]
        have hpt : ∀ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n)
            + (1 - Real.cos (Λ n j ℓ / Real.sqrt n)) = 1 := fun ℓ => by ring
        rw [Finset.sum_congr rfl (fun ℓ (_ : ℓ ∈ (Finset.univ : Finset (Fin d))) => hpt ℓ)]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        have hd0 : (d:ℝ) ≠ 0 := by positivity
        field_simp
      rw [← hwdef] at hsumeq
      linarith [hsumeq]
    -- eventually 0 < n case handled by caller; here just need w's bounds, no n>0 assumption needed
    have hnn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    by_cases hn0 : n = 0
    · -- degenerate: Real.sqrt 0 = 0, division by zero gives junk 0 for every Λ/√n term
      subst hn0
      simp only [Nat.cast_zero, Real.sqrt_zero, div_zero] at *
      have hd0 : (d:ℝ) ≠ 0 := by positivity
      norm_num [inv_mul_cancel₀ hd0]
      rw [hX2]
      norm_num
    · have hn0' : 0 < n := Nat.pos_of_ne_zero hn0
      have hw_le := hw_le_X2 n j hn0'
      have hw_nn := hw_nonneg n j
      have hX2W := hX2_le_W n j hn0'
      have hwW : w ≤ W n := le_trans hw_le hX2W
      have hWval : W n = δ n ^ 2 / 2 := by rw [hW]
      have hδnonneg : 0 ≤ δ n := by rw [hδ]; positivity
      have hwhalf : w ≤ 1/2 := by
        have hWle : W n ≤ 1/2 := by
          rw [hWval]
          nlinarith [hδ1, hδnonneg]
        linarith [hwW, hWle]
      have hwlt1 : |w| < 1 := by rw [abs_of_nonneg hw_nn]; linarith
      -- Term A
      have hTermA : |w + Real.log (1 - w)| ≤ w^2 / (1 - |w|) := by
        have := Real.abs_log_sub_add_sum_range_le hwlt1 1
        simpa using this
      have hTermA' : |w + Real.log (1 - w)| ≤ 2 * w^2 := by
        have h1 : (1:ℝ) - |w| ≥ 1/2 := by rw [abs_of_nonneg hw_nn]; linarith
        have h2 : w^2 / (1 - |w|) ≤ 2 * w^2 := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith [sq_nonneg w]
        linarith [hTermA, h2]
      -- Term B
      have hTermB : |X2 n j - w| ≤ (5/24) * W n * X2 n j := by
        have hbound1 : ∀ ℓ : Fin d, |1 - Real.cos (Λ n j ℓ / Real.sqrt n) - (Λ n j ℓ / Real.sqrt n)^2/2|
            ≤ (5/96) * (Λ n j ℓ / Real.sqrt n)^4 := by
          intro ℓ
          have hle1 : |Λ n j ℓ / Real.sqrt n| ≤ 1 := by
            calc |Λ n j ℓ / Real.sqrt n| ≤ δ n := by
                  rw [hδ, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
                  exact div_le_div_of_nonneg_right (hLbound n j ℓ) (Real.sqrt_pos.mpr
                    (by exact_mod_cast hn0')).le
              _ ≤ 1 := hδ1
          have hcb := Real.cos_bound hle1
          have heq : Real.cos (Λ n j ℓ / Real.sqrt n) - (1 - (Λ n j ℓ / Real.sqrt n)^2/2)
              = -(1 - Real.cos (Λ n j ℓ / Real.sqrt n) - (Λ n j ℓ / Real.sqrt n)^2/2) := by ring
          rw [heq, abs_neg, mul_comm] at hcb
          have habs4 : |Λ n j ℓ / Real.sqrt n|^4 = (Λ n j ℓ / Real.sqrt n)^4 := by
            rw [show (4:ℕ) = 2*2 from rfl, pow_mul, pow_mul, sq_abs]
          rwa [habs4] at hcb
        have hbound2 : ∀ ℓ : Fin d, (Λ n j ℓ / Real.sqrt n)^4
            ≤ (δ n)^2 * (Λ n j ℓ / Real.sqrt n)^2 := by
          intro ℓ
          have h1 : |Λ n j ℓ / Real.sqrt n| ≤ δ n := by
            rw [hδ, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
            exact div_le_div_of_nonneg_right (hLbound n j ℓ) (Real.sqrt_pos.mpr
              (by exact_mod_cast hn0')).le
          have h2 : (Λ n j ℓ / Real.sqrt n)^2 ≤ (δ n)^2 := by
            calc (Λ n j ℓ / Real.sqrt n)^2 = |Λ n j ℓ / Real.sqrt n|^2 := (sq_abs _).symm
              _ ≤ (δ n)^2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
          calc (Λ n j ℓ / Real.sqrt n)^4 = (Λ n j ℓ / Real.sqrt n)^2 * (Λ n j ℓ / Real.sqrt n)^2 := by
                ring
            _ ≤ (δ n)^2 * (Λ n j ℓ / Real.sqrt n)^2 := by
                have h3 : (0:ℝ) ≤ (Λ n j ℓ / Real.sqrt n)^2 := sq_nonneg _
                exact mul_le_mul_of_nonneg_right h2 h3
        have hX2eq2 : X2 n j = (1/d:ℝ) * ∑ ℓ : Fin d, (Λ n j ℓ / Real.sqrt n)^2/2 := by
          show (1/(2*d):ℝ) * ∑ ℓ : Fin d, (Λ n j ℓ / Real.sqrt n)^2
              = (1/d:ℝ) * ∑ ℓ : Fin d, (Λ n j ℓ / Real.sqrt n)^2/2
          rw [← Finset.sum_div]
          ring
        have heqXw : X2 n j - w = (1/d:ℝ) * ∑ ℓ : Fin d,
            ((Λ n j ℓ / Real.sqrt n)^2/2 - (1 - Real.cos (Λ n j ℓ / Real.sqrt n))) := by
          rw [hX2eq2, hwdef, ← mul_sub]
          congr 1
          exact (Finset.sum_sub_distrib (fun ℓ : Fin d => (Λ n j ℓ / Real.sqrt n)^2/2)
            (fun ℓ : Fin d => 1 - Real.cos (Λ n j ℓ / Real.sqrt n))).symm
        have hsum1 : |X2 n j - w| ≤ (1/d:ℝ) * ∑ ℓ : Fin d,
            |1 - Real.cos (Λ n j ℓ / Real.sqrt n) - (Λ n j ℓ / Real.sqrt n)^2/2| := by
          rw [heqXw]
          calc |(1/d:ℝ) * ∑ ℓ : Fin d,
                ((Λ n j ℓ / Real.sqrt n)^2/2 - (1 - Real.cos (Λ n j ℓ / Real.sqrt n)))|
              = (1/d:ℝ) * |∑ ℓ : Fin d,
                ((Λ n j ℓ / Real.sqrt n)^2/2 - (1 - Real.cos (Λ n j ℓ / Real.sqrt n)))| := by
                rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/d)]
            _ ≤ (1/d:ℝ) * ∑ ℓ : Fin d,
                |(Λ n j ℓ / Real.sqrt n)^2/2 - (1 - Real.cos (Λ n j ℓ / Real.sqrt n))| := by
                exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
            _ = (1/d:ℝ) * ∑ ℓ : Fin d,
                |1 - Real.cos (Λ n j ℓ / Real.sqrt n) - (Λ n j ℓ / Real.sqrt n)^2/2| := by
                congr 1
                refine Finset.sum_congr rfl fun ℓ _ => ?_
                rw [abs_sub_comm]
        have hSumSqX2 : (1/d:ℝ) * ∑ ℓ : Fin d, (Λ n j ℓ / Real.sqrt n)^2 = 2 * X2 n j := by
          show (1/d:ℝ) * ∑ ℓ : Fin d, (Λ n j ℓ / Real.sqrt n)^2
              = 2 * ((1/(2*d):ℝ) * ∑ ℓ : Fin d, (Λ n j ℓ / Real.sqrt n)^2)
          ring
        calc |X2 n j - w| ≤ (1/d:ℝ) * ∑ ℓ : Fin d,
              |1 - Real.cos (Λ n j ℓ / Real.sqrt n) - (Λ n j ℓ / Real.sqrt n)^2/2| := hsum1
          _ ≤ (1/d:ℝ) * ∑ ℓ : Fin d, (5/96) * (Λ n j ℓ / Real.sqrt n)^4 :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ℓ _ => hbound1 ℓ) (by positivity)
          _ ≤ (1/d:ℝ) * ∑ ℓ : Fin d, (5/96) * ((δ n)^2 * (Λ n j ℓ / Real.sqrt n)^2) := by
              refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ℓ _ => ?_) (by positivity)
              exact mul_le_mul_of_nonneg_left (hbound2 ℓ) (by norm_num)
          _ = (5/96) * (δ n)^2 * ((1/d:ℝ) * ∑ ℓ : Fin d, (Λ n j ℓ / Real.sqrt n)^2) := by
              rw [Finset.mul_sum, Finset.mul_sum]
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun ℓ _ => ?_
              ring
          _ = (5/96) * (δ n)^2 * (2 * X2 n j) := by rw [hSumSqX2]
          _ = (5/48) * (δ n)^2 * X2 n j := by ring
          _ = (5/24) * W n * X2 n j := by rw [hW]; ring
      have hexpand : Real.log ((1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n)) + X2 n j
          = (w + Real.log (1 - w)) + (X2 n j - w) := by
        rw [hcoseq]; ring
      rw [hexpand]
      calc |(w + Real.log (1 - w)) + (X2 n j - w)|
          ≤ |w + Real.log (1 - w)| + |X2 n j - w| := abs_add_le _ _
        _ ≤ 2 * w^2 + (5/24) * W n * X2 n j := by linarith [hTermA', hTermB]
        _ ≤ 2 * (W n * X2 n j) + (5/24) * W n * X2 n j := by
            have : w^2 ≤ W n * X2 n j := by nlinarith [hwW, hw_le, hX2W]
            linarith [this]
        _ ≤ 3 * W n * X2 n j := by nlinarith [hWlim, hX2W]
  -- 6. assembling the sum-of-logs limit
  have hev1 : ∀ᶠ n : ℕ in atTop, δ n ≤ 1 := hδlim.eventually (eventually_le_nhds (by norm_num))
  have hboundedX2 : ∃ M : ℝ, ∀ᶠ n : ℕ in atTop, ∑ j ∈ Finset.range (K n), X2 n j ≤ M := by
    refine ⟨(1/(2*d):ℝ)*Q + 1, ?_⟩
    exact hX2lim.eventually (eventually_le_nhds (by linarith))
  obtain ⟨M, hMev⟩ := hboundedX2
  have hnonnegX2sum : ∀ n, 0 ≤ ∑ j ∈ Finset.range (K n), X2 n j := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      apply Finset.sum_nonneg
      intro j _
      rw [hX2]
      positivity
    · apply Finset.sum_nonneg
      intro j _
      have := hw_le_X2 n j hpos
      have hnn2 := hw_nonneg n j
      linarith
  have hrsum : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (K n),
      (Real.log ((1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n)) + X2 n j)) atTop (𝓝 0) := by
    have hbound : ∀ᶠ n : ℕ in atTop, |∑ j ∈ Finset.range (K n),
        (Real.log ((1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n)) + X2 n j)|
          ≤ 3 * W n * M := by
      filter_upwards [hev1, hMev] with n hδ1 hM
      calc |∑ j ∈ Finset.range (K n),
            (Real.log ((1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n)) + X2 n j)|
          ≤ ∑ j ∈ Finset.range (K n),
            |Real.log ((1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n)) + X2 n j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.range (K n), 3 * W n * X2 n j :=
            Finset.sum_le_sum fun j _ => hrbound n j hδ1
        _ = 3 * W n * ∑ j ∈ Finset.range (K n), X2 n j := by
            rw [← Finset.mul_sum]
        _ ≤ 3 * W n * M := by
            have hWnn : 0 ≤ W n := by rw [hW]; positivity
            exact mul_le_mul_of_nonneg_left hM (by positivity)
    have hzero : Tendsto (fun n : ℕ => 3 * W n * M) atTop (𝓝 0) := by
      have := (hWlim.const_mul (3:ℝ)).mul_const M
      simpa using this
    have hnegzero : Tendsto (fun n : ℕ => -(3 * W n * M)) atTop (𝓝 0) := by
      have := hzero.neg
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hnegzero hzero ?_ ?_
    · filter_upwards [hbound] with n hn
      have := (neg_abs_le _).trans hn
      linarith [abs_le.mp hn]
    · filter_upwards [hbound] with n hn
      linarith [abs_le.mp hn]
  have hlogsum : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (K n),
      Real.log ((1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n))) atTop
      (𝓝 (-((1/(2*d):ℝ)*Q))) := by
    have heq : (fun n : ℕ => ∑ j ∈ Finset.range (K n),
        Real.log ((1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n)))
        = (fun n => (∑ j ∈ Finset.range (K n),
            (Real.log ((1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n)) + X2 n j))
          - ∑ j ∈ Finset.range (K n), X2 n j) := by
      funext n
      have hadd : (∑ j ∈ Finset.range (K n),
          (Real.log ((1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n)) + X2 n j))
          = (∑ j ∈ Finset.range (K n),
              Real.log ((1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n)))
            + ∑ j ∈ Finset.range (K n), X2 n j :=
        Finset.sum_add_distrib
      rw [hadd]
      ring
    rw [heq]
    have := hrsum.sub hX2lim
    simpa using this
  -- 7. lift to the product, via exp
  have hev2 : ∀ᶠ n : ℕ in atTop, ∀ j ∈ Finset.range (K n),
      (0:ℝ) < (1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n) := by
    filter_upwards [hev1] with n hδ1
    intro j _
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have hd0 : (d:ℝ) ≠ 0 := by positivity
      norm_num [inv_mul_cancel₀ hd0]
    · have hw_le := hw_le_X2 n j hpos
      have hX2W := hX2_le_W n j hpos
      have hWval : W n = δ n ^ 2 / 2 := by rw [hW]
      have hδnonneg : 0 ≤ δ n := by rw [hδ]; positivity
      have hwhalf : (1/d:ℝ) * ∑ ℓ : Fin d, (1 - Real.cos (Λ n j ℓ / Real.sqrt n)) < 1 := by
        have hWle : W n ≤ 1/2 := by rw [hWval]; nlinarith [hδ1, hδnonneg]
        linarith [hw_le, hX2W, hWle]
      have hsumeq : (1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n)
          + (1/d:ℝ) * ∑ ℓ : Fin d, (1 - Real.cos (Λ n j ℓ / Real.sqrt n)) = 1 := by
        rw [← mul_add, ← Finset.sum_add_distrib]
        have hpt : ∀ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n)
            + (1 - Real.cos (Λ n j ℓ / Real.sqrt n)) = 1 := fun ℓ => by ring
        rw [Finset.sum_congr rfl (fun ℓ (_ : ℓ ∈ (Finset.univ : Finset (Fin d))) => hpt ℓ)]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        have hd0 : (d:ℝ) ≠ 0 := by positivity
        field_simp
      linarith [hsumeq, hwhalf]
  have hprod_eq_exp : ∀ᶠ n : ℕ in atTop, ∏ j ∈ Finset.range (K n),
      (1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n)
      = Real.exp (∑ j ∈ Finset.range (K n),
          Real.log ((1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n))) := by
    filter_upwards [hev2] with n hpos
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun j hj => (Real.exp_log (hpos j hj)).symm
  have hprodlim : Tendsto (fun n : ℕ => ∏ j ∈ Finset.range (K n),
      (1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n)) atTop
      (𝓝 (Real.exp (-((1/(2*d):ℝ)*Q)))) := by
    refine Tendsto.congr' (hprod_eq_exp.mono (fun n h => h.symm)) ?_
    exact (Real.continuous_exp.tendsto _).comp hlogsum
  -- 8. cast to ℂ and match charFun_spatWalkFdd
  have hcastlim : Tendsto (fun n : ℕ => ((∏ j ∈ Finset.range (K n),
      (1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n) : ℝ) : ℂ)) atTop
      (𝓝 ((Real.exp (-((1/(2*d):ℝ)*Q)) : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hprodlim
  have hcastprod : ∀ n : ℕ, (∏ j ∈ Finset.range (K n),
      ((1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n) : ℂ))
      = ((∏ j ∈ Finset.range (K n), (1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n) : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    push_cast
    ring
  have hval : ((Real.exp (-((1/(2*d):ℝ)*Q)) : ℝ) : ℂ)
      = Complex.exp (-((∑ ℓ : Fin d, ∑ i, ∑ i', t i ℓ * t i' ℓ * min (ts i) (ts i') : ℝ) : ℂ) / (2*d)) := by
    rw [Complex.ofReal_exp]
    congr 1
    rw [← hQ]
    push_cast
    ring
  have hfinal : Tendsto (fun n : ℕ => ∏ j ∈ Finset.range (K n),
      ((1/d:ℝ) * ∑ ℓ : Fin d, Real.cos (Λ n j ℓ / Real.sqrt n) : ℂ)) atTop
      (𝓝 (Complex.exp (-((∑ ℓ : Fin d, ∑ i, ∑ i', t i ℓ * t i' ℓ * min (ts i) (ts i') : ℝ) : ℂ) / (2*d)))) := by
    refine Tendsto.congr' (Filter.Eventually.of_forall fun n => (hcastprod n).symm) ?_
    rw [← hval]
    exact hcastlim
  refine Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) hfinal
  exact (charFun_spatWalkFdd d m hd t ts T hts (n := n)).symm ▸ rfl

/-- **`hWalk`: the finite-dimensional convergence in law of the rescaled `d`-dimensional simple
random walk to `LatticeProb.IsBrownianSpace`.** The exact shape
`Parking.External.SpatialStoppingStability` needs as its `hWalk` hypothesis. -/
theorem hWalk_of_isBrownianSpace (d : ℕ) (hd1 : 1 ≤ d) (_hd3 : d ≤ 3)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)) (hB : IsBrownianSpace d 0 B PB)
    (T : ℝ) (_hT : 0 < T) :
    ∀ (m : ℕ) (ts : Fin m → ℝ), (∀ i, ts i ∈ Set.Icc (0 : ℝ) T) →
      ∀ F : BoundedContinuousFunction (Fin m → (Fin d → ℝ)) ℝ,
        Tendsto (fun n : ℕ =>
            ∫ p, F (fun i => spatialScaledSite n (walkPath (0 : Site d) p ⌊(n : ℝ) * ts i⌋₊))
              ∂(walkLaw d)) atTop
          (𝓝 (∫ β, F (fun i => ofBrownianSpace B (Real.toNNReal (ts i)) β) ∂PB)) := by
  intro m ts hts F
  set m' : ℕ := m * d with hm'def
  set Xdisc : ℕ → (ℕ → Fin d × Bool) → Fin m' → ℝ :=
    fun n p k => spatialScaledSite n
      (walkPath (0 : Site d) p ⌊(n:ℝ) * ts (finProdFinEquiv.symm k).1⌋₊)
      (finProdFinEquiv.symm k).2 with hXdiscdef
  set Xcont : ΩB → Fin m' → ℝ :=
    fun β k => ofBrownianSpace B (Real.toNNReal (ts (finProdFinEquiv.symm k).1)) β
      (finProdFinEquiv.symm k).2 with hXcontdef
  have hXdiscm : ∀ n : ℕ, Measurable (Xdisc n) := by
    intro n
    apply measurable_pi_lambda
    intro k
    show Measurable (fun p => spatialScaledSite n
      (walkPath (0 : Site d) p ⌊(n:ℝ) * ts (finProdFinEquiv.symm k).1⌋₊)
      (finProdFinEquiv.symm k).2)
    unfold spatialScaledSite
    have hmeas : Measurable (fun p => (walkPath (0 : Site d) p
        ⌊(n:ℝ) * ts (finProdFinEquiv.symm k).1⌋₊) (finProdFinEquiv.symm k).2) :=
      (measurable_pi_apply (finProdFinEquiv.symm k).2).comp
        (measurable_walkPath (0 : Site d) ⌊(n:ℝ) * ts (finProdFinEquiv.symm k).1⌋₊)
    exact Measurable.div_const (Measurable.comp Measurable.of_discrete hmeas) _
  set u : (Fin m' → ℝ) → (Fin m → (Fin d → ℝ)) :=
    fun g i ℓ => g (finProdFinEquiv (i, ℓ)) with hudef
  have hucont : Continuous u := by
    apply continuous_pi; intro i; apply continuous_pi; intro ℓ
    exact continuous_apply _
  have huXdisc : ∀ n p, u (Xdisc n p) = fun i => spatialScaledSite n
      (walkPath (0 : Site d) p ⌊(n:ℝ) * ts i⌋₊) := by
    intro n p
    funext i ℓ
    show Xdisc n p (finProdFinEquiv (i, ℓ)) = _
    simp only [hXdiscdef, finProdFinEquiv.symm_apply_apply]
  have huXcont : ∀ β, u (Xcont β) = fun i => ofBrownianSpace B
      (Real.toNNReal (ts i)) β := by
    intro β
    funext i ℓ
    show Xcont β (finProdFinEquiv (i, ℓ)) = _
    simp only [hXcontdef, finProdFinEquiv.symm_apply_apply]
  have hXcontAE : AEMeasurable Xcont PB := by
    apply aemeasurable_pi_iff.mpr
    intro k
    show AEMeasurable (fun β => ofBrownianSpace B
      (Real.toNNReal (ts (finProdFinEquiv.symm k).1)) β (finProdFinEquiv.symm k).2) PB
    unfold ofBrownianSpace
    show AEMeasurable (fun β => B (Real.toNNReal (ts (finProdFinEquiv.symm k).1)) β
      (finProdFinEquiv.symm k).2) PB
    exact Parking.Generic.WalkCLT.aemeasurable_isBrownianSpace_coord hd1 hB _ _
  set Z : ΩB → Fin m' → ℝ := hXcontAE.mk Xcont with hZdef
  have hZmeas : Measurable Z := hXcontAE.measurable_mk
  have hZaeeq : Xcont =ᵐ[PB] Z := hXcontAE.ae_eq_mk
  have hcomb : ∀ t' : Fin m' → ℝ,
      Tendsto (fun n : ℕ => charFun ((walkLaw d).map
          (fun p => ∑ k, t' k * Xdisc n p k)) 1) atTop
        (𝓝 (charFun (PB.map (fun β => ∑ k, t' k * Z β k)) 1)) := by
    intro t'
    set tt : Fin m → Fin d → ℝ := fun i ℓ => t' (finProdFinEquiv (i, ℓ)) with httdef
    have hLHS : ∀ n p, (∑ k : Fin m', t' k * Xdisc n p k)
        = ∑ i, ∑ ℓ, tt i ℓ * spatialScaledSite n
            (walkPath (0 : Site d) p ⌊(n:ℝ) * ts i⌋₊) ℓ := by
      intro n p
      rw [← Fintype.sum_prod_type
        (fun q : Fin m × Fin d => tt q.1 q.2 * spatialScaledSite n
          (walkPath (0 : Site d) p ⌊(n:ℝ) * ts q.1⌋₊) q.2),
        ← Equiv.sum_comp finProdFinEquiv (fun k : Fin m' => t' k * Xdisc n p k)]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [httdef, hXdiscdef, Equiv.symm_apply_apply]
    have hRHScont : ∀ β, (∑ k : Fin m', t' k * Xcont β k)
        = ∑ i, ∑ ℓ, tt i ℓ * B (Real.toNNReal (ts i)) β ℓ := by
      intro β
      rw [← Fintype.sum_prod_type
        (fun q : Fin m × Fin d => tt q.1 q.2 * B (Real.toNNReal (ts q.1)) β q.2),
        ← Equiv.sum_comp finProdFinEquiv (fun k : Fin m' => t' k * Xcont β k)]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [httdef, hXcontdef, Equiv.symm_apply_apply, ofBrownianSpace]
      rfl
    have hdisclim := tendsto_charFun_spatWalkFdd d m hd1 tt ts T hts
    have hdiscongr : (fun n : ℕ => charFun ((walkLaw d).map
        (fun p => ∑ k, t' k * Xdisc n p k)) 1)
        = fun n => charFun ((walkLaw d).map (fun p => ∑ i, ∑ ℓ, tt i ℓ *
            spatialScaledSite n
              (walkPath (0 : Site d) p ⌊(n:ℝ) * ts i⌋₊) ℓ)) 1 := by
      funext n
      rw [Measure.map_congr (Eventually.of_forall fun p => hLHS n p)]
    rw [hdiscongr]
    have hcontstep1 : (fun β => ∑ k : Fin m', t' k * Xcont β k)
        =ᵐ[PB] (fun β => ∑ k : Fin m', t' k * Z β k) := by
      filter_upwards [hZaeeq] with β hβ
      rw [hβ]
    have hcontcongr : PB.map (fun β => ∑ k, t' k * Xcont β k)
        = PB.map (fun β => ∑ k, t' k * Z β k) := Measure.map_congr hcontstep1
    have hcontval : charFun (PB.map (fun β => ∑ k, t' k * Xcont β k)) 1
        = Complex.exp
          (-((∑ ℓ : Fin d, ∑ i, ∑ i', tt i ℓ * tt i' ℓ *
              (min (Real.toNNReal (ts i)) (Real.toNNReal (ts i')) : ℝ) : ℝ) : ℂ) / (2 * d)) := by
      have hstep : (fun β => ∑ k : Fin m', t' k * Xcont β k)
          = fun β => ∑ i, ∑ ℓ, tt i ℓ * B (Real.toNNReal (ts i)) β ℓ := funext hRHScont
      rw [hstep]
      exact Parking.Generic.WalkCLT.charFun_isBrownianSpace_linearCombination hd1 hB tt
        (fun i => Real.toNNReal (ts i))
    have hmineq : ∀ i i' : Fin m,
        (min (Real.toNNReal (ts i)) (Real.toNNReal (ts i')) : ℝ) = min (ts i) (ts i') := by
      intro i i'
      rw [Real.coe_toNNReal (ts i) (hts i).1, Real.coe_toNNReal (ts i') (hts i').1]
    rw [← hcontcongr, hcontval]
    have hQeq : (∑ ℓ : Fin d, ∑ i, ∑ i', tt i ℓ * tt i' ℓ *
          (min (Real.toNNReal (ts i)) (Real.toNNReal (ts i')) : ℝ))
        = ∑ ℓ : Fin d, ∑ i, ∑ i', tt i ℓ * tt i' ℓ * (min (ts i) (ts i') : ℝ) :=
      Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun i' _ => by rw [hmineq i i']
    rw [hQeq]
    exact hdisclim
  haveI : Fact (1 ≤ d) := ⟨hd1⟩
  haveI := stepLaw_isProbability (d := d) hd1
  haveI hwlp : IsProbabilityMeasure (walkLaw d) := by
    unfold walkLaw; infer_instance
  have hTID : TendstoInDistribution Xdisc atTop Z (fun _ : ℕ => walkLaw d) PB :=
    Parking.Generic.CramerWold.tendstoInDistribution_of_tendsto_charFun_linearCombination
      hXdiscm hZmeas hcomb
  have hTIDu := hTID.continuous_comp hucont
  have hport := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hTIDu.tendsto F
  have hXum : ∀ n, Measurable (fun p => u (Xdisc n p)) :=
    fun n => hucont.measurable.comp (hXdiscm n)
  have hZum : Measurable (fun β => u (Z β)) := hucont.measurable.comp hZmeas
  have heqL : (fun n : ℕ => ∫ x, F x ∂((walkLaw d).map (fun p => u (Xdisc n p))))
      = fun n => ∫ p, F (fun i => spatialScaledSite n
          (walkPath (0 : Site d) p ⌊(n:ℝ) * ts i⌋₊)) ∂(walkLaw d) := by
    funext n
    rw [integral_map (hXum n).aemeasurable F.continuous.aestronglyMeasurable]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    show F (u (Xdisc n p)) = F (fun i => spatialScaledSite n
      (walkPath (0 : Site d) p ⌊(n:ℝ) * ts i⌋₊))
    rw [huXdisc n p]
  have heqR : (∫ x, F x ∂(PB.map (fun β => u (Z β))))
      = ∫ β, F (fun i => ofBrownianSpace B (Real.toNNReal (ts i)) β) ∂PB := by
    rw [integral_map hZum.aemeasurable F.continuous.aestronglyMeasurable]
    have hstep : (fun β => F (u (Z β))) =ᵐ[PB] fun β => F (u (Xcont β)) := by
      filter_upwards [hZaeeq] with β hβ
      show F (u (Z β)) = F (u (Xcont β))
      rw [← hβ]
    rw [integral_congr_ae hstep]
    refine integral_congr_ae (Eventually.of_forall fun β => ?_)
    show F (u (Xcont β)) = F (fun i => ofBrownianSpace B (Real.toNNReal (ts i)) β)
    rw [huXcont β]
  simp only [ProbabilityMeasure.coe_mk, Function.comp_def] at hport
  rw [heqL, heqR] at hport
  exact hport

end Parking

end
