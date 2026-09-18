/-
The variance bound and the Chebyshev step showing `signedM(φ) → 0` in `(law d ν)`-probability.
This module assembles `Parking.Support.SpatWMartingale`'s partial-sum measurability,
`Parking.Support.SpatWMartingaleCore`'s single- and two-instruction conditional means, and
`Parking.Generic.RoundMartingale`'s square-function identity into the target bound
`parking.tex:1758-1766` states, `E signedM(φ)² ≤ CR^{-d-2}∑_{...}E U_t(y) ≤ CR^{-d/2}`, and then
applies Chebyshev.

Exponent bookkeeping: `signedM ω R φ = R^{-d/2} ∑_{k<t} xiRound φR box' k ω` (`t = ⌊R²⌋₊`), so
`E[signedM²] = R^{-d} ∑_{k<t} E[(xiRound k)²]`. Each site's round-`k` term has conditional
variance `γ_y(φR)·(increment length)`, `γ_y(φR) ≤ (L_φ/R)²` (the rescaled test function's
lattice-step oscillation, `Parking.testFun_nbr_diff_le` below — this is the paper's own
"each term is bounded by `C_φ/R`"), telescoping the increment lengths over `k < t` to
`meanU(t)` (`Parking.meanU_shift_invariant`), and `|box'| = O(R^d)`
(`Parking.card_boxFinset`). So `E[signedM²] ≤ R^{-d}·O(R^d)·(L_φ/R)²·meanU(t)
= O(1)·R^{-2}·meanU(⌊R²⌋₊)`. `Parking.Frozen.growth`'s `d ≤ 3` branch gives
`meanU(n) ≤ C·n^{(4-d)/4}`, so at `n = ⌊R²⌋₊ ≍ R²` this is `O(R^{(4-d)/2})`, giving
`E[signedM²] ≤ C_φ·R^{(4-d)/2 - 2} = C_φ·R^{-d/2}`, exactly the paper's own target.
-/
import Parking.Support.SpatWMartingale
import Parking.Support.RiemannLattice
import Parking.Support.ContOpRegularity
import Parking.Support.MatchedUniform
import Parking.Frozen.Growth
import Parking.Generic.Telescope
import Parking.Generic.Chebyshev

open MeasureTheory LatticeProb Finset Filter Topology
open scoped ENNReal

noncomputable section
namespace Parking

variable {d : ℕ}

/-! ### A global Lipschitz-type bound for a test function, along a coordinate direction -/

/-- **The partial derivative of a test function is bounded.** -/
theorem exists_partialDeriv_bound {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) (i : Fin d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |partialDeriv φ i x| ≤ M := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_le_of_hasCompactSupport
    (contDiff_partialDeriv hφ.1 i).continuous (hasCompactSupport_partialDeriv hφ.2 i)
  exact ⟨M, hM0, hM⟩

/-- **A slice of a test function is globally Lipschitz, with constant a bound on the partial
derivative along that slice's direction.** -/
theorem testFun_slice_lipschitz {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) (i : Fin d)
    {M : ℝ} (hM : ∀ x, |partialDeriv φ i x| ≤ M) (x : Fin d → ℝ) (t0 t1 : ℝ) :
    |φ (Function.update x i t1) - φ (Function.update x i t0)| ≤ M * |t1 - t0| := by
  have hdiff : ∀ s : ℝ, DifferentiableAt ℝ (fun t => φ (Function.update x i t)) s := by
    intro s
    exact (((hφ.1.differentiable (by simp)) (Function.update x i s)).hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_update x i s)).differentiableAt
  have hbound : ∀ s ∈ (Set.univ : Set ℝ),
      ‖deriv (fun t => φ (Function.update x i t)) s‖ ≤ M := by
    intro s _
    rw [deriv_slice (hφ.1.differentiable (by simp)) x i s, Real.norm_eq_abs]
    exact hM _
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun t => φ (Function.update x i t)) (s := (Set.univ : Set ℝ))
    (fun s _ => hdiff s) hbound convex_univ (Set.mem_univ t0) (Set.mem_univ t1)
  simpa [Real.norm_eq_abs] using hmvt

/-- **A shifted slice of a test function is Lipschitz in the shift.** -/
theorem testFun_slice_step {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) (i : Fin d)
    {M : ℝ} (hM : ∀ x, |partialDeriv φ i x| ≤ M) (x0 : Fin d → ℝ) (h : ℝ) :
    |φ (Function.update x0 i (x0 i + h)) - φ x0| ≤ M * |h| := by
  have hbound := testFun_slice_lipschitz hφ i hM x0 (x0 i) (x0 i + h)
  rw [Function.update_eq_self] at hbound
  simpa using hbound

/-- **A test function's rescaled lattice difference across one lattice step is `O(1/R)`.**
`parking.tex:1758-1762`'s own "each term is bounded by `C_φ/R`". -/
theorem testFun_nbr_diff_le {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ R : ℝ, 0 < R → ∀ y z : Site d, z ∈ nbrFinset y →
      |φ (fun j => (z j : ℝ) / R) - φ (fun j => (y j : ℝ) / R)| ≤ L / R := by
  choose M hM0 hM using fun i : Fin d => exists_partialDeriv_bound hφ i
  refine ⟨∑ i : Fin d, M i, Finset.sum_nonneg fun i _ => hM0 i, fun R hR y z hz => ?_⟩
  obtain ⟨i, hi | hi⟩ := mem_nbrFinset_iff.mp hz
  · subst hi
    have hMi_le : M i ≤ ∑ j : Fin d, M j :=
      Finset.single_le_sum (fun j _ => hM0 j) (Finset.mem_univ i)
    have hupdate : (fun j => ((y + unit i) j : ℝ) / R)
        = Function.update (fun j => (y j : ℝ) / R) i ((fun j => (y j : ℝ) / R) i + 1 / R) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self, Pi.add_apply, unit, Pi.single_eq_same]
        push_cast; ring
      · simp only [Function.update_of_ne hj, Pi.add_apply, unit, Pi.single_eq_of_ne hj, add_zero]
    rw [hupdate]
    have hstep := testFun_slice_step hφ i (hM i) (fun j => (y j : ℝ) / R) (1 / R)
    have h1R : |(1 : ℝ) / R| = 1 / R := abs_of_pos (by positivity)
    rw [h1R] at hstep
    calc |φ (Function.update (fun j => (y j : ℝ) / R) i
          ((fun j => (y j : ℝ) / R) i + 1 / R)) - φ (fun j => (y j : ℝ) / R)|
        ≤ M i * (1 / R) := hstep
      _ ≤ (∑ j : Fin d, M j) * (1 / R) :=
          mul_le_mul_of_nonneg_right hMi_le (by positivity)
      _ = (∑ j : Fin d, M j) / R := by ring
  · subst hi
    have hMi_le : M i ≤ ∑ j : Fin d, M j :=
      Finset.single_le_sum (fun j _ => hM0 j) (Finset.mem_univ i)
    have hupdate : (fun j => ((y - unit i) j : ℝ) / R)
        = Function.update (fun j => (y j : ℝ) / R) i ((fun j => (y j : ℝ) / R) i + (-(1 / R))) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp only [Function.update_self, Pi.sub_apply, unit, Pi.single_eq_same]
        push_cast; ring
      · simp only [Function.update_of_ne hj, Pi.sub_apply, unit, Pi.single_eq_of_ne hj, sub_zero]
    rw [hupdate]
    have hstep := testFun_slice_step hφ i (hM i) (fun j => (y j : ℝ) / R) (-(1 / R))
    have h1R : |(-(1 / R) : ℝ)| = 1 / R := by
      rw [abs_neg]; exact abs_of_pos (by positivity)
    rw [h1R] at hstep
    calc |φ (Function.update (fun j => (y j : ℝ) / R) i
          ((fun j => (y j : ℝ) / R) i + (-(1 / R)))) - φ (fun j => (y j : ℝ) / R)|
        ≤ M i * (1 / R) := hstep
      _ ≤ (∑ j : Fin d, M j) * (1 / R) :=
          mul_le_mul_of_nonneg_right hMi_le (by positivity)
      _ = (∑ j : Fin d, M j) / R := by ring

/-! ### The walk operator's variance bound -/

/-- **`walkOp` of the square minus the square of `walkOp` is bounded by any second moment around
a fixed constant.** -/
theorem walkOp_variance_le (hd : 1 ≤ d) (f : Site d → ℝ) (y : Site d) {B : ℝ}
    (h : ∀ z ∈ nbrFinset y, (f z - f y) ^ 2 ≤ B) :
    walkOp (fun z => (f z) ^ 2) y - (walkOp f y) ^ 2 ≤ B := by
  have hexpand : (fun z => (f z - f y) ^ 2)
      = fun z => ((fun z => (f z) ^ 2) z - (fun _ => 2 * f y) z * f z) + (fun _ : Site d => (f y) ^ 2) z := by
    funext z; ring
  have h1 : walkOp (fun z => (f z - f y) ^ 2) y
      = (walkOp (fun z => (f z) ^ 2) y - walkOp (fun z => 2 * f y * f z) y) + (f y) ^ 2 := by
    rw [hexpand, walkOp_add, walkOp_sub, walkOp_const_mul, walkOp_const hd]
  have hcross : walkOp (fun z => 2 * f y * f z) y = 2 * f y * walkOp f y := by
    have := walkOp_const_mul (2 * f y) f y
    simpa using this
  rw [hcross] at h1
  have hle : walkOp (fun z => (f z - f y) ^ 2) y ≤ B := walkOp_le_of_nbr hd h
  nlinarith [sq_nonneg (walkOp f y - f y), h1, hle]

/-! ### The squared sum of a fixed range of unread instructions, centered -/

/-- **The squared sum of a fixed range of unread instructions at one site, for a CENTERED test
function, integrates to the range length times the variance.**  The off-diagonal terms vanish
(`ψ` is centered, `walkOp ψ y = 0`, via `double_core`); the diagonal survives via `single_core`
at `ψ²`. -/
theorem sum_sq_centered_core (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (k : ℕ) (y : Site d) (a b : ℕ) (ψ : Site d → ℝ) {M : ℝ} (hbound : ∀ x, |ψ x| ≤ M)
    (hcenter : walkOp ψ y = 0)
    {T : Set (Data d)} (hT : MeasurableSet[expFiltration d k] T)
    (hTsub : T ⊆ {ω | U ω k y = a}) :
    ∫ ω, T.indicator (fun ω => (∑ j ∈ Finset.Ico a b, ψ (ω.2.1 (y, j))) ^ 2) ω ∂(law d ν)
      = ((b - a : ℕ) : ℝ) * walkOp (fun x => (ψ x) ^ 2) y * (law d ν).real T := by
  classical
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  have hTamb : MeasurableSet T := expFiltration_le d k T hT
  have hptwise : ∀ j ∈ Finset.Ico a b, ∀ j' ∈ Finset.Ico a b,
      ∫ ω, T.indicator (fun ω => ψ (ω.2.1 (y, j)) * ψ (ω.2.1 (y, j'))) ω ∂(law d ν)
        = if j = j' then walkOp (fun x => (ψ x) ^ 2) y * (law d ν).real T else 0 := by
    intro j hj j' hj'
    have hTsubj : T ⊆ {ω | U ω k y ≤ j} := fun ω hω => by
      show U ω k y ≤ j
      rw [hTsub hω]; exact (Finset.mem_Ico.mp hj).1
    have hTsubj' : T ⊆ {ω | U ω k y ≤ j'} := fun ω hω => by
      show U ω k y ≤ j'
      rw [hTsub hω]; exact (Finset.mem_Ico.mp hj').1
    by_cases hjj' : j = j'
    · subst hjj'
      rw [if_pos rfl]
      have hcore := single_core hd ν k y j (fun x => (ψ x) ^ 2) hT hTsubj
      have heq : (fun ω : Data d => ψ (ω.2.1 (y, j)) * ψ (ω.2.1 (y, j)))
          = fun ω : Data d => (ψ (ω.2.1 (y, j))) ^ 2 := by funext ω; ring
      rw [heq]
      exact hcore
    · rw [if_neg hjj']
      have hne : (y, j) ≠ (y, j') := by simp [hjj']
      have hTsub2 : T ⊆ {ω | U ω k y ≤ j} ∩ {ω | U ω k y ≤ j'} :=
        fun ω hω => ⟨hTsubj hω, hTsubj' hω⟩
      have hdc := double_core hd ν k y y j j' hne ψ ψ hT hTsub2
      rw [hdc, hcenter]; ring
  have hexpand : (fun ω : Data d =>
      T.indicator (fun ω => (∑ j ∈ Finset.Ico a b, ψ (ω.2.1 (y, j))) ^ 2) ω)
      = fun ω => ∑ j ∈ Finset.Ico a b, ∑ j' ∈ Finset.Ico a b,
          T.indicator (fun ω => ψ (ω.2.1 (y, j)) * ψ (ω.2.1 (y, j'))) ω := by
    funext ω
    by_cases hω : ω ∈ T
    · rw [Set.indicator_of_mem hω, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
      exact (Set.indicator_of_mem hω (fun ω => ψ (ω.2.1 (y, j)) * ψ (ω.2.1 (y, j')))).symm
    · rw [Set.indicator_of_notMem hω]
      symm
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun j' _ => ?_
      exact Set.indicator_of_notMem hω _
  rw [hexpand]
  have hmeasjj' : ∀ j j' : ℕ,
      Measurable (fun ω : Data d => ψ (ω.2.1 (y, j)) * ψ (ω.2.1 (y, j'))) := fun j j' =>
    ((measurable_from_countable' ψ).comp
        ((measurable_pi_apply (y, j)).comp (measurable_fst.comp measurable_snd))).mul
      ((measurable_from_countable' ψ).comp
        ((measurable_pi_apply (y, j')).comp (measurable_fst.comp measurable_snd)))
  have hintg : ∀ j ∈ Finset.Ico a b, ∀ j' ∈ Finset.Ico a b,
      Integrable (fun ω =>
          T.indicator (fun ω => ψ (ω.2.1 (y, j)) * ψ (ω.2.1 (y, j'))) ω) (law d ν) := by
    intro j _ j' _
    refine Integrable.indicator ?_ hTamb
    refine Integrable.mono' (integrable_const (M * M)) (hmeasjj' j j').aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hbound (ω.2.1 (y, j))) (hbound (ω.2.1 (y, j'))) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hbound (ω.2.1 (y, j))))
  have hIntInner : ∀ j ∈ Finset.Ico a b,
      Integrable (fun ω => ∑ j' ∈ Finset.Ico a b,
          T.indicator (fun ω => ψ (ω.2.1 (y, j)) * ψ (ω.2.1 (y, j'))) ω) (law d ν) :=
    fun j hj => integrable_finsetSum _ (fun j' hj' => hintg j hj j' hj')
  rw [integral_finsetSum _ hIntInner]
  have hInnerEq : ∀ j ∈ Finset.Ico a b,
      ∫ ω, (∑ j' ∈ Finset.Ico a b,
          T.indicator (fun ω => ψ (ω.2.1 (y, j)) * ψ (ω.2.1 (y, j'))) ω) ∂(law d ν)
        = walkOp (fun x => (ψ x) ^ 2) y * (law d ν).real T := by
    intro j hj
    rw [integral_finsetSum _ (fun j' hj' => hintg j hj j' hj'), Finset.sum_congr rfl (hptwise j hj)]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]
    · intro x _ hx
      rw [if_neg (fun h : j = x => hx h.symm)]
    · intro h; exact absurd hj h
  rw [Finset.sum_congr rfl hInnerEq, Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
  ring

/-! ### The product over two DIFFERENT sites, at fixed ranges -/

/-- **The product of two fixed ranges of unread instructions at two DIFFERENT sites integrates
to the product of the per-site means, times the two range lengths.**  Every pair `(y, j), (y', j')`
automatically differs (the sites differ), so `double_core` applies uniformly, with no diagonal
term to separate out. -/
theorem sum_prod_diffsite_core (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (k : ℕ) (y y' : Site d) (hyy' : y ≠ y') (a b a' b' : ℕ) (ψ ψ' : Site d → ℝ) {M M' : ℝ}
    (hbound : ∀ x, |ψ x| ≤ M) (hbound' : ∀ x, |ψ' x| ≤ M')
    {T : Set (Data d)} (hT : MeasurableSet[expFiltration d k] T)
    (hTsub : T ⊆ {ω | U ω k y = a} ∩ {ω | U ω k y' = a'}) :
    ∫ ω, T.indicator (fun ω => (∑ j ∈ Finset.Ico a b, ψ (ω.2.1 (y, j)))
        * (∑ j' ∈ Finset.Ico a' b', ψ' (ω.2.1 (y', j')))) ω ∂(law d ν)
      = ((b - a : ℕ) : ℝ) * ((b' - a' : ℕ) : ℝ) * walkOp ψ y * walkOp ψ' y'
          * (law d ν).real T := by
  classical
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  have hTamb : MeasurableSet T := expFiltration_le d k T hT
  have hptwise : ∀ j ∈ Finset.Ico a b, ∀ j' ∈ Finset.Ico a' b',
      ∫ ω, T.indicator (fun ω => ψ (ω.2.1 (y, j)) * ψ' (ω.2.1 (y', j'))) ω ∂(law d ν)
        = walkOp ψ y * walkOp ψ' y' * (law d ν).real T := by
    intro j hj j' hj'
    have hTsubj : T ⊆ {ω | U ω k y ≤ j} := fun ω hω => by
      show U ω k y ≤ j
      rw [(hTsub hω).1]; exact (Finset.mem_Ico.mp hj).1
    have hTsubj' : T ⊆ {ω | U ω k y' ≤ j'} := fun ω hω => by
      show U ω k y' ≤ j'
      rw [(hTsub hω).2]; exact (Finset.mem_Ico.mp hj').1
    have hne : (y, j) ≠ (y', j') := fun heq => hyy' (congrArg Prod.fst heq)
    have hTsub2 : T ⊆ {ω | U ω k y ≤ j} ∩ {ω | U ω k y' ≤ j'} :=
      fun ω hω => ⟨hTsubj hω, hTsubj' hω⟩
    exact double_core hd ν k y y' j j' hne ψ ψ' hT hTsub2
  have hexpand : (fun ω : Data d =>
      T.indicator (fun ω => (∑ j ∈ Finset.Ico a b, ψ (ω.2.1 (y, j)))
          * (∑ j' ∈ Finset.Ico a' b', ψ' (ω.2.1 (y', j')))) ω)
      = fun ω => ∑ j ∈ Finset.Ico a b, ∑ j' ∈ Finset.Ico a' b',
          T.indicator (fun ω => ψ (ω.2.1 (y, j)) * ψ' (ω.2.1 (y', j'))) ω := by
    funext ω
    by_cases hω : ω ∈ T
    · rw [Set.indicator_of_mem hω, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
      exact (Set.indicator_of_mem hω (fun ω => ψ (ω.2.1 (y, j)) * ψ' (ω.2.1 (y', j')))).symm
    · rw [Set.indicator_of_notMem hω]
      symm
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun j' _ => ?_
      exact Set.indicator_of_notMem hω _
  rw [hexpand]
  have hmeasjj' : ∀ j j' : ℕ,
      Measurable (fun ω : Data d => ψ (ω.2.1 (y, j)) * ψ' (ω.2.1 (y', j'))) := fun j j' =>
    ((measurable_from_countable' ψ).comp
        ((measurable_pi_apply (y, j)).comp (measurable_fst.comp measurable_snd))).mul
      ((measurable_from_countable' ψ').comp
        ((measurable_pi_apply (y', j')).comp (measurable_fst.comp measurable_snd)))
  have hintg : ∀ j ∈ Finset.Ico a b, ∀ j' ∈ Finset.Ico a' b',
      Integrable (fun ω =>
          T.indicator (fun ω => ψ (ω.2.1 (y, j)) * ψ' (ω.2.1 (y', j'))) ω) (law d ν) := by
    intro j _ j' _
    refine Integrable.indicator ?_ hTamb
    refine Integrable.mono' (integrable_const (M * M')) (hmeasjj' j j').aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hbound (ω.2.1 (y, j))) (hbound' (ω.2.1 (y', j'))) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hbound (ω.2.1 (y, j))))
  have hIntInner : ∀ j ∈ Finset.Ico a b,
      Integrable (fun ω => ∑ j' ∈ Finset.Ico a' b',
          T.indicator (fun ω => ψ (ω.2.1 (y, j)) * ψ' (ω.2.1 (y', j'))) ω) (law d ν) :=
    fun j hj => integrable_finsetSum _ (fun j' hj' => hintg j hj j' hj')
  rw [integral_finsetSum _ hIntInner]
  have hInnerEq : ∀ j ∈ Finset.Ico a b,
      ∫ ω, (∑ j' ∈ Finset.Ico a' b',
          T.indicator (fun ω => ψ (ω.2.1 (y, j)) * ψ' (ω.2.1 (y', j'))) ω) ∂(law d ν)
        = ((b' - a' : ℕ) : ℝ) * (walkOp ψ y * walkOp ψ' y' * (law d ν).real T) := by
    intro j hj
    rw [integral_finsetSum _ (fun j' hj' => hintg j hj j' hj'), Finset.sum_congr rfl (hptwise j hj)]
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
  rw [Finset.sum_congr rfl hInnerEq, Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
  ring

/-! ### The second moment of the odometer -/

/-- **The odometer has a finite second moment.** `CriticalLaw`'s exponential moment gives every
polynomial moment, via `Parking.integrable_U_rpow`; specialized to `r = 2`. -/
theorem integrable_U_sq (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] (hν : CriticalLaw ν)
    (n : ℕ) (x : Site d) :
    Integrable (fun ω : Data d => ((U ω n x : ℕ) : ℝ) ^ 2) (law d ν) := by
  obtain ⟨θ, hθ, hexpabs⟩ := hν.expMoment
  have hexp := integrable_expMax_of_expAbs hθ hexpabs
  have h := integrable_U_rpow hd ν hθ hexp (r := (2 : ℝ)) (by norm_num) n x
  have heq : (fun ω : Data d => ((U ω n x : ℕ) : ℝ) ^ (2 : ℝ))
      = fun ω : Data d => ((U ω n x : ℕ) : ℝ) ^ (2 : ℕ) := by
    funext ω
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  rwa [heq] at h

/-! ### The round increment's conditional variance, at a single site -/

/-- **The `expOdometer`-gated round-`k` increment at a single site has conditional variance
`γ_y(φR)·(expOdometer_ky - U_ky)`**, `γ_y(φR) := walkOp(φR²)y - (walkOp φR y)²`.  Same selector
and structure as `Parking.condExp_siteExp_eq_zero`; the per-piece fact is now
`Parking.sum_sq_centered_core` instead of the centred `single_core`. -/
theorem condExp_siteVar_eq (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (k : ℕ) (y : Site d) {φR : Site d → ℝ} {M : ℝ} (hbound : ∀ x, |φR x| ≤ M) :
    (law d ν)[fun ω : Data d =>
        (∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y)) ^ 2
      | expFiltration d k]
      =ᵐ[law d ν] fun ω => (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2)
          * ((expOdometer d k ω y : ℝ) - (U ω k y : ℝ)) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  classical
  set γ : ℝ := walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2 with hγdef
  set sel : Data d → ℕ × ℕ := fun ω => (U ω k y, expOdometer d k ω y) with hseldef
  have hsel : Measurable[expFiltration d k] sel :=
    (measurable_U_expFiltration k y).prodMk (measurable_expOdometer k y)
  have hMbound : ∀ x, |φR x - walkOp φR y| ≤ M + |walkOp φR y| := fun x => by
    calc |φR x - walkOp φR y| ≤ |φR x| + |walkOp φR y| := abs_sub _ _
      _ ≤ M + |walkOp φR y| := by linarith [hbound x]
  have hmeasSum : Measurable (fun ω : Data d =>
      ∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y)) := by
    have hmeasrange : Measurable fun ω : Data d => (U ω k y, expOdometer d k ω y) :=
      ((measurable_U_expFiltration k y).mono (expFiltration_le d k) le_rfl).prodMk
        ((measurable_expOdometer k y).mono (expFiltration_le d k) le_rfl)
    have hmeasj : ∀ j : ℕ, Measurable (fun ω : Data d => φR (ω.2.1 (y, j)) - walkOp φR y) :=
      fun j => ((measurable_from_countable' φR).comp
        ((measurable_pi_apply (y, j)).comp (measurable_fst.comp measurable_snd))).sub
        measurable_const
    exact measurable_of_countable_partition (fun ω => (U ω k y, expOdometer d k ω y))
      hmeasrange _ (fun c ω => ∑ j ∈ Finset.Ico c.1 c.2, (φR (ω.2.1 (y, j)) - walkOp φR y))
      (fun c => Finset.measurable_sum _ fun j _ => hmeasj j) (fun _ => rfl)
  have hmeasΦ : Measurable (fun ω : Data d =>
      (∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y),
        (φR (ω.2.1 (y, j)) - walkOp φR y)) ^ 2) := hmeasSum.pow_const 2
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (φR (0 : Site d))) (hbound (0 : Site d))
  have h0 : 0 ≤ M + |walkOp φR y| := by linarith [abs_nonneg (walkOp φR y)]
  have hIsum : Integrable (fun ω : Data d =>
      ∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y))
      (law d ν) := by
    have hInt2 : Integrable (fun ω : Data d => (expOdometer d k ω y : ℝ)) (law d ν) := by
      have hcong : (fun ω : Data d => (expOdometer d k ω y : ℝ))
          =ᵐ[law d ν] fun ω => (U ω (k + 1) y : ℝ) := by
        filter_upwards [U_succ_ae_eq_expOdometer hd ν k y] with ω hω
        exact_mod_cast hω.symm
      exact (integrable_U_law hd ν hν.integrable_abs (k + 1) y).congr hcong.symm
    refine Integrable.mono' ((hInt2.add (integrable_U_law hd ν hν.integrable_abs k y)).const_mul
      (M + |walkOp φR y|)) hmeasSum.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    show |∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y)|
      ≤ (M + |walkOp φR y|) * ((expOdometer d k ω y : ℝ) + (U ω k y : ℝ))
    calc |∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y)|
        ≤ ∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (M + |walkOp φR y|) :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => hMbound (ω.2.1 (y, j)))
      _ = ((Finset.Ico (U ω k y) (expOdometer d k ω y)).card : ℝ) * (M + |walkOp φR y|) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (expOdometer d k ω y : ℝ) * (M + |walkOp φR y|) := by
          have hcard : (Finset.Ico (U ω k y) (expOdometer d k ω y)).card ≤ expOdometer d k ω y := by
            rw [Nat.card_Ico]; omega
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) h0
      _ ≤ (M + |walkOp φR y|) * ((expOdometer d k ω y : ℝ) + (U ω k y : ℝ)) := by
          have hUnn : (0 : ℝ) ≤ (U ω k y : ℝ) := Nat.cast_nonneg _
          nlinarith
  have hIΦ : Integrable (fun ω : Data d =>
      (∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y),
        (φR (ω.2.1 (y, j)) - walkOp φR y)) ^ 2) (law d ν) := by
    have hEsq : Integrable (fun ω : Data d =>
        ((expOdometer d k ω y : ℝ) + (U ω k y : ℝ)) ^ 2) (law d ν) := by
      have hUsq : Integrable (fun ω : Data d => ((U ω k y : ℕ) : ℝ) ^ 2) (law d ν) :=
        integrable_U_sq hd ν hν k y
      have hEsq0 : Integrable (fun ω : Data d => (expOdometer d k ω y : ℝ) ^ 2) (law d ν) := by
        have hcong : (fun ω : Data d => (expOdometer d k ω y : ℝ) ^ 2)
            =ᵐ[law d ν] fun ω => ((U ω (k + 1) y : ℕ) : ℝ) ^ 2 := by
          filter_upwards [U_succ_ae_eq_expOdometer hd ν k y] with ω hω
          rw [hω]
        exact (integrable_U_sq hd ν hν (k + 1) y).congr hcong.symm
      have hDom : Integrable (fun ω : Data d =>
          2 * ((expOdometer d k ω y : ℝ) ^ 2 + (U ω k y : ℝ) ^ 2)) (law d ν) :=
        (hEsq0.add hUsq).const_mul 2
      refine Integrable.mono' hDom ?_ (Filter.Eventually.of_forall fun ω => ?_)
      · exact (((measurable_from_countable' (fun n : ℕ => (n : ℝ))).comp
            ((measurable_expOdometer k y).mono (expFiltration_le d k) le_rfl)).add
          ((measurable_from_countable' (fun n : ℕ => (n : ℝ))).comp
            (measurable_U k y))).pow_const 2 |>.aestronglyMeasurable
      · have hL : ‖(((expOdometer d k ω y : ℝ) + (U ω k y : ℝ)) ^ 2 : ℝ)‖
            = ((expOdometer d k ω y : ℝ) + (U ω k y : ℝ)) ^ 2 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        rw [hL]
        nlinarith [sq_nonneg ((expOdometer d k ω y : ℝ) - (U ω k y : ℝ))]
    refine Integrable.mono' (hEsq.const_mul ((M + |walkOp φR y|) ^ 2)) hmeasΦ.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    have hL : ‖((∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y),
          (φR (ω.2.1 (y, j)) - walkOp φR y)) ^ 2 : ℝ)‖
        = (∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y),
            (φR (ω.2.1 (y, j)) - walkOp φR y)) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [hL]
    have hb : |∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y),
        (φR (ω.2.1 (y, j)) - walkOp φR y)|
        ≤ (M + |walkOp φR y|) * ((expOdometer d k ω y : ℝ) + (U ω k y : ℝ)) := by
      calc |∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y)|
          ≤ ∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (M + |walkOp φR y|) :=
            (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun j _ => hMbound (ω.2.1 (y, j)))
        _ = ((Finset.Ico (U ω k y) (expOdometer d k ω y)).card : ℝ) * (M + |walkOp φR y|) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (expOdometer d k ω y : ℝ) * (M + |walkOp φR y|) := by
            have hcard : (Finset.Ico (U ω k y) (expOdometer d k ω y)).card
                ≤ expOdometer d k ω y := by rw [Nat.card_Ico]; omega
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) h0
        _ ≤ (M + |walkOp φR y|) * ((expOdometer d k ω y : ℝ) + (U ω k y : ℝ)) := by
            have hUnn : (0 : ℝ) ≤ (U ω k y : ℝ) := Nat.cast_nonneg _
            nlinarith
    have hab := abs_le.mp hb
    calc (∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y),
          (φR (ω.2.1 (y, j)) - walkOp φR y)) ^ 2
        ≤ ((M + |walkOp φR y|) * ((expOdometer d k ω y : ℝ) + (U ω k y : ℝ))) ^ 2 :=
          sq_le_sq' hab.1 hab.2
      _ = (M + |walkOp φR y|) ^ 2 * ((expOdometer d k ω y : ℝ) + (U ω k y : ℝ)) ^ 2 := by ring
  have hnullset : (law d ν) {ω | expOdometer d k ω y < U ω k y} = 0 := by
    have hae : ∀ᵐ ω ∂(law d ν), U ω k y ≤ expOdometer d k ω y := by
      filter_upwards [U_succ_ae_eq_expOdometer hd ν k y] with ω hω
      rw [← hω]; exact U_mono_time ω y (Nat.le_succ k)
    have := MeasureTheory.ae_iff.mp hae
    simpa [not_le] using this
  refine Parking.Generic.CondExpPartition.condExp_of_countable_partition
    (μ := law d ν) (expFiltration_le d k) sel hsel _
    (fun ω => γ * ((expOdometer d k ω y : ℝ) - (U ω k y : ℝ))) hIΦ ?_ ?_ ?_
  · exact ((measurable_from_countable' (fun n : ℕ => (n : ℝ))).comp (measurable_expOdometer k y)
      |>.sub ((measurable_from_countable' (fun n : ℕ => (n : ℝ))).comp
        (measurable_U_expFiltration k y))
      |>.const_mul γ)
  · have hInt2 : Integrable (fun ω : Data d => (expOdometer d k ω y : ℝ)) (law d ν) := by
      have hcong : (fun ω : Data d => (expOdometer d k ω y : ℝ))
          =ᵐ[law d ν] fun ω => (U ω (k + 1) y : ℝ) := by
        filter_upwards [U_succ_ae_eq_expOdometer hd ν k y] with ω hω
        exact_mod_cast hω.symm
      exact (integrable_U_law hd ν hν.integrable_abs (k + 1) y).congr hcong.symm
    exact ((hInt2.sub (integrable_U_law hd ν hν.integrable_abs k y)).const_mul γ)
  · rintro ⟨a, b⟩ S hS hSsub
    have hpiece : ∀ ω ∈ S, U ω k y = a ∧ expOdometer d k ω y = b := by
      intro ω hω
      have heq : (U ω k y, expOdometer d k ω y) = (a, b) := hSsub hω
      injection heq with h1 h2
      exact ⟨h1, h2⟩
    have hSsub' : S ⊆ {ω | U ω k y = a} := fun ω hω => (hpiece ω hω).1
    have hSamb : MeasurableSet S := expFiltration_le d k S hS
    by_cases hab : a ≤ b
    · set ψ : Site d → ℝ := fun x => φR x - walkOp φR y with hψdef
      have hψbound : ∀ x, |ψ x| ≤ M + |walkOp φR y| := fun x => hMbound x
      have hψwalk : walkOp ψ y = 0 := by rw [hψdef, walkOp_sub_const hd, sub_self]
      have hcore := sum_sq_centered_core hd ν k y a b ψ hψbound hψwalk hS hSsub'
      have hψsqwalk : walkOp (fun x => (ψ x) ^ 2) y = γ := by
        have hexpand : (fun x => (ψ x) ^ 2)
            = fun x => (φR x) ^ 2 - 2 * (walkOp φR y) * φR x + (walkOp φR y) ^ 2 := by
          funext x; rw [hψdef]; ring
        rw [hexpand]
        have h1 : walkOp (fun x => (φR x) ^ 2 - 2 * (walkOp φR y) * φR x + (walkOp φR y) ^ 2) y
            = (walkOp (fun x => (φR x) ^ 2) y - walkOp (fun x => 2 * (walkOp φR y) * φR x) y)
              + (walkOp φR y) ^ 2 := by
          rw [show (fun x => (φR x) ^ 2 - 2 * (walkOp φR y) * φR x + (walkOp φR y) ^ 2)
              = fun x => ((φR x) ^ 2 - 2 * (walkOp φR y) * φR x) + (walkOp φR y) ^ 2 from
                by funext x; ring]
          rw [walkOp_add, walkOp_sub, walkOp_const_mul, walkOp_const hd]
        rw [h1, walkOp_const_mul]
        rw [hγdef]; ring
      have heqS : (fun ω : Data d => S.indicator
            (fun ω => (∑ j ∈ Finset.Ico a b, ψ (ω.2.1 (y, j))) ^ 2) ω)
          = fun ω => S.indicator (fun ω =>
              (∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y),
                (φR (ω.2.1 (y, j)) - walkOp φR y)) ^ 2) ω := by
        funext ω
        by_cases h : ω ∈ S
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, (hpiece ω h).1, (hpiece ω h).2]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      rw [← heqS, hcore, hψsqwalk]
      have hRHS : (fun ω : Data d => S.indicator
            (fun ω => γ * ((expOdometer d k ω y : ℝ) - (U ω k y : ℝ))) ω)
          = fun ω => S.indicator (fun _ => γ * ((b : ℝ) - (a : ℝ))) ω := by
        funext ω
        by_cases h : ω ∈ S
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, (hpiece ω h).1, (hpiece ω h).2]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      have hRHSint : ∫ ω, S.indicator (fun _ : Data d => γ * ((b : ℝ) - (a : ℝ))) ω ∂(law d ν)
          = (law d ν).real S * (γ * ((b : ℝ) - (a : ℝ))) := by
        have hterm := MeasureTheory.integral_indicator_const (μ := law d ν)
          (γ * ((b : ℝ) - (a : ℝ))) hSamb
        rw [smul_eq_mul] at hterm
        exact hterm
      rw [hRHS, hRHSint]
      have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - (a : ℝ) := by
        rw [Nat.cast_sub hab]
      rw [hcast]
      ring
    · have hab' : b < a := not_le.mp hab
      have hSsub2 : S ⊆ {ω | expOdometer d k ω y < U ω k y} := fun ω hω => by
        show expOdometer d k ω y < U ω k y
        rw [(hpiece ω hω).1, (hpiece ω hω).2]; exact hab'
      have hSnull : (law d ν) S = 0 := measure_mono_null hSsub2 hnullset
      have hSae : ∀ᵐ ω ∂(law d ν), ω ∉ S := by
        rw [MeasureTheory.ae_iff]; simpa using hSnull
      have hz1 : (fun ω : Data d => S.indicator
          (fun ω => (∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y),
            (φR (ω.2.1 (y, j)) - walkOp φR y)) ^ 2) ω) =ᵐ[law d ν] fun _ => (0 : ℝ) := by
        filter_upwards [hSae] with ω hω
        exact Set.indicator_of_notMem hω _
      have hz2 : (fun ω : Data d => S.indicator
          (fun ω => γ * ((expOdometer d k ω y : ℝ) - (U ω k y : ℝ))) ω)
          =ᵐ[law d ν] fun _ => (0 : ℝ) := by
        filter_upwards [hSae] with ω hω
        exact Set.indicator_of_notMem hω _
      rw [integral_congr_ae hz1, integral_congr_ae hz2]

/-! ### The round increment's conditional cross term, at two DIFFERENT sites -/

/-- **The `expOdometer`-gated round-`k` increments at two DIFFERENT sites have conditional cross
term zero.**  Same selector technique as `condExp_siteVar_eq`, now a FOUR-index selector
`(U_ky,expOdometer_ky,U_ky',expOdometer_ky')`; the per-piece fact is
`Parking.sum_prod_diffsite_core` applied to the CENTRED test functions, which is `0` outright
(no case split on the relative order of the range endpoints is needed, unlike the single-site
variance: the centring alone kills the whole product). -/
theorem condExp_crossSite_eq_zero (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (k : ℕ) (y y' : Site d) (hyy' : y ≠ y') {φR : Site d → ℝ} {M : ℝ}
    (hbound : ∀ x, |φR x| ≤ M) :
    (law d ν)[fun ω : Data d =>
        (∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y))
        * (∑ j' ∈ Finset.Ico (U ω k y') (expOdometer d k ω y'),
            (φR (ω.2.1 (y', j')) - walkOp φR y'))
      | expFiltration d k] =ᵐ[law d ν] fun _ => (0 : ℝ) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  classical
  set sel : Data d → (ℕ × ℕ) × (ℕ × ℕ) :=
    fun ω => ((U ω k y, expOdometer d k ω y), (U ω k y', expOdometer d k ω y')) with hseldef
  have hsel : Measurable[expFiltration d k] sel :=
    ((measurable_U_expFiltration k y).prodMk (measurable_expOdometer k y)).prodMk
      ((measurable_U_expFiltration k y').prodMk (measurable_expOdometer k y'))
  have hMbound : ∀ z : Site d, ∀ x, |φR x - walkOp φR z| ≤ M + |walkOp φR z| := fun z x => by
    calc |φR x - walkOp φR z| ≤ |φR x| + |walkOp φR z| := abs_sub _ _
      _ ≤ M + |walkOp φR z| := by linarith [hbound x]
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (φR (0 : Site d))) (hbound (0 : Site d))
  have h0 : ∀ z : Site d, 0 ≤ M + |walkOp φR z| := fun z => by
    linarith [abs_nonneg (walkOp φR z)]
  have hmeasSum : ∀ z : Site d, Measurable (fun ω : Data d =>
      ∑ j ∈ Finset.Ico (U ω k z) (expOdometer d k ω z), (φR (ω.2.1 (z, j)) - walkOp φR z)) := by
    intro z
    have hmeasrange : Measurable fun ω : Data d => (U ω k z, expOdometer d k ω z) :=
      ((measurable_U_expFiltration k z).mono (expFiltration_le d k) le_rfl).prodMk
        ((measurable_expOdometer k z).mono (expFiltration_le d k) le_rfl)
    have hmeasj : ∀ j : ℕ, Measurable (fun ω : Data d => φR (ω.2.1 (z, j)) - walkOp φR z) :=
      fun j => ((measurable_from_countable' φR).comp
        ((measurable_pi_apply (z, j)).comp (measurable_fst.comp measurable_snd))).sub
        measurable_const
    exact measurable_of_countable_partition (fun ω => (U ω k z, expOdometer d k ω z))
      hmeasrange _ (fun c ω => ∑ j ∈ Finset.Ico c.1 c.2, (φR (ω.2.1 (z, j)) - walkOp φR z))
      (fun c => Finset.measurable_sum _ fun j _ => hmeasj j) (fun _ => rfl)
  have hbnd : ∀ z : Site d, ∀ ω : Data d,
      |∑ j ∈ Finset.Ico (U ω k z) (expOdometer d k ω z), (φR (ω.2.1 (z, j)) - walkOp φR z)|
        ≤ (M + |walkOp φR z|) * ((expOdometer d k ω z : ℝ) + (U ω k z : ℝ)) := by
    intro z ω
    calc |∑ j ∈ Finset.Ico (U ω k z) (expOdometer d k ω z), (φR (ω.2.1 (z, j)) - walkOp φR z)|
        ≤ ∑ j ∈ Finset.Ico (U ω k z) (expOdometer d k ω z), (M + |walkOp φR z|) :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => hMbound z (ω.2.1 (z, j)))
      _ = ((Finset.Ico (U ω k z) (expOdometer d k ω z)).card : ℝ) * (M + |walkOp φR z|) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (expOdometer d k ω z : ℝ) * (M + |walkOp φR z|) := by
          have hcard : (Finset.Ico (U ω k z) (expOdometer d k ω z)).card
              ≤ expOdometer d k ω z := by rw [Nat.card_Ico]; omega
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (h0 z)
      _ ≤ (M + |walkOp φR z|) * ((expOdometer d k ω z : ℝ) + (U ω k z : ℝ)) := by
          have hUnn : (0 : ℝ) ≤ (U ω k z : ℝ) := Nat.cast_nonneg _
          nlinarith [mul_nonneg (h0 z) hUnn]
  have hIsum : ∀ z : Site d, Integrable (fun ω : Data d =>
      ∑ j ∈ Finset.Ico (U ω k z) (expOdometer d k ω z), (φR (ω.2.1 (z, j)) - walkOp φR z))
      (law d ν) := by
    intro z
    have hInt2 : Integrable (fun ω : Data d => (expOdometer d k ω z : ℝ)) (law d ν) := by
      have hcong : (fun ω : Data d => (expOdometer d k ω z : ℝ))
          =ᵐ[law d ν] fun ω => (U ω (k + 1) z : ℝ) := by
        filter_upwards [U_succ_ae_eq_expOdometer hd ν k z] with ω hω
        exact_mod_cast hω.symm
      exact (integrable_U_law hd ν hν.integrable_abs (k + 1) z).congr hcong.symm
    refine Integrable.mono' ((hInt2.add (integrable_U_law hd ν hν.integrable_abs k z)).const_mul
      (M + |walkOp φR z|)) (hmeasSum z).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    show |∑ j ∈ Finset.Ico (U ω k z) (expOdometer d k ω z), (φR (ω.2.1 (z, j)) - walkOp φR z)|
      ≤ (M + |walkOp φR z|) * ((expOdometer d k ω z : ℝ) + (U ω k z : ℝ))
    exact hbnd z ω
  have hEsq : ∀ z : Site d, Integrable (fun ω : Data d =>
      ((expOdometer d k ω z : ℝ) + (U ω k z : ℝ)) ^ 2) (law d ν) := by
    intro z
    have hUsq : Integrable (fun ω : Data d => ((U ω k z : ℕ) : ℝ) ^ 2) (law d ν) :=
      integrable_U_sq hd ν hν k z
    have hEsq0 : Integrable (fun ω : Data d => (expOdometer d k ω z : ℝ) ^ 2) (law d ν) := by
      have hcong : (fun ω : Data d => (expOdometer d k ω z : ℝ) ^ 2)
          =ᵐ[law d ν] fun ω => ((U ω (k + 1) z : ℕ) : ℝ) ^ 2 := by
        filter_upwards [U_succ_ae_eq_expOdometer hd ν k z] with ω hω
        rw [hω]
      exact (integrable_U_sq hd ν hν (k + 1) z).congr hcong.symm
    have hDom : Integrable (fun ω : Data d =>
        2 * ((expOdometer d k ω z : ℝ) ^ 2 + (U ω k z : ℝ) ^ 2)) (law d ν) :=
      (hEsq0.add hUsq).const_mul 2
    refine Integrable.mono' hDom ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact (((measurable_from_countable' (fun n : ℕ => (n : ℝ))).comp
          ((measurable_expOdometer k z).mono (expFiltration_le d k) le_rfl)).add
        ((measurable_from_countable' (fun n : ℕ => (n : ℝ))).comp
          (measurable_U k z))).pow_const 2 |>.aestronglyMeasurable
    · have hL : ‖(((expOdometer d k ω z : ℝ) + (U ω k z : ℝ)) ^ 2 : ℝ)‖
          = ((expOdometer d k ω z : ℝ) + (U ω k z : ℝ)) ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [hL]
      nlinarith [sq_nonneg ((expOdometer d k ω z : ℝ) - (U ω k z : ℝ))]
  have hIsq : ∀ z : Site d, Integrable (fun ω : Data d =>
      (∑ j ∈ Finset.Ico (U ω k z) (expOdometer d k ω z), (φR (ω.2.1 (z, j)) - walkOp φR z)) ^ 2)
      (law d ν) := by
    intro z
    refine Integrable.mono' ((hEsq z).const_mul ((M + |walkOp φR z|) ^ 2))
      ((hmeasSum z).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    have hL : ‖((∑ j ∈ Finset.Ico (U ω k z) (expOdometer d k ω z),
          (φR (ω.2.1 (z, j)) - walkOp φR z)) ^ 2 : ℝ)‖
        = (∑ j ∈ Finset.Ico (U ω k z) (expOdometer d k ω z),
            (φR (ω.2.1 (z, j)) - walkOp φR z)) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [hL]
    have hab := abs_le.mp (hbnd z ω)
    calc (∑ j ∈ Finset.Ico (U ω k z) (expOdometer d k ω z),
          (φR (ω.2.1 (z, j)) - walkOp φR z)) ^ 2
        ≤ ((M + |walkOp φR z|) * ((expOdometer d k ω z : ℝ) + (U ω k z : ℝ))) ^ 2 :=
          sq_le_sq' hab.1 hab.2
      _ = (M + |walkOp φR z|) ^ 2 * ((expOdometer d k ω z : ℝ) + (U ω k z : ℝ)) ^ 2 := by ring
  have hIprod : Integrable (fun ω : Data d =>
      (∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y))
      * (∑ j' ∈ Finset.Ico (U ω k y') (expOdometer d k ω y'),
          (φR (ω.2.1 (y', j')) - walkOp φR y'))) (law d ν) := by
    have hDom : Integrable (fun ω : Data d =>
        ((∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y)) ^ 2
          + (∑ j' ∈ Finset.Ico (U ω k y') (expOdometer d k ω y'),
              (φR (ω.2.1 (y', j')) - walkOp φR y')) ^ 2) / 2) (law d ν) :=
      ((hIsq y).add (hIsq y')).div_const 2
    refine Integrable.mono' hDom ((hmeasSum y).mul (hmeasSum y')).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;>
      nlinarith [sq_nonneg
          ((∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y))
            - (∑ j' ∈ Finset.Ico (U ω k y') (expOdometer d k ω y'),
                (φR (ω.2.1 (y', j')) - walkOp φR y'))),
        sq_nonneg
          ((∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y))
            + (∑ j' ∈ Finset.Ico (U ω k y') (expOdometer d k ω y'),
                (φR (ω.2.1 (y', j')) - walkOp φR y')))]
  refine Parking.Generic.CondExpPartition.condExp_of_countable_partition
    (μ := law d ν) (expFiltration_le d k) sel hsel _ (fun _ => 0) hIprod measurable_const
    (integrable_const 0) ?_
  rintro ⟨⟨a, b⟩, ⟨a', b'⟩⟩ S hS hSsub
  have hpiece : ∀ ω ∈ S, U ω k y = a ∧ expOdometer d k ω y = b
      ∧ U ω k y' = a' ∧ expOdometer d k ω y' = b' := by
    intro ω hω
    have heq : ((U ω k y, expOdometer d k ω y), (U ω k y', expOdometer d k ω y'))
        = ((a, b), (a', b')) := hSsub hω
    injection heq with h12 h34
    injection h12 with h1 h2
    injection h34 with h3 h4
    exact ⟨h1, h2, h3, h4⟩
  set ψ : Site d → ℝ := fun x => φR x - walkOp φR y with hψdef
  set ψ' : Site d → ℝ := fun x => φR x - walkOp φR y' with hψ'def
  have hψbound : ∀ x, |ψ x| ≤ M + |walkOp φR y| := fun x => hMbound y x
  have hψ'bound : ∀ x, |ψ' x| ≤ M + |walkOp φR y'| := fun x => hMbound y' x
  have hSsub2 : S ⊆ {ω | U ω k y = a} ∩ {ω | U ω k y' = a'} :=
    fun ω hω => ⟨(hpiece ω hω).1, (hpiece ω hω).2.2.1⟩
  have hcore := sum_prod_diffsite_core hd ν k y y' hyy' a b a' b' ψ ψ' hψbound hψ'bound hS hSsub2
  have hψwalk : walkOp ψ y = 0 := by rw [hψdef, walkOp_sub_const hd, sub_self]
  have hψ'walk : walkOp ψ' y' = 0 := by rw [hψ'def, walkOp_sub_const hd, sub_self]
  have heqS : (fun ω : Data d => S.indicator
        (fun ω => (∑ j ∈ Finset.Ico a b, ψ (ω.2.1 (y, j)))
          * (∑ j' ∈ Finset.Ico a' b', ψ' (ω.2.1 (y', j')))) ω)
      = fun ω => S.indicator (fun ω =>
          (∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y))
          * (∑ j' ∈ Finset.Ico (U ω k y') (expOdometer d k ω y'),
              (φR (ω.2.1 (y', j')) - walkOp φR y'))) ω := by
    funext ω
    by_cases h : ω ∈ S
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h,
        (hpiece ω h).1, (hpiece ω h).2.1, (hpiece ω h).2.2.1, (hpiece ω h).2.2.2]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
  rw [← heqS, hcore, hψwalk, hψ'walk]
  simp

/-! ### Reusable per-site facts: measurability, a pathwise bound, second-moment
integrability, and the integrability of a cross-site product (the same content
`condExp_crossSite_eq_zero` builds locally, extracted here for the box'-wide assembly). -/

theorem measurable_siteSum (k : ℕ) (z : Site d) (φR : Site d → ℝ) :
    Measurable (fun ω : Data d =>
      ∑ j ∈ Finset.Ico (U ω k z) (expOdometer d k ω z), (φR (ω.2.1 (z, j)) - walkOp φR z)) := by
  have hmeasrange : Measurable fun ω : Data d => (U ω k z, expOdometer d k ω z) :=
    ((measurable_U_expFiltration k z).mono (expFiltration_le d k) le_rfl).prodMk
      ((measurable_expOdometer k z).mono (expFiltration_le d k) le_rfl)
  have hmeasj : ∀ j : ℕ, Measurable (fun ω : Data d => φR (ω.2.1 (z, j)) - walkOp φR z) :=
    fun j => ((measurable_from_countable' φR).comp
      ((measurable_pi_apply (z, j)).comp (measurable_fst.comp measurable_snd))).sub
      measurable_const
  exact measurable_of_countable_partition (fun ω => (U ω k z, expOdometer d k ω z))
    hmeasrange _ (fun c ω => ∑ j ∈ Finset.Ico c.1 c.2, (φR (ω.2.1 (z, j)) - walkOp φR z))
    (fun c => Finset.measurable_sum _ fun j _ => hmeasj j) (fun _ => rfl)

theorem siteSum_abs_le {φR : Site d → ℝ} {M : ℝ} (hbound : ∀ x, |φR x| ≤ M)
    (k : ℕ) (z : Site d) (ω : Data d) :
    |∑ j ∈ Finset.Ico (U ω k z) (expOdometer d k ω z), (φR (ω.2.1 (z, j)) - walkOp φR z)|
      ≤ (M + |walkOp φR z|) * ((expOdometer d k ω z : ℝ) + (U ω k z : ℝ)) := by
  have hMbound : ∀ x, |φR x - walkOp φR z| ≤ M + |walkOp φR z| := fun x => by
    calc |φR x - walkOp φR z| ≤ |φR x| + |walkOp φR z| := abs_sub _ _
      _ ≤ M + |walkOp φR z| := by linarith [hbound x]
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (φR (0 : Site d))) (hbound (0 : Site d))
  have h0 : 0 ≤ M + |walkOp φR z| := by linarith [abs_nonneg (walkOp φR z)]
  calc |∑ j ∈ Finset.Ico (U ω k z) (expOdometer d k ω z), (φR (ω.2.1 (z, j)) - walkOp φR z)|
      ≤ ∑ j ∈ Finset.Ico (U ω k z) (expOdometer d k ω z), (M + |walkOp φR z|) :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => hMbound (ω.2.1 (z, j)))
    _ = ((Finset.Ico (U ω k z) (expOdometer d k ω z)).card : ℝ) * (M + |walkOp φR z|) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (expOdometer d k ω z : ℝ) * (M + |walkOp φR z|) := by
        have hcard : (Finset.Ico (U ω k z) (expOdometer d k ω z)).card
            ≤ expOdometer d k ω z := by rw [Nat.card_Ico]; omega
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) h0
    _ ≤ (M + |walkOp φR z|) * ((expOdometer d k ω z : ℝ) + (U ω k z : ℝ)) := by
        have hUnn : (0 : ℝ) ≤ (U ω k z : ℝ) := Nat.cast_nonneg _
        nlinarith [mul_nonneg h0 hUnn]

theorem integrable_siteSum_sq (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (k : ℕ) (z : Site d) {φR : Site d → ℝ} {M : ℝ} (hbound : ∀ x, |φR x| ≤ M) :
    Integrable (fun ω : Data d =>
      (∑ j ∈ Finset.Ico (U ω k z) (expOdometer d k ω z), (φR (ω.2.1 (z, j)) - walkOp φR z)) ^ 2)
      (law d ν) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (φR (0 : Site d))) (hbound (0 : Site d))
  have h0 : 0 ≤ M + |walkOp φR z| := by linarith [abs_nonneg (walkOp φR z)]
  have hEsq : Integrable (fun ω : Data d =>
      ((expOdometer d k ω z : ℝ) + (U ω k z : ℝ)) ^ 2) (law d ν) := by
    have hUsq : Integrable (fun ω : Data d => ((U ω k z : ℕ) : ℝ) ^ 2) (law d ν) :=
      integrable_U_sq hd ν hν k z
    have hEsq0 : Integrable (fun ω : Data d => (expOdometer d k ω z : ℝ) ^ 2) (law d ν) := by
      have hcong : (fun ω : Data d => (expOdometer d k ω z : ℝ) ^ 2)
          =ᵐ[law d ν] fun ω => ((U ω (k + 1) z : ℕ) : ℝ) ^ 2 := by
        filter_upwards [U_succ_ae_eq_expOdometer hd ν k z] with ω hω
        rw [hω]
      exact (integrable_U_sq hd ν hν (k + 1) z).congr hcong.symm
    have hDom : Integrable (fun ω : Data d =>
        2 * ((expOdometer d k ω z : ℝ) ^ 2 + (U ω k z : ℝ) ^ 2)) (law d ν) :=
      (hEsq0.add hUsq).const_mul 2
    refine Integrable.mono' hDom ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact (((measurable_from_countable' (fun n : ℕ => (n : ℝ))).comp
          ((measurable_expOdometer k z).mono (expFiltration_le d k) le_rfl)).add
        ((measurable_from_countable' (fun n : ℕ => (n : ℝ))).comp
          (measurable_U k z))).pow_const 2 |>.aestronglyMeasurable
    · have hL : ‖(((expOdometer d k ω z : ℝ) + (U ω k z : ℝ)) ^ 2 : ℝ)‖
          = ((expOdometer d k ω z : ℝ) + (U ω k z : ℝ)) ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [hL]
      nlinarith [sq_nonneg ((expOdometer d k ω z : ℝ) - (U ω k z : ℝ))]
  refine Integrable.mono' (hEsq.const_mul ((M + |walkOp φR z|) ^ 2))
    ((measurable_siteSum k z φR).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have hL : ‖((∑ j ∈ Finset.Ico (U ω k z) (expOdometer d k ω z),
        (φR (ω.2.1 (z, j)) - walkOp φR z)) ^ 2 : ℝ)‖
      = (∑ j ∈ Finset.Ico (U ω k z) (expOdometer d k ω z),
          (φR (ω.2.1 (z, j)) - walkOp φR z)) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [hL]
  have hab := abs_le.mp (siteSum_abs_le hbound k z ω)
  calc (∑ j ∈ Finset.Ico (U ω k z) (expOdometer d k ω z),
        (φR (ω.2.1 (z, j)) - walkOp φR z)) ^ 2
      ≤ ((M + |walkOp φR z|) * ((expOdometer d k ω z : ℝ) + (U ω k z : ℝ))) ^ 2 :=
        sq_le_sq' hab.1 hab.2
    _ = (M + |walkOp φR z|) ^ 2 * ((expOdometer d k ω z : ℝ) + (U ω k z : ℝ)) ^ 2 := by ring

theorem integrable_siteProduct (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (k : ℕ) (y y' : Site d) {φR : Site d → ℝ} {M : ℝ} (hbound : ∀ x, |φR x| ≤ M) :
    Integrable (fun ω : Data d =>
      (∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y))
      * (∑ j' ∈ Finset.Ico (U ω k y') (expOdometer d k ω y'),
          (φR (ω.2.1 (y', j')) - walkOp φR y'))) (law d ν) := by
  have hDom : Integrable (fun ω : Data d =>
      ((∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y)) ^ 2
        + (∑ j' ∈ Finset.Ico (U ω k y') (expOdometer d k ω y'),
            (φR (ω.2.1 (y', j')) - walkOp φR y')) ^ 2) / 2) (law d ν) :=
    ((integrable_siteSum_sq hd ν hν k y hbound).add
      (integrable_siteSum_sq hd ν hν k y' hbound)).div_const 2
  refine Integrable.mono' hDom
    ((measurable_siteSum k y φR).mul (measurable_siteSum k y' φR)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;>
    nlinarith [sq_nonneg
        ((∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y))
          - (∑ j' ∈ Finset.Ico (U ω k y') (expOdometer d k ω y'),
              (φR (ω.2.1 (y', j')) - walkOp φR y'))),
      sq_nonneg
        ((∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y))
          + (∑ j' ∈ Finset.Ico (U ω k y') (expOdometer d k ω y'),
              (φR (ω.2.1 (y', j')) - walkOp φR y')))]

theorem integrable_siteSum (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (k : ℕ) (z : Site d) {φR : Site d → ℝ} {M : ℝ} (hbound : ∀ x, |φR x| ≤ M) :
    Integrable (fun ω : Data d =>
      ∑ j ∈ Finset.Ico (U ω k z) (expOdometer d k ω z), (φR (ω.2.1 (z, j)) - walkOp φR z))
      (law d ν) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  have hInt2 : Integrable (fun ω : Data d => (expOdometer d k ω z : ℝ)) (law d ν) := by
    have hcong : (fun ω : Data d => (expOdometer d k ω z : ℝ))
        =ᵐ[law d ν] fun ω => (U ω (k + 1) z : ℝ) := by
      filter_upwards [U_succ_ae_eq_expOdometer hd ν k z] with ω hω
      exact_mod_cast hω.symm
    exact (integrable_U_law hd ν hν.integrable_abs (k + 1) z).congr hcong.symm
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (φR (0 : Site d))) (hbound (0 : Site d))
  have h0 : 0 ≤ M + |walkOp φR z| := by linarith [abs_nonneg (walkOp φR z)]
  refine Integrable.mono' ((hInt2.add (integrable_U_law hd ν hν.integrable_abs k z)).const_mul
    (M + |walkOp φR z|)) (measurable_siteSum k z φR).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact siteSum_abs_le hbound k z ω

/-! ### The box-summed round increment, `expOdometer`-gated -/

/-- **The box-summed round-`k` increment**, using `expOdometer` (for the conditional-expectation
computation) rather than `U_{k+1}` (used for pathwise measurability,
`Parking.xiRound`/`Parking.Support.SpatWMartingale`). -/
def xiRoundExp (φR : Site d → ℝ) (box' : Finset (Site d)) (k : ℕ) (ω : Data d) : ℝ :=
  ∑ y ∈ box', ∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y)

/-- **`xiRoundExp` has conditional mean zero.**  `condExp_finsetSum` combined with
`condExp_siteExp_eq_zero`, one site at a time. -/
theorem condExp_xiRoundExp_eq_zero (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (k : ℕ) (box' : Finset (Site d)) {φR : Site d → ℝ} {M : ℝ} (hbound : ∀ x, |φR x| ≤ M) :
    (law d ν)[xiRoundExp φR box' k | expFiltration d k] =ᵐ[law d ν] fun _ => (0 : ℝ) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  have hInt : ∀ y ∈ box', Integrable (fun ω : Data d =>
      ∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y))
      (law d ν) := fun y _ => integrable_siteSum hd ν hν k y hbound
  have hsum := MeasureTheory.condExp_finsetSum hInt (expFiltration d k)
  have hconv : (∑ y ∈ box', fun ω : Data d =>
      ∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y))
      = xiRoundExp φR box' k := by
    funext ω
    show (∑ y ∈ box', fun ω : Data d =>
        ∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y)) ω
      = xiRoundExp φR box' k ω
    rw [Finset.sum_apply]
    rfl
  rw [hconv] at hsum
  have hzero : ∀ y ∈ box', (law d ν)[fun ω : Data d =>
      ∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y)
      | expFiltration d k] =ᵐ[law d ν] fun _ => (0 : ℝ) :=
    fun y _ => condExp_siteExp_eq_zero hd ν hν k y hbound
  have hall : ∀ᵐ ω ∂(law d ν), ∀ y ∈ box', (law d ν)[fun ω : Data d =>
      ∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y)
      | expFiltration d k] ω = 0 :=
    (Finset.eventually_all box').mpr hzero
  filter_upwards [hsum, hall] with ω h1 h2
  rw [h1, Finset.sum_apply]
  exact Finset.sum_eq_zero h2

/-- **`xiRoundExp`'s conditional second moment**: the sum over `box'` of the per-site variance,
`γ_y(φR)·(expOdometer_ky−U_ky)`, `γ_y(φR):=walkOp(φR²)y−(walkOp φR y)²`.
`condExp_finsetSum` (via `Finset.sum_product'` to turn the squared box-sum into a sum over
`box'×ˢbox'`) combined with `condExp_siteVar_eq` on the diagonal and
`condExp_crossSite_eq_zero` off it. -/
theorem condExp_xiRoundExp_sq (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (k : ℕ) (box' : Finset (Site d)) {φR : Site d → ℝ} {M : ℝ} (hbound : ∀ x, |φR x| ≤ M) :
    (law d ν)[fun ω : Data d => (xiRoundExp φR box' k ω) ^ 2 | expFiltration d k]
      =ᵐ[law d ν] fun ω => ∑ y ∈ box',
        (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2)
          * ((expOdometer d k ω y : ℝ) - (U ω k y : ℝ)) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  classical
  have hInt : ∀ p ∈ box' ×ˢ box', Integrable (fun ω : Data d =>
      (∑ j ∈ Finset.Ico (U ω k p.1) (expOdometer d k ω p.1), (φR (ω.2.1 (p.1, j)) - walkOp φR p.1))
      * (∑ j' ∈ Finset.Ico (U ω k p.2) (expOdometer d k ω p.2),
          (φR (ω.2.1 (p.2, j')) - walkOp φR p.2))) (law d ν) :=
    fun p _ => integrable_siteProduct hd ν hν k p.1 p.2 hbound
  have hsum := MeasureTheory.condExp_finsetSum hInt (expFiltration d k)
  have hconv : (fun ω : Data d => (xiRoundExp φR box' k ω) ^ 2)
      = ∑ p ∈ box' ×ˢ box', fun ω : Data d =>
          (∑ j ∈ Finset.Ico (U ω k p.1) (expOdometer d k ω p.1),
              (φR (ω.2.1 (p.1, j)) - walkOp φR p.1))
          * (∑ j' ∈ Finset.Ico (U ω k p.2) (expOdometer d k ω p.2),
              (φR (ω.2.1 (p.2, j')) - walkOp φR p.2)) := by
    funext ω
    show (xiRoundExp φR box' k ω) ^ 2 = _
    rw [Finset.sum_apply, xiRoundExp, sq, Finset.sum_mul_sum, ← Finset.sum_product']
  rw [← hconv] at hsum
  have hterm : ∀ p ∈ box' ×ˢ box', (law d ν)[fun ω : Data d =>
      (∑ j ∈ Finset.Ico (U ω k p.1) (expOdometer d k ω p.1),
          (φR (ω.2.1 (p.1, j)) - walkOp φR p.1))
      * (∑ j' ∈ Finset.Ico (U ω k p.2) (expOdometer d k ω p.2),
          (φR (ω.2.1 (p.2, j')) - walkOp φR p.2)) | expFiltration d k]
      =ᵐ[law d ν] fun ω => if p.1 = p.2 then
        (walkOp (fun x => (φR x) ^ 2) p.1 - (walkOp φR p.1) ^ 2)
          * ((expOdometer d k ω p.1 : ℝ) - (U ω k p.1 : ℝ)) else 0 := by
    intro p _
    by_cases hpp : p.1 = p.2
    · have hv := condExp_siteVar_eq hd ν hν k p.1 hbound
      filter_upwards [hv] with ω hω
      rw [if_pos hpp]
      rw [show (fun ω : Data d =>
          (∑ j ∈ Finset.Ico (U ω k p.1) (expOdometer d k ω p.1),
              (φR (ω.2.1 (p.1, j)) - walkOp φR p.1))
          * (∑ j' ∈ Finset.Ico (U ω k p.2) (expOdometer d k ω p.2),
              (φR (ω.2.1 (p.2, j')) - walkOp φR p.2)))
          = fun ω : Data d =>
            (∑ j ∈ Finset.Ico (U ω k p.1) (expOdometer d k ω p.1),
                (φR (ω.2.1 (p.1, j)) - walkOp φR p.1)) ^ 2 from by
          funext ω'; rw [hpp]; ring]
      exact hω
    · have hc := condExp_crossSite_eq_zero hd ν hν k p.1 p.2 hpp hbound
      filter_upwards [hc] with ω hω
      rw [if_neg hpp]
      exact hω
  have hall : ∀ᵐ ω ∂(law d ν), ∀ p ∈ box' ×ˢ box', (law d ν)[fun ω : Data d =>
      (∑ j ∈ Finset.Ico (U ω k p.1) (expOdometer d k ω p.1),
          (φR (ω.2.1 (p.1, j)) - walkOp φR p.1))
      * (∑ j' ∈ Finset.Ico (U ω k p.2) (expOdometer d k ω p.2),
          (φR (ω.2.1 (p.2, j')) - walkOp φR p.2)) | expFiltration d k] ω
      = if p.1 = p.2 then
          (walkOp (fun x => (φR x) ^ 2) p.1 - (walkOp φR p.1) ^ 2)
            * ((expOdometer d k ω p.1 : ℝ) - (U ω k p.1 : ℝ)) else 0 :=
    (Finset.eventually_all (box' ×ˢ box')).mpr hterm
  filter_upwards [hsum, hall] with ω h1 h2
  rw [h1, Finset.sum_apply, Finset.sum_congr rfl h2, Finset.sum_product]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Finset.sum_eq_single y]
  · rw [if_pos rfl]
  · intro y' _ hy'
    rw [if_neg (fun h => hy' h.symm)]
  · intro h; exact absurd hy h

/-! ### The bridge from `xiRoundExp` (expOdometer-gated) to `xiRound` (pathwise measurable) -/

/-- **`xiRound` and `xiRoundExp` agree almost surely.**  `Parking.U_succ_ae_eq_expOdometer`,
site by site over the finite box `box'`. -/
theorem xiRound_ae_eq_xiRoundExp (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (φR : Site d → ℝ) (box' : Finset (Site d)) (k : ℕ) :
    xiRound φR box' k =ᵐ[law d ν] xiRoundExp φR box' k := by
  have hall : ∀ᵐ ω ∂(law d ν), ∀ y ∈ box', expOdometer d k ω y = U ω (k + 1) y :=
    (Finset.eventually_all box').mpr
      (fun y _ => (U_succ_ae_eq_expOdometer hd ν k y).symm)
  filter_upwards [hall] with ω hω
  unfold xiRound xiRoundExp
  refine Finset.sum_congr rfl fun y hy => ?_
  unfold roundInc
  rw [hω y hy]

theorem integrable_xiRoundExp (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (k : ℕ) (box' : Finset (Site d)) {φR : Site d → ℝ} {M : ℝ} (hbound : ∀ x, |φR x| ≤ M) :
    Integrable (xiRoundExp φR box' k) (law d ν) :=
  integrable_finsetSum _ (fun y _ => integrable_siteSum hd ν hν k y hbound)

theorem integrable_xiRoundExp_sq (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (k : ℕ) (box' : Finset (Site d)) {φR : Site d → ℝ} {M : ℝ} (hbound : ∀ x, |φR x| ≤ M) :
    Integrable (fun ω => (xiRoundExp φR box' k ω) ^ 2) (law d ν) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  have hDom : Integrable (fun ω : Data d => (box'.card : ℝ) * ∑ y ∈ box',
      (∑ j ∈ Finset.Ico (U ω k y) (expOdometer d k ω y), (φR (ω.2.1 (y, j)) - walkOp φR y)) ^ 2)
      (law d ν) :=
    (integrable_finsetSum _ (fun y _ => integrable_siteSum_sq hd ν hν k y hbound)).const_mul _
  refine Integrable.mono' hDom ((Finset.measurable_sum box'
      (fun y _ => measurable_siteSum k y φR)).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have hL : ‖((xiRoundExp φR box' k ω) ^ 2 : ℝ)‖ = (xiRoundExp φR box' k ω) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [hL]
  unfold xiRoundExp
  exact sq_sum_le_card_mul_sum_sq

theorem integrable_xiRound (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (k : ℕ) (box' : Finset (Site d)) {φR : Site d → ℝ} {M : ℝ} (hbound : ∀ x, |φR x| ≤ M) :
    Integrable (xiRound φR box' k) (law d ν) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  exact (integrable_xiRoundExp hd ν hν k box' hbound).congr
    (xiRound_ae_eq_xiRoundExp hd ν φR box' k).symm

theorem integrable_xiRound_sq (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (k : ℕ) (box' : Finset (Site d)) {φR : Site d → ℝ} {M : ℝ} (hbound : ∀ x, |φR x| ≤ M) :
    Integrable (fun ω => (xiRound φR box' k ω) ^ 2) (law d ν) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  have hbridge : (fun ω => (xiRound φR box' k ω) ^ 2)
      =ᵐ[law d ν] fun ω => (xiRoundExp φR box' k ω) ^ 2 := by
    filter_upwards [xiRound_ae_eq_xiRoundExp hd ν φR box' k] with ω h
    rw [h]
  exact (integrable_xiRoundExp_sq hd ν hν k box' hbound).congr hbridge.symm

theorem condExp_xiRound_eq_zero (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (k : ℕ) (box' : Finset (Site d)) {φR : Site d → ℝ} {M : ℝ} (hbound : ∀ x, |φR x| ≤ M) :
    (law d ν)[xiRound φR box' k | expFiltration d k] =ᵐ[law d ν] fun _ => (0 : ℝ) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  exact (MeasureTheory.condExp_congr_ae (xiRound_ae_eq_xiRoundExp hd ν φR box' k)).trans
    (condExp_xiRoundExp_eq_zero hd ν hν k box' hbound)

theorem condExp_xiRound_sq (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (k : ℕ) (box' : Finset (Site d)) {φR : Site d → ℝ} {M : ℝ} (hbound : ∀ x, |φR x| ≤ M) :
    (law d ν)[fun ω => (xiRound φR box' k ω) ^ 2 | expFiltration d k]
      =ᵐ[law d ν] fun ω => ∑ y ∈ box',
        (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2)
          * ((expOdometer d k ω y : ℝ) - (U ω k y : ℝ)) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  have hbridge : (fun ω => (xiRound φR box' k ω) ^ 2)
      =ᵐ[law d ν] fun ω => (xiRoundExp φR box' k ω) ^ 2 := by
    filter_upwards [xiRound_ae_eq_xiRoundExp hd ν φR box' k] with ω h
    rw [h]
  exact (MeasureTheory.condExp_congr_ae hbridge).trans
    (condExp_xiRoundExp_sq hd ν hν k box' hbound)

/-! ### Feeding the round martingale square-function identity -/

theorem xiRound_sq_sum_eq (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (box' : Finset (Site d)) {φR : Site d → ℝ} {M : ℝ} (hbound : ∀ x, |φR x| ≤ M) (t : ℕ) :
    Integrable (fun ω => (∑ k ∈ Finset.range t, xiRound φR box' k ω) ^ 2) (law d ν) ∧
      ∫ ω, (∑ k ∈ Finset.range t, xiRound φR box' k ω) ^ 2 ∂(law d ν)
        = ∑ k ∈ Finset.range t, ∫ ω, (xiRound φR box' k ω) ^ 2 ∂(law d ν) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  refine Parking.Generic.RoundMartingale.integral_sq_sum_eq_sum_integral_sq
    (expFiltration d) (expFiltration_le d) (xiRound φR box') ?_
    (fun k => integrable_xiRound hd ν hν k box' hbound)
    (fun k => integrable_xiRound_sq hd ν hν k box' hbound)
    (fun k => condExp_xiRound_eq_zero hd ν hν k box' hbound) t
  intro s
  rcases Nat.eq_zero_or_pos s with hs0 | hs1
  · subst hs0
    simp only [Finset.range_zero, Finset.sum_empty]
    exact measurable_const
  · exact measurable_sum_range_xiRound φR box' hs1

/-! ### The mean odometer at round `0`, and telescoping -/

theorem meanU_zero (P : Measure (Data d)) [IsProbabilityMeasure P] : meanU P 0 = 0 := by
  unfold meanU
  have heq : (fun ω : Data d => (U ω 0 (0 : Site d) : ℝ)) = fun _ => 0 := by
    funext ω
    have : U ω 0 (0 : Site d) = 0 := rfl
    rw [this]; norm_num
  rw [heq, integral_zero]

-- `Parking.Generic.Telescope.sum_range_sub_telescope` (`Parking/Generic/Telescope.lean`) is the
-- generic real-sequence telescoping fact this file uses below; it mentions no object specific
-- to this paper, so it is stated there.

/-! ### The per-round expectation of `(xiRound)²`, in terms of `meanU` -/

theorem integral_xiRound_sq_eq (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (k : ℕ) (box' : Finset (Site d)) {φR : Site d → ℝ} {M : ℝ} (hbound : ∀ x, |φR x| ≤ M) :
    ∫ ω, (xiRound φR box' k ω) ^ 2 ∂(law d ν)
      = ∑ y ∈ box', (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2)
          * (meanU (law d ν) (k + 1) - meanU (law d ν) k) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  have htower : ∫ ω, (xiRound φR box' k ω) ^ 2 ∂(law d ν)
      = ∫ ω, (∑ y ∈ box', (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2)
          * ((expOdometer d k ω y : ℝ) - (U ω k y : ℝ))) ∂(law d ν) := by
    rw [← integral_condExp (expFiltration_le d k)
      (f := fun ω => (xiRound φR box' k ω) ^ 2) (μ := law d ν)]
    exact integral_congr_ae (condExp_xiRound_sq hd ν hν k box' hbound)
  rw [htower]
  have hIntEO : ∀ y : Site d, Integrable (fun ω : Data d => (expOdometer d k ω y : ℝ))
      (law d ν) := by
    intro y
    have hcong : (fun ω : Data d => (expOdometer d k ω y : ℝ))
        =ᵐ[law d ν] fun ω => (U ω (k + 1) y : ℝ) := by
      filter_upwards [U_succ_ae_eq_expOdometer hd ν k y] with ω hω
      exact_mod_cast hω.symm
    exact (integrable_U_law hd ν hν.integrable_abs (k + 1) y).congr hcong.symm
  have hIntTerm : ∀ y ∈ box', Integrable (fun ω : Data d =>
      (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2)
        * ((expOdometer d k ω y : ℝ) - (U ω k y : ℝ))) (law d ν) := fun y _ =>
    ((hIntEO y).sub (integrable_U_law hd ν hν.integrable_abs k y)).const_mul _
  rw [integral_finsetSum _ hIntTerm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_const_mul, integral_sub (hIntEO y) (integrable_U_law hd ν hν.integrable_abs k y)]
  have hE1 : ∫ ω, (expOdometer d k ω y : ℝ) ∂(law d ν) = meanU (law d ν) (k + 1) := by
    have hcong : (fun ω : Data d => (expOdometer d k ω y : ℝ))
        =ᵐ[law d ν] fun ω => (U ω (k + 1) y : ℝ) := by
      filter_upwards [U_succ_ae_eq_expOdometer hd ν k y] with ω hω
      exact_mod_cast hω.symm
    rw [integral_congr_ae hcong]
    exact meanU_shift_invariant hd ν (k + 1) y
  have hE2 : ∫ ω, (U ω k y : ℝ) ∂(law d ν) = meanU (law d ν) k := meanU_shift_invariant hd ν k y
  rw [hE1, hE2]

theorem sum_integral_xiRound_sq_eq (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν)
    (box' : Finset (Site d)) {φR : Site d → ℝ} {M : ℝ} (hbound : ∀ x, |φR x| ≤ M) (t : ℕ) :
    ∑ k ∈ Finset.range t, ∫ ω, (xiRound φR box' k ω) ^ 2 ∂(law d ν)
      = ∑ y ∈ box', (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2)
          * meanU (law d ν) t := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  have hstep : ∀ k, ∫ ω, (xiRound φR box' k ω) ^ 2 ∂(law d ν)
      = ∑ y ∈ box', (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2)
          * (meanU (law d ν) (k + 1) - meanU (law d ν) k) :=
    fun k => integral_xiRound_sq_eq hd ν hν k box' hbound
  calc ∑ k ∈ Finset.range t, ∫ ω, (xiRound φR box' k ω) ^ 2 ∂(law d ν)
      = ∑ k ∈ Finset.range t, ∑ y ∈ box', (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2)
          * (meanU (law d ν) (k + 1) - meanU (law d ν) k) :=
        Finset.sum_congr rfl fun k _ => hstep k
    _ = ∑ y ∈ box', ∑ k ∈ Finset.range t, (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2)
          * (meanU (law d ν) (k + 1) - meanU (law d ν) k) := Finset.sum_comm
    _ = ∑ y ∈ box', (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2)
          * ∑ k ∈ Finset.range t, (meanU (law d ν) (k + 1) - meanU (law d ν) k) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ y ∈ box', (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2)
          * (meanU (law d ν) t - meanU (law d ν) 0) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Parking.Generic.Telescope.sum_range_sub_telescope]
    _ = ∑ y ∈ box', (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2) * meanU (law d ν) t := by
        rw [meanU_zero]; simp

/-! ### `signedM` as the box-summed round martingale, pathwise -/

/-- **`signedM ω R φ`, unfolded into the box-summed round increments.**  The box'-reduction of
`Parking.Support.SpatWSignedDecomp`'s own `hMeq` (`signedPair_eq_decomposition`'s proof, not
exported there), combined with `Parking.sum_range_xiRound_eq`. -/
theorem signedM_eq_sum_xiRound {ω : Data d} (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1)
    {φ : (Fin d → ℝ) → ℝ} {B : ℝ} (hB : 0 < B)
    (hbound : ∀ x : Fin d → ℝ, φ x ≠ 0 → ‖x‖ ≤ B) {R : ℝ} (hR : 1 ≤ R) :
    signedM ω R φ = R ^ (-(d : ℝ) / 2) *
      ∑ k ∈ Finset.range ⌊R ^ 2⌋₊,
        xiRound (fun x => φ (fun i => (x i : ℝ) / R)) (boxFinset (0 : Site d) (⌈B * R⌉₊ + 1))
          k ω := by
  set box := sceneryBox d B R with hboxdef
  set box' := boxFinset (0 : Site d) (⌈B * R⌉₊ + 1) with hbox'def
  set t := ⌊R ^ 2⌋₊ with htdef
  have hnbrvanish : ∀ y : Site d, y ∉ box' → ∀ z ∈ nbrFinset y, φ (fun i => (z i : ℝ) / R) = 0 := by
    intro y hy z hz
    by_contra hne
    have hzbox : z ∈ box := by rw [hboxdef]; exact mem_sceneryBox_of_ne_zero hB hbound hR hne
    apply hy
    rw [hbox'def]
    exact nbrFinset_subset_boxFinset_succ hzbox (nbrFinset_symm hz)
  have hwalkvanish : ∀ y : Site d, y ∉ box' →
      walkOp (fun x => φ (fun i => (x i : ℝ) / R)) y = 0 := by
    intro y hy
    unfold walkOp nbrSum
    have hterm : ∀ i : Fin d, φ (fun j => ((y + unit i) j : ℝ) / R) = 0
        ∧ φ (fun j => ((y - unit i) j : ℝ) / R) = 0 :=
      fun i => ⟨hnbrvanish y hy _ (mem_nbrFinset_add y i), hnbrvanish y hy _ (mem_nbrFinset_sub y i)⟩
    have hsum0 : (∑ i : Fin d, (φ (fun j => ((y + unit i) j : ℝ) / R)
        + φ (fun j => ((y - unit i) j : ℝ) / R))) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [(hterm i).1, (hterm i).2]; ring
    rw [hsum0]; ring
  have hMeq : signedM ω R φ = R ^ (-(d : ℝ) / 2) *
      ∑ y ∈ box', (∑ j ∈ Finset.range (U ω t y), φ (fun i => ((ω.2.1 (y, j)) i : ℝ) / R)
          - (U ω t y : ℝ) * walkOp (fun x => φ (fun i => (x i : ℝ) / R)) y) := by
    unfold signedM
    rw [← htdef]
    congr 1
    apply tsum_eq_sum
    intro y hy
    have hall0 : ∀ j ∈ Finset.range (U ω t y), φ (fun i => ((ω.2.1 (y, j)) i : ℝ) / R) = 0 :=
      fun j _ => hnbrvanish y hy _ (hstep (y, j))
    rw [Finset.sum_congr rfl hall0, Finset.sum_const, hwalkvanish y hy]
    simp
  rw [hMeq, sum_range_xiRound_eq]

/-! ### The box count and the final numeric bound -/

theorem card_sceneryBox_le {B : ℝ} (hB : 0 < B) {R : ℝ} (hR : 1 ≤ R) :
    ((boxFinset (0 : Site d) (⌈B * R⌉₊ + 1)).card : ℝ) ≤ (2 * B + 5) ^ d * R ^ d := by
  have hceil : (⌈B * R⌉₊ : ℝ) < B * R + 1 := Nat.ceil_lt_add_one (by positivity)
  have hbound : ((2 * (⌈B * R⌉₊ + 1) + 1 : ℕ) : ℝ) ≤ (2 * B + 5) * R := by
    push_cast
    nlinarith [hceil]
  have hcardeq : ((boxFinset (0 : Site d) (⌈B * R⌉₊ + 1)).card : ℝ)
      = ((2 * (⌈B * R⌉₊ + 1) + 1 : ℕ) : ℝ) ^ d := by
    rw [card_boxFinset]; push_cast; ring
  rw [hcardeq]
  calc ((2 * (⌈B * R⌉₊ + 1) + 1 : ℕ) : ℝ) ^ d
      ≤ ((2 * B + 5) * R) ^ d := pow_le_pow_left₀ (by positivity) hbound d
    _ = (2 * B + 5) ^ d * R ^ d := by rw [mul_pow]

/-- **`E[signedM(φ)²] ≤ C_φ·R^{-d/2}`**, for `R ≥ 1` with `⌊R²⌋₊ ≥ 2` (`parking.tex:1758-1766`'s
own bound). Exponent bookkeeping: `R^{-d}·(box' size, O(R^d))·(L_φ/R)²·meanU(⌊R²⌋₊,
O(R^{(4-d)/2}))` collapses the `R^{-d}`/`R^d` factors and leaves `R^{-2+(4-d)/2}=R^{-d/2}`. -/
theorem integral_signedM_sq_le (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : Parking.External.SandpileGrowth) (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration) (hGreenNorms : Parking.External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) :
    ∃ Cφ : ℝ, 0 ≤ Cφ ∧ ∀ R : ℝ, 1 ≤ R → 2 ≤ ⌊R ^ 2⌋₊ →
      ∫ ω, (signedM ω R φ) ^ 2 ∂(law d ν) ≤ Cφ * R ^ (-(d : ℝ) / 2) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  obtain ⟨B, hB, hbound⟩ := exists_norm_bound_of_hasCompactSupport hφ.2
  obtain ⟨L, hL0, hLbound⟩ := testFun_nbr_diff_le hφ
  obtain ⟨c, C, hc, hcC, hmean, _⟩ :=
    (Parking.Frozen.growth hGrowth hBernstein hConcentration hGreenNorms d hd ν hν).1 hd3
  have hC0 : (0:ℝ) ≤ C := hc.le.trans hcC
  refine ⟨(2 * B + 5) ^ d * L ^ 2 * C, by positivity, fun R hR ht2 => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  set box' := boxFinset (0 : Site d) (⌈B * R⌉₊ + 1) with hbox'def
  set t := ⌊R ^ 2⌋₊ with htdef
  set φR : Site d → ℝ := fun x => φ (fun i => (x i : ℝ) / R) with hφRdef
  have hae : ∀ᵐ ω ∂(law d ν), signedM ω R φ
      = R ^ (-(d : ℝ) / 2) * ∑ k ∈ Finset.range t, xiRound φR box' k ω := by
    filter_upwards [ae_stack_nbr_law hd ν] with ω hω
    exact signedM_eq_sum_xiRound hω hB hbound hR
  have hEeq : ∫ ω, (signedM ω R φ) ^ 2 ∂(law d ν)
      = (R ^ (-(d : ℝ) / 2)) ^ 2
        * ∫ ω, (∑ k ∈ Finset.range t, xiRound φR box' k ω) ^ 2 ∂(law d ν) := by
    have hcongr : (fun ω => (signedM ω R φ) ^ 2)
        =ᵐ[law d ν] fun ω => (R ^ (-(d : ℝ) / 2)
          * ∑ k ∈ Finset.range t, xiRound φR box' k ω) ^ 2 := by
      filter_upwards [hae] with ω h; rw [h]
    rw [integral_congr_ae hcongr]
    simp_rw [mul_pow]
    rw [integral_const_mul]
  obtain ⟨M, hM0, hMbound⟩ := exists_norm_le_of_hasCompactSupport hφ.1.continuous hφ.2
  have hboundφR : ∀ x, |φR x| ≤ M := fun x => hMbound _
  rw [hEeq, (xiRound_sq_sum_eq hd ν hν box' hboundφR t).2, sum_integral_xiRound_sq_eq hd ν hν
    box' hboundφR t]
  have hgamma : ∀ y : Site d,
      (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2) ≤ (L / R) ^ 2 := by
    intro y
    refine walkOp_variance_le hd φR y (fun z hz => ?_)
    have hz' := hLbound R hR0 y z hz
    calc (φR z - φR y) ^ 2 = |φR z - φR y| ^ 2 := (sq_abs _).symm
      _ ≤ (L / R) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hz' 2
  have hsumgamma : ∑ y ∈ box', (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2)
      ≤ (box'.card : ℝ) * (L / R) ^ 2 := by
    calc ∑ y ∈ box', (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2)
        ≤ ∑ _y ∈ box', (L / R) ^ 2 := Finset.sum_le_sum (fun y _ => hgamma y)
      _ = (box'.card : ℝ) * (L / R) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hmeanUnn : (0:ℝ) ≤ meanU (law d ν) t :=
    integral_nonneg fun ω => Nat.cast_nonneg _
  have hmeanUbound : meanU (law d ν) t ≤ C * (t : ℝ) ^ ((4 - (d : ℝ)) / 4) := (hmean t ht2).2
  have hboxbound : (box'.card : ℝ) ≤ (2 * B + 5) ^ d * R ^ d := card_sceneryBox_le hB hR
  have hstep1 : ∑ y ∈ box', (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2)
        * meanU (law d ν) t
      ≤ ((box'.card : ℝ) * (L / R) ^ 2) * meanU (law d ν) t := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hsumgamma hmeanUnn
  have hstep2 : ((box'.card : ℝ) * (L / R) ^ 2) * meanU (law d ν) t
      ≤ ((2 * B + 5) ^ d * R ^ d * (L / R) ^ 2) * (C * (t : ℝ) ^ ((4 - (d : ℝ)) / 4)) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hboxbound (by positivity)
    · exact hmeanUbound
    · exact hmeanUnn
    · positivity
  have htR2 : (t : ℝ) ≤ R ^ 2 := by
    rw [htdef]; exact_mod_cast Nat.floor_le (by positivity : (0:ℝ) ≤ R ^ 2)
  have hexp0 : (0:ℝ) ≤ (4 - (d:ℝ)) / 4 := by
    have : (d:ℝ) ≤ 3 := by exact_mod_cast hd3
    linarith
  have htpow : (t : ℝ) ^ ((4 - (d:ℝ)) / 4) ≤ (R ^ 2) ^ ((4 - (d:ℝ)) / 4) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) htR2 hexp0
  have hR2pow : (R ^ (2:ℕ) : ℝ) ^ ((4 - (d:ℝ)) / 4) = R ^ ((4 - (d:ℝ)) / 2) := by
    rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR0.le]
    congr 1
    push_cast
    ring
  have hstep3 : ((2 * B + 5) ^ d * R ^ d * (L / R) ^ 2) * (C * (t : ℝ) ^ ((4 - (d:ℝ)) / 4))
      ≤ ((2 * B + 5) ^ d * R ^ d * (L / R) ^ 2) * (C * R ^ ((4 - (d:ℝ)) / 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left (htpow.trans_eq hR2pow) hC0
  have hfinal : ((2 * B + 5) ^ d * R ^ d * (L / R) ^ 2) * (C * R ^ ((4 - (d:ℝ)) / 2))
      = (2 * B + 5) ^ d * L ^ 2 * C * R ^ ((d : ℝ) / 2) := by
    have h1 : (R:ℝ) ^ d = R ^ (d:ℝ) := (Real.rpow_natCast R d).symm
    have h2 : (L / R) ^ (2:ℕ) = L ^ 2 * R ^ (-(2:ℝ)) := by
      have hcast : (R:ℝ) ^ (2:ℝ) = R ^ (2:ℕ) := by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
      rw [Real.rpow_neg hR0.le, hcast, div_pow, div_eq_mul_inv]
    rw [h1, h2]
    rw [show (2 * B + 5) ^ d * R ^ (d:ℝ) * (L ^ 2 * R ^ (-(2:ℝ)))
        * (C * R ^ ((4 - (d:ℝ)) / 2))
        = ((2 * B + 5) ^ d * L ^ 2 * C) * (R ^ (d:ℝ) * R ^ (-(2:ℝ)) * R ^ ((4 - (d:ℝ)) / 2))
        from by ring]
    congr 1
    rw [← Real.rpow_add hR0, ← Real.rpow_add hR0]
    congr 1
    ring
  have hSumBound : ∑ y ∈ box', (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2)
        * meanU (law d ν) t
      ≤ (2 * B + 5) ^ d * L ^ 2 * C * R ^ ((d : ℝ) / 2) := by
    calc ∑ y ∈ box', (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2) * meanU (law d ν) t
        ≤ ((box'.card : ℝ) * (L / R) ^ 2) * meanU (law d ν) t := hstep1
      _ ≤ ((2 * B + 5) ^ d * R ^ d * (L / R) ^ 2) * (C * (t : ℝ) ^ ((4 - (d:ℝ)) / 4)) := hstep2
      _ ≤ ((2 * B + 5) ^ d * R ^ d * (L / R) ^ 2) * (C * R ^ ((4 - (d:ℝ)) / 2)) := hstep3
      _ = (2 * B + 5) ^ d * L ^ 2 * C * R ^ ((d : ℝ) / 2) := hfinal
  have hprefactor : (R ^ (-(d : ℝ) / 2)) ^ 2 * ((2 * B + 5) ^ d * L ^ 2 * C * R ^ ((d : ℝ) / 2))
      = (2 * B + 5) ^ d * L ^ 2 * C * R ^ (-(d : ℝ) / 2) := by
    have h1 : (R ^ (-(d : ℝ) / 2)) ^ (2:ℕ) = R ^ (-(d : ℝ)) := by
      rw [← Real.rpow_natCast (R ^ (-(d : ℝ) / 2)) 2, ← Real.rpow_mul hR0.le]
      congr 1
      push_cast
      ring
    rw [h1]
    rw [show (2 * B + 5) ^ d * L ^ 2 * C * R ^ (-(d : ℝ) / 2)
        = ((2 * B + 5) ^ d * L ^ 2 * C) * R ^ (-(d : ℝ) / 2) from by ring,
      show R ^ (-(d : ℝ)) * ((2 * B + 5) ^ d * L ^ 2 * C * R ^ ((d : ℝ) / 2))
        = ((2 * B + 5) ^ d * L ^ 2 * C) * (R ^ (-(d : ℝ)) * R ^ ((d : ℝ) / 2)) from by ring,
      ← Real.rpow_add hR0]
    congr 2
    ring
  calc (R ^ (-(d : ℝ) / 2)) ^ 2
      * (∑ y ∈ box', (walkOp (fun x => (φR x) ^ 2) y - (walkOp φR y) ^ 2) * meanU (law d ν) t)
      ≤ (R ^ (-(d : ℝ) / 2)) ^ 2 * ((2 * B + 5) ^ d * L ^ 2 * C * R ^ ((d : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hSumBound (by positivity)
    _ = (2 * B + 5) ^ d * L ^ 2 * C * R ^ (-(d : ℝ) / 2) := hprefactor

/-! ### Chebyshev, and `signedM(φ) → 0` in probability -/

-- `Parking.Generic.Chebyshev.measure_gt_le_integral_sq_div_sq`
-- (`Parking/Generic/Chebyshev.lean`) is the generic Chebyshev fact this file uses below.
-- It mentions no object specific to this paper, so it is stated in the generic part of the
-- repository rather than here.

/-- **`signedM(φ) → 0` in `(law d ν)`-probability.**  `parking.tex:1758-1766`. Chebyshev applied
to `Parking.integral_signedM_sq_le`'s bound, and `Real.tendsto_rpow_neg_atTop`. -/
theorem tendsto_signedM_zero (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hGrowth : Parking.External.SandpileGrowth) (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration) (hGreenNorms : Parking.External.GreenNorms)
    (ν : Measure ℤ) (hν : CriticalLaw ν) {φ : (Fin d → ℝ) → ℝ} (hφ : IsTestFun φ) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun R : ℝ => ((law d ν) {w | ε < |signedM w R φ|}).toReal) atTop (𝓝 0) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (law d ν) := law_isProb hd ν
  obtain ⟨Cφ, hCφ0, hCφ⟩ :=
    integral_signedM_sq_le hd hd3 hGrowth hBernstein hConcentration hGreenNorms ν hν hφ
  intro ε hε
  have h1 : ∀ᶠ R : ℝ in atTop, 2 ≤ ⌊R ^ 2⌋₊ := by
    have hsq : Tendsto (fun R : ℝ => R ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num)
    have hfloor : Tendsto (fun R : ℝ => ⌊R ^ 2⌋₊) atTop atTop :=
      tendsto_nat_floor_atTop.comp hsq
    exact hfloor.eventually_ge_atTop 2
  have h2 : ∀ᶠ R : ℝ in atTop, (1:ℝ) ≤ R := eventually_ge_atTop 1
  have hIntSq : ∀ R : ℝ, 1 ≤ R → Integrable (fun ω => (signedM ω R φ) ^ 2) (law d ν) := by
    intro R hR
    obtain ⟨B, hB, hbound⟩ := exists_norm_bound_of_hasCompactSupport hφ.2
    set box' := boxFinset (0 : Site d) (⌈B * R⌉₊ + 1) with hbox'def
    set t := ⌊R ^ 2⌋₊ with htdef
    set φR : Site d → ℝ := fun x => φ (fun i => (x i : ℝ) / R) with hφRdef
    obtain ⟨M, hM0, hMbound⟩ := exists_norm_le_of_hasCompactSupport hφ.1.continuous hφ.2
    have hboundφR : ∀ x, |φR x| ≤ M := fun x => hMbound _
    have hae : ∀ᵐ ω ∂(law d ν), signedM ω R φ
        = R ^ (-(d : ℝ) / 2) * ∑ k ∈ Finset.range t, xiRound φR box' k ω := by
      filter_upwards [ae_stack_nbr_law hd ν] with ω hω
      exact signedM_eq_sum_xiRound hω hB hbound hR
    have hIsq : Integrable (fun ω =>
        (R ^ (-(d : ℝ) / 2) * ∑ k ∈ Finset.range t, xiRound φR box' k ω) ^ 2) (law d ν) := by
      simp_rw [mul_pow]
      exact ((xiRound_sq_sum_eq hd ν hν box' hboundφR t).1).const_mul _
    refine hIsq.congr ?_
    filter_upwards [hae] with ω h; rw [h]
  have hcheb : ∀ᶠ R : ℝ in atTop,
      ((law d ν) {w | ε < |signedM w R φ|}).toReal ≤ Cφ * R ^ (-(d : ℝ) / 2) / ε ^ 2 := by
    filter_upwards [h1, h2] with R hR2 hR1
    exact (Parking.Generic.Chebyshev.measure_gt_le_integral_sq_div_sq (law d ν)
      (fun w => signedM w R φ) hε
      (hIntSq R hR1)).trans (div_le_div_of_nonneg_right (hCφ R hR1 hR2) (by positivity) |>.trans_eq
        rfl)
  have hlim : Tendsto (fun R : ℝ => Cφ * R ^ (-(d : ℝ) / 2) / ε ^ 2) atTop (𝓝 0) := by
    have hexp : (0:ℝ) < (d:ℝ) / 2 := by
      have : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      linarith
    have h0 : Tendsto (fun R : ℝ => R ^ (-(d : ℝ) / 2)) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_atTop hexp
      simpa [neg_div] using this
    have h1' : Tendsto (fun R : ℝ => Cφ * R ^ (-(d : ℝ) / 2)) atTop (𝓝 (Cφ * 0)) :=
      h0.const_mul Cφ
    rw [mul_zero] at h1'
    have h2' : Tendsto (fun R : ℝ => Cφ * R ^ (-(d : ℝ) / 2) / ε ^ 2) atTop (𝓝 (0 / ε ^ 2)) :=
      h1'.div_const (ε ^ 2)
    simpa using h2'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    exact ENNReal.toReal_nonneg
  · filter_upwards [hcheb] with R hR
    exact hR

end Parking

end
