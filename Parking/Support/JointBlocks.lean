/-
Step 2 of `lem:mean-horizon` on the joint space of the configuration and the walk.

The paper's Step 2 averages `1{σ>s_k} u_{ℓ_k}(X_{s_k};ξ_δ)` over BOTH the
configuration and the walk, applies Hölder's inequality to the pair, bounds the
first factor by Markov's inequality and the second by Step 1.  This file is that
computation.

The joint law is the product `jointLaw d ν`, the configuration and the walk being
independent.  Tonelli and Fubini move between the product and the iterated
integrals; the integrability they need is the a priori domination of
`Parking/Support/BlockAverages.lean` (the slice in the walk) together with the
integrability in the configuration of the block averages (the other slice).

The fifth moment on the joint space is computed once and for all in
`integral_uPair_pow`: it equals the fifth moment at the ORIGIN, by the
stationarity of `Parking/Support/BlockMoments.lean`, and it is finite because the
one-site law of the recentred scenery has every polynomial moment.
-/
import Parking.Support.BlockAverages

noncomputable section

namespace Parking

open MeasureTheory LatticeProb
open scoped ENNReal

variable {d : ℕ}

/-- The joint law of the configuration and the walk: they are independent. -/
def jointLaw (d : ℕ) (ν : Measure ℤ) : Measure ((Site d → ℤ) × (ℕ → Site d)) :=
  (LatticeProb.iidLaw d ν).prod (LatticeProb.siteWalkLaw d (0 : Site d))

theorem jointLaw_isProbability (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (jointLaw d ν) := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  rw [jointLaw]; infer_instance

/-- The odometer at the walk's position at the block's start. -/
def uPair (δ : ℝ) (ℓ s : ℕ) (p : (Site d → ℤ) × (ℕ → Site d)) : ℝ :=
  u (Parking.xi δ p.1) ℓ (p.2 s)

/-- The event that the stopping time has passed the block's start. -/
def blockEvent (σ : (Site d → ℤ) → (ℕ → Site d) → ℕ) (s : ℕ) :
    Set ((Site d → ℤ) × (ℕ → Site d)) :=
  {p | s < σ p.1 p.2}

theorem uPair_nonneg (δ : ℝ) (ℓ s : ℕ) (p : (Site d → ℤ) × (ℕ → Site d)) :
    0 ≤ uPair δ ℓ s p := u_nonneg _ _ _

theorem measurable_uPair (δ : ℝ) (ℓ s : ℕ) :
    Measurable (uPair (d := d) δ ℓ s) :=
  (measurable_u_xi_pair (d := d) δ ℓ).fun_comp
    (measurable_fst.prodMk ((measurable_pi_apply s).comp measurable_snd))

theorem measurableSet_blockEvent {σ : (Site d → ℤ) → (ℕ → Site d) → ℕ}
    (hσ : ∀ η, LatticeProb.IsWalkStopping (σ η)) {n : ℕ} (hσn : ∀ η X, σ η X ≤ n)
    (hm : ∀ X, Measurable fun η => σ η X) (s : ℕ) :
    MeasurableSet (blockEvent σ s) :=
  (measurable_uncurry_stopping hσ hσn hm) (measurableSet_Ioi (a := s))

/-- Hölder's inequality in the indicator form. -/
theorem integral_indicator_le_holder {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {A : Set Ω} (hA : MeasurableSet A) {f : Ω → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hfm : AEStronglyMeasurable f μ)
    (hf : Integrable (fun ω => |f ω| ^ (5:ℝ)) μ) :
    ∫ ω, Set.indicator A f ω ∂μ
      ≤ (μ.real A) ^ ((4:ℝ)/5) * (∫ ω, |f ω| ^ (5:ℝ) ∂μ) ^ ((1:ℝ)/5) := by
  classical
  have h := integral_ite_le_holder μ hA hf0 hfm hf
  refine le_trans (le_of_eq ?_) h
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => Set.indicator_apply A f ω)

/-- The `k`-th block term as a function on the joint space. -/
def blockPair (δ : ℝ) (σ : (Site d → ℤ) → (ℕ → Site d) → ℕ) (N k : ℕ) :
    (Site d → ℤ) × (ℕ → Site d) → ℝ :=
  Set.indicator (blockEvent σ (blockBound N k))
    (uPair δ (blockBound N (k + 1) - blockBound N k) (blockBound N k))

theorem blockPair_apply (δ : ℝ) (σ : (Site d → ℤ) → (ℕ → Site d) → ℕ) (N k : ℕ)
    (η : Site d → ℤ) (X : ℕ → Site d) :
    blockPair δ σ N k (η, X)
      = if blockBound N k < σ η X then
          u (Parking.xi δ η) (blockBound N (k + 1) - blockBound N k) (X (blockBound N k))
        else 0 := by
  classical
  rw [blockPair, Set.indicator_apply]
  by_cases h : blockBound N k < σ η X
  · rw [if_pos (show (η, X) ∈ blockEvent σ (blockBound N k) from h), if_pos h]
    rfl
  · rw [if_neg (show (η, X) ∉ blockEvent σ (blockBound N k) from h), if_neg h]

theorem blockPair_nonneg (δ : ℝ) (σ : (Site d → ℤ) → (ℕ → Site d) → ℕ) (N k : ℕ)
    (p : (Site d → ℤ) × (ℕ → Site d)) : 0 ≤ blockPair δ σ N k p := by
  rw [blockPair]
  exact Set.indicator_nonneg (fun q _ => uPair_nonneg _ _ _ q) p

/-! ### Integrability on the joint space -/

theorem measurable_blockPair {σ : (Site d → ℤ) → (ℕ → Site d) → ℕ}
    (hσ : ∀ η, LatticeProb.IsWalkStopping (σ η)) {n : ℕ} (hσn : ∀ η X, σ η X ≤ n)
    (hm : ∀ X, Measurable fun η => σ η X) (δ : ℝ) (N k : ℕ) :
    Measurable (blockPair (d := d) δ σ N k) := by
  have h := measurable_blockTerm hσ hσn hm δ (blockBound N k)
    (blockBound N (k + 1) - blockBound N k)
  have heq : blockPair (d := d) δ σ N k
      = fun p : (Site d → ℤ) × (ℕ → Site d) =>
        if blockBound N k < σ p.1 p.2 then
          u (Parking.xi δ p.1) (blockBound N (k + 1) - blockBound N k) (p.2 (blockBound N k))
        else 0 := funext fun p => blockPair_apply δ σ N k p.1 p.2
  rw [heq]
  exact h

theorem integrable_blockPair_slice (hd : 1 ≤ d) (δ : ℝ)
    {σ : (Site d → ℤ) → (ℕ → Site d) → ℕ} (hσ : ∀ η, LatticeProb.IsWalkStopping (σ η))
    {n : ℕ} (hσn : ∀ η X, σ η X ≤ n) (N k : ℕ) (η : Site d → ℤ) :
    Integrable (fun X => blockPair δ σ N k (η, X))
      (LatticeProb.siteWalkLaw d (0 : Site d)) := by
  haveI : NeZero d := ⟨by omega⟩
  have hmeas : Measurable (fun X : ℕ → Site d => blockPair δ σ N k (η, X)) := by
    have h := LatticeProb.measurable_of_dependsUpTo
      (dependsUpTo_blockU (Parking.xi δ η) (hσ η) (hσn η) (blockBound N k)
        (blockBound N (k + 1) - blockBound N k))
    have heq : (fun X : ℕ → Site d => blockPair δ σ N k (η, X))
        = fun X : ℕ → Site d =>
          if blockBound N k < σ η X then
            u (Parking.xi δ η) (blockBound N (k + 1) - blockBound N k) (X (blockBound N k))
          else 0 := funext fun X => blockPair_apply δ σ N k η X
    rw [heq]
    exact h
  refine Integrable.mono' (integrable_const (((max N (2 * n) : ℕ) : ℝ)
      * ∑ z ∈ boxFinset (0 : Site d) (n + max N (2 * n)), |Parking.xi δ η z|))
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_mem_boxFinset hd n (0 : Site d)] with X hX
  rw [Real.norm_eq_abs, abs_of_nonneg (blockPair_nonneg δ σ N k (η, X)),
    blockPair_apply]
  exact blockTerm_bound hd δ η (hσn η) k hX

theorem integrable_blockPair (hd : 1 ≤ d) {δ θ : ℝ} (hθ : 0 < θ)
    (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν)
    {σ : (Site d → ℤ) → (ℕ → Site d) → ℕ} (hσ : ∀ η, LatticeProb.IsWalkStopping (σ η))
    {n : ℕ} (hσn : ∀ η X, σ η X ≤ n) (hm : ∀ X, Measurable fun η => σ η X) (N k : ℕ) :
    Integrable (blockPair δ σ N k) (jointLaw d ν) := by
  haveI : NeZero d := ⟨by omega⟩
  rw [jointLaw]
  refine (integrable_prod_iff
    (measurable_blockPair hσ hσn hm δ N k).aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · exact Filter.Eventually.of_forall fun η => integrable_blockPair_slice hd δ hσ hσn N k η
  · refine (integrable_blockAvg (δ := δ) hd hθ ν hexp hσ hσn hm N k).congr
      (Filter.Eventually.of_forall fun η => ?_)
    rw [blockAvg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    show (if blockBound N k < σ η X then
        u (Parking.xi δ η) (blockBound N (k + 1) - blockBound N k) (X (blockBound N k))
      else 0) = ‖blockPair δ σ N k (η, X)‖
    rw [Real.norm_eq_abs, abs_of_nonneg (blockPair_nonneg δ σ N k (η, X)), blockPair_apply]

theorem integral_blockPair_eq (hd : 1 ≤ d) {δ θ : ℝ} (hθ : 0 < θ)
    (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν)
    {σ : (Site d → ℤ) → (ℕ → Site d) → ℕ} (hσ : ∀ η, LatticeProb.IsWalkStopping (σ η))
    {n : ℕ} (hσn : ∀ η X, σ η X ≤ n) (hm : ∀ X, Measurable fun η => σ η X) (N k : ℕ) :
    ∫ p, blockPair δ σ N k p ∂(jointLaw d ν)
      = ∫ η, blockAvg δ σ N k η ∂(LatticeProb.iidLaw d ν) := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have h := integral_prod (μ := LatticeProb.iidLaw d ν)
    (ν := LatticeProb.siteWalkLaw d (0 : Site d)) (blockPair δ σ N k)
    (by rw [← jointLaw]; exact integrable_blockPair hd hθ ν hexp hσ hσn hm N k)
  rw [← jointLaw] at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  rw [blockAvg]
  exact integral_congr_ae (Filter.Eventually.of_forall fun X => blockPair_apply δ σ N k η X)

/-! ### The fifth moment on the joint space -/

theorem uPair_pow_abs (δ : ℝ) (ℓ s : ℕ) (p : (Site d → ℤ) × (ℕ → Site d)) :
    |uPair δ ℓ s p| ^ (5:ℝ) = uPair δ ℓ s p ^ (5:ℕ) := by
  rw [abs_of_nonneg (uPair_nonneg δ ℓ s p), show (5:ℝ) = ((5:ℕ):ℝ) by norm_num,
    Real.rpow_natCast]

theorem lintegral_uPair_pow (hd : 1 ≤ d) {δ θ : ℝ} (hθ : 0 < θ)
    (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) (ℓ s : ℕ) :
    ∫⁻ p, ENNReal.ofReal (|uPair δ ℓ s p| ^ (5:ℝ)) ∂(jointLaw d ν)
      = ENNReal.ofReal (∫ η, u (Parking.xi δ η) ℓ 0 ^ (5:ℕ) ∂(LatticeProb.iidLaw d ν)) := by
  have hIA : Integrable (fun η : Site d → ℤ => u (Parking.xi δ η) ℓ 0 ^ (5:ℕ))
      (LatticeProb.iidLaw d ν) := integrable_u_xi_pow (δ := δ) hd hθ ν hexp 5 ℓ 0
  have h1 : ∫⁻ p, ENNReal.ofReal (|uPair δ ℓ s p| ^ (5:ℝ)) ∂(jointLaw d ν)
      = ∫⁻ p, ENNReal.ofReal (u (Parking.xi δ p.1) ℓ (p.2 s) ^ (5:ℕ)) ∂(jointLaw d ν) := by
    refine lintegral_congr fun p => ?_
    rw [uPair_pow_abs]
    rfl
  rw [h1, jointLaw, lintegral_prod_u_xi hd δ ν ℓ s,
    ← ofReal_integral_eq_lintegral_ofReal hIA
      (Filter.Eventually.of_forall fun η => pow_nonneg (u_nonneg _ _ _) 5)]

theorem integrable_uPair_pow (hd : 1 ≤ d) {δ θ : ℝ} (hθ : 0 < θ)
    (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) (ℓ s : ℕ) :
    Integrable (fun p => |uPair δ ℓ s p| ^ (5:ℝ)) (jointLaw d ν) := by
  refine ⟨((measurable_uPair (d := d) δ ℓ s).abs.pow_const (5:ℝ)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun p => Real.rpow_nonneg (abs_nonneg _) _),
    lintegral_uPair_pow hd hθ ν hexp ℓ s]
  exact ENNReal.ofReal_lt_top

theorem integral_uPair_pow (hd : 1 ≤ d) {δ θ : ℝ} (hθ : 0 < θ)
    (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) (ℓ s : ℕ) :
    ∫ p, |uPair δ ℓ s p| ^ (5:ℝ) ∂(jointLaw d ν)
      = ∫ η, u (Parking.xi δ η) ℓ 0 ^ (5:ℕ) ∂(LatticeProb.iidLaw d ν) := by
  have hA0 : (0:ℝ) ≤ ∫ η, u (Parking.xi δ η) ℓ 0 ^ (5:ℕ) ∂(LatticeProb.iidLaw d ν) :=
    integral_nonneg fun η => pow_nonneg (u_nonneg _ _ _) 5
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun p => Real.rpow_nonneg (abs_nonneg _) _)
    ((measurable_uPair (d := d) δ ℓ s).abs.pow_const (5:ℝ)).aestronglyMeasurable,
    lintegral_uPair_pow hd hθ ν hexp ℓ s, ENNReal.toReal_ofReal hA0]

/-! ### The chance that the stopping time reaches a block -/

theorem integrable_sigma_prod (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {σ : (Site d → ℤ) → (ℕ → Site d) → ℕ} (hσ : ∀ η, LatticeProb.IsWalkStopping (σ η))
    {n : ℕ} (hσn : ∀ η X, σ η X ≤ n) (hm : ∀ X, Measurable fun η => σ η X) :
    Integrable (fun p : (Site d → ℤ) × (ℕ → Site d) => ((σ p.1 p.2 : ℕ) : ℝ))
      (jointLaw d ν) := by
  haveI := jointLaw_isProbability hd ν
  have hmeas : Measurable (fun p : (Site d → ℤ) × (ℕ → Site d) => ((σ p.1 p.2 : ℕ) : ℝ)) :=
    (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp
      (measurable_uncurry_stopping hσ hσn hm)
  refine Integrable.mono' (integrable_const ((n : ℝ))) hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast hσn p.1 p.2

theorem integral_sigma_prod (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {σ : (Site d → ℤ) → (ℕ → Site d) → ℕ} (hσ : ∀ η, LatticeProb.IsWalkStopping (σ η))
    {n : ℕ} (hσn : ∀ η X, σ η X ≤ n) (hm : ∀ X, Measurable fun η => σ η X) :
    ∫ p, ((σ p.1 p.2 : ℕ) : ℝ) ∂(jointLaw d ν)
      = ∫ η, ∫ X, ((σ η X : ℕ) : ℝ) ∂(LatticeProb.siteWalkLaw d (0 : Site d))
        ∂(LatticeProb.iidLaw d ν) := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have h := integral_prod (μ := LatticeProb.iidLaw d ν)
    (ν := LatticeProb.siteWalkLaw d (0 : Site d))
    (fun p : (Site d → ℤ) × (ℕ → Site d) => ((σ p.1 p.2 : ℕ) : ℝ))
    (by rw [← jointLaw]; exact integrable_sigma_prod hd ν hσ hσn hm)
  rw [← jointLaw] at h
  exact h

theorem measureReal_blockEvent_le (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {σ : (Site d → ℤ) → (ℕ → Site d) → ℕ} (hσ : ∀ η, LatticeProb.IsWalkStopping (σ η))
    {n : ℕ} (hσn : ∀ η X, σ η X ≤ n) (hm : ∀ X, Measurable fun η => σ η X)
    {s : ℕ} (hs : 0 < s) :
    (jointLaw d ν).real (blockEvent σ s)
      ≤ (∫ η, ∫ X, ((σ η X : ℕ) : ℝ) ∂(LatticeProb.siteWalkLaw d (0 : Site d))
          ∂(LatticeProb.iidLaw d ν)) / (s : ℝ) := by
  haveI := jointLaw_isProbability hd ν
  have hs' : (0:ℝ) < (s : ℝ) := by exact_mod_cast hs
  have h := measureReal_gt_le_div (jointLaw d ν)
    (f := fun p : (Site d → ℤ) × (ℕ → Site d) => ((σ p.1 p.2 : ℕ) : ℝ))
    (fun p => Nat.cast_nonneg _) (integrable_sigma_prod hd ν hσ hσn hm) hs'
  rw [integral_sigma_prod hd ν hσ hσn hm] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext p
  simp only [blockEvent, Set.mem_setOf_eq]
  exact_mod_cast Iff.rfl

theorem measureReal_blockEvent_le_one (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (σ : (Site d → ℤ) → (ℕ → Site d) → ℕ) (s : ℕ) :
    (jointLaw d ν).real (blockEvent σ s) ≤ 1 := by
  haveI := jointLaw_isProbability hd ν
  exact measureReal_le_one

/-! ### Hölder on one block -/

/-- **Hölder's inequality on one block** (`parking.tex:2820-2824`).  The block's
contribution is at most the chance that the stopping time reaches it, to the power
`1 - 1/5`, times the fifth moment norm of the odometer at the block's length. -/
theorem integral_blockAvg_le (hd : 1 ≤ d) {δ θ : ℝ} (hθ : 0 < θ)
    (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν)
    {σ : (Site d → ℤ) → (ℕ → Site d) → ℕ} (hσ : ∀ η, LatticeProb.IsWalkStopping (σ η))
    {n : ℕ} (hσn : ∀ η X, σ η X ≤ n) (hm : ∀ X, Measurable fun η => σ η X) (N k : ℕ) :
    ∫ η, blockAvg δ σ N k η ∂(LatticeProb.iidLaw d ν)
      ≤ ((jointLaw d ν).real (blockEvent σ (blockBound N k))) ^ ((4:ℝ)/5)
        * (∫ η, u (Parking.xi δ η) (blockBound N (k + 1) - blockBound N k) 0 ^ (5:ℕ)
            ∂(LatticeProb.iidLaw d ν)) ^ ((1:ℝ)/5) := by
  haveI := jointLaw_isProbability hd ν
  rw [← integral_blockPair_eq hd hθ ν hexp hσ hσn hm N k]
  have h := integral_indicator_le_holder (jointLaw d ν)
    (measurableSet_blockEvent hσ hσn hm (blockBound N k))
    (f := uPair δ (blockBound N (k + 1) - blockBound N k) (blockBound N k))
    (uPair_nonneg _ _ _) (measurable_uPair (d := d) _ _ _).aestronglyMeasurable
    (integrable_uPair_pow hd hθ ν hexp _ _)
  rw [integral_uPair_pow hd hθ ν hexp] at h
  exact h

/-! ### The scale is monotone -/

theorem phi_mono (d : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : phi d a ≤ phi d b := by
  simp only [phi]
  split_ifs with h
  · have hd3 : (d:ℝ) ≤ 3 := by exact_mod_cast h
    exact Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
  · exact Real.log_le_log (by linarith) (by linarith)

end Parking

end
