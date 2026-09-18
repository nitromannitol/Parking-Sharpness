/-
Step 1 of `prop:near-divisible` (`parking.tex:2848-2859`).

"For each `n`, let `σ_n` be the first `j ≤ n` for which `u^δ_{n-j}(X_j) = 0`.
Dynamic programming shows that `σ_n` attains the supremum in eq:stopping.  Let
`M_n = E σ_n`.  Since `η_δ = ξ_δ - δ`, Lemma lem:mean-horizon gives
`E u_n^δ(0) ≤ C φ_d(M_n) - δ M_n`.  Taking the supremum over `M ≥ 0` gives the
upper bound.  The resulting bound is uniform in `n`, so the monotone convergence
theorem applies."

The dynamic programming step is the shared library's optimal stopping
representation, `LatticeProb.Graph.Zd.sandpileOptimalStopping'`: the odometer is
the value of the stopping problem AND is attained at `zdOptimalStop`, the first
time the remaining value vanishes.  `Parking.optStop` is that rule read in the
integer configuration.  What has to be supplied here is what
`lem:mean-horizon` asks of a rule: that it is a stopping time of the walk, that
it is bounded by the horizon, and that it is measurable in the configuration.
The first two are read off the infimum (the horizon itself always lies in the
set), and the third is the countability of the range together with the
measurability of the odometer in the configuration.

The optimization over `M ≥ 0` is `Parking.exists_phi_sub_le_nearRate` of
`Parking/Support/NearOptimize.lean`, and "the monotone convergence theorem
applies" is the supremum defining `Parking.meanuLimit`.
-/
import Parking.Support.NearLower
import Parking.Support.MeanHorizonProof
import Parking.Support.NearOptimize
import Parking.External.Stopping

open MeasureTheory ProbabilityTheory LatticeProb

noncomputable section
namespace Parking
variable {d : ℕ}

/-- The optimal stopping value of the walk problem is the sandpile odometer. -/
theorem zdStoppingValue_eq_u (hd : 1 ≤ d) (ζ : Site d → ℝ) (m : ℕ) (z : Site d) :
    LatticeProb.Graph.Zd.zdStoppingValue ζ m z = u ζ m z := by
  have h1 := (LatticeProb.Graph.Zd.sandpileOptimalStopping' d hd ζ m z).1
  have h2 : Parking.u ζ m z = LatticeProb.Graph.Zd.zdOdometer ζ m z :=
    congrFun (Parking.u_eq_zdOdometer ζ m) z
  rw [h2, h1]

/-- The set the optimal rule takes the infimum of. -/
theorem zdOptimalStop_eq (hd : 1 ≤ d) (ζ : Site d → ℝ) (n : ℕ) (X : ℕ → Site d) :
    LatticeProb.Graph.Zd.zdOptimalStop ζ n X
      = sInf {k : ℕ | k ≤ n ∧ u ζ (n - k) (X k) = 0} := by
  rw [LatticeProb.Graph.Zd.zdOptimalStop]
  congr 1
  ext k
  simp only [Set.mem_setOf_eq, zdStoppingValue_eq_u hd]

theorem zdOptimalStop_mem (_hd : 1 ≤ d) (ζ : Site d → ℝ) (n : ℕ) (X : ℕ → Site d) :
    n ∈ {k : ℕ | k ≤ n ∧ u ζ (n - k) (X k) = 0} := by
  refine ⟨le_rfl, ?_⟩
  rw [Nat.sub_self]
  rfl

theorem zdOptimalStop_le (hd : 1 ≤ d) (ζ : Site d → ℝ) (n : ℕ) (X : ℕ → Site d) :
    LatticeProb.Graph.Zd.zdOptimalStop ζ n X ≤ n := by
  rw [zdOptimalStop_eq hd]
  exact Nat.sInf_le (zdOptimalStop_mem hd ζ n X)

/-- The optimal rule is a stopping time of the walk. -/
theorem isWalkStopping_zdOptimalStop (hd : 1 ≤ d) (ζ : Site d → ℝ) (n : ℕ) :
    LatticeProb.IsWalkStopping (LatticeProb.Graph.Zd.zdOptimalStop ζ n) := by
  intro k X Y hXY hk
  rw [zdOptimalStop_eq hd] at hk ⊢
  set SX : Set ℕ := {j : ℕ | j ≤ n ∧ u ζ (n - j) (X j) = 0} with hSX
  set SY : Set ℕ := {j : ℕ | j ≤ n ∧ u ζ (n - j) (Y j) = 0} with hSY
  have hXmem : k ∈ SX := by
    rw [← hk]
    exact Nat.sInf_mem ⟨n, zdOptimalStop_mem hd ζ n X⟩
  have hYmem : k ∈ SY := by
    refine ⟨hXmem.1, ?_⟩
    rw [← hXY k le_rfl]
    exact hXmem.2
  have hlow : ∀ j : ℕ, j < k → j ∉ SY := by
    intro j hj hmem
    have hXj : j ∈ SX := by
      refine ⟨hmem.1, ?_⟩
      rw [hXY j (le_of_lt hj)]
      exact hmem.2
    have := Nat.sInf_le hXj
    rw [hk] at this
    omega
  refine le_antisymm (Nat.sInf_le hYmem) ?_
  by_contra hcon
  have hlt : sInf SY < k := by omega
  exact hlow _ hlt (Nat.sInf_mem ⟨k, hYmem⟩)

/-- The odometer is the expected reward of the optimal rule. -/
theorem u_eq_integral_zdOptimalStop (hd : 1 ≤ d) (ζ : Site d → ℝ) (n : ℕ) (x : Site d) :
    u ζ n x = ∫ X, LatticeProb.Graph.Zd.sceneryPartialSum ζ
        (LatticeProb.Graph.Zd.zdOptimalStop ζ n X) X ∂(LatticeProb.siteWalkLaw d x) := by
  have h := LatticeProb.Graph.Zd.sandpileOptimalStopping' d hd ζ n x
  rw [← zdStoppingValue_eq_u hd, h.2]

/-- The optimal stopping rule read in the integer configuration. -/
def optStop (n : ℕ) (η : Site d → ℤ) (X : ℕ → Site d) : ℕ :=
  LatticeProb.Graph.Zd.zdOptimalStop (fun y => ((η y : ℤ) : ℝ)) n X

theorem measurable_intField : Measurable (fun η : Site d → ℤ => (fun y => ((η y : ℤ) : ℝ))) :=
  measurable_pi_lambda _ fun y => measurable_intCastReal.comp (measurable_pi_apply y)

theorem measurable_u_intField (m : ℕ) (z : Site d) :
    Measurable fun η : Site d → ℤ => u (fun y => ((η y : ℤ) : ℝ)) m z :=
  (measurable_u_eval m z).comp measurable_intField

theorem measurable_optStop (hd : 1 ≤ d) (n : ℕ) (X : ℕ → Site d) :
    Measurable fun η : Site d → ℤ => optStop n η X := by
  classical
  refine measurable_to_countable' fun k => ?_
  have hchar : (fun η : Site d → ℤ => optStop n η X) ⁻¹' {k}
      = {η : Site d → ℤ | k ≤ n ∧ u (fun y => ((η y : ℤ) : ℝ)) (n - k) (X k) = 0}
        ∩ ⋂ j ∈ Finset.range k,
          {η : Site d → ℤ | ¬ (j ≤ n ∧ u (fun y => ((η y : ℤ) : ℝ)) (n - j) (X j) = 0)} := by
    ext η
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq, Finset.mem_range]
    rw [optStop, zdOptimalStop_eq hd]
    constructor
    · intro h
      refine ⟨?_, fun j hj hmem => ?_⟩
      · rw [← h]
        exact Nat.sInf_mem ⟨n, zdOptimalStop_mem hd _ n X⟩
      · have hmem' : j ∈ {i : ℕ | i ≤ n ∧ u (fun y => ((η y : ℤ) : ℝ)) (n - i) (X i) = 0} :=
          hmem
        have hle := Nat.sInf_le hmem'
        omega
    · rintro ⟨hk, hlt⟩
      have hk' : k ∈ {i : ℕ | i ≤ n ∧ u (fun y => ((η y : ℤ) : ℝ)) (n - i) (X i) = 0} := hk
      refine le_antisymm (Nat.sInf_le hk') ?_
      by_contra hcon
      exact hlt _ (not_le.mp hcon) (Nat.sInf_mem ⟨k, hk'⟩)
  rw [hchar]
  refine MeasurableSet.inter ?_ ?_
  · by_cases hkn : k ≤ n
    · have hset : {η : Site d → ℤ | k ≤ n ∧ u (fun y => ((η y : ℤ) : ℝ)) (n - k) (X k) = 0}
          = (fun η : Site d → ℤ => u (fun y => ((η y : ℤ) : ℝ)) (n - k) (X k)) ⁻¹' {0} := by
        ext η; simp [hkn]
      rw [hset]
      exact (measurable_u_intField (n - k) (X k)) (measurableSet_singleton 0)
    · have hset : {η : Site d → ℤ | k ≤ n ∧ u (fun y => ((η y : ℤ) : ℝ)) (n - k) (X k) = 0}
          = (∅ : Set (Site d → ℤ)) := by
        ext η; simp [hkn]
      rw [hset]
      exact MeasurableSet.empty
  · refine MeasurableSet.biInter (Finset.range k).countable_toSet fun j _ => ?_
    by_cases hjn : j ≤ n
    · have hset : {η : Site d → ℤ | ¬ (j ≤ n ∧ u (fun y => ((η y : ℤ) : ℝ)) (n - j) (X j) = 0)}
          = ((fun η : Site d → ℤ => u (fun y => ((η y : ℤ) : ℝ)) (n - j) (X j)) ⁻¹' {0})ᶜ := by
        ext η; simp [hjn]
      rw [hset]
      exact ((measurable_u_intField (n - j) (X j)) (measurableSet_singleton 0)).compl
    · have hset : {η : Site d → ℤ | ¬ (j ≤ n ∧ u (fun y => ((η y : ℤ) : ℝ)) (n - j) (X j) = 0)}
          = (Set.univ : Set (Site d → ℤ)) := by
        ext η; simp [hjn]
      rw [hset]
      exact MeasurableSet.univ

theorem measurable_optStop_walk (hd : 1 ≤ d) (n : ℕ) (η : Site d → ℤ) :
    Measurable (optStop n η) :=
  LatticeProb.measurable_isWalkStopping (isWalkStopping_zdOptimalStop hd _ n)
    (fun X => zdOptimalStop_le hd _ n X)

theorem integrable_optStop_walk (hd : 1 ≤ d) (n : ℕ) (η : Site d → ℤ) :
    Integrable (fun X => ((optStop n η X : ℕ) : ℝ)) (LatticeProb.siteWalkLaw d (0 : Site d)) := by
  haveI : NeZero d := ⟨by omega⟩
  refine Integrable.mono' (integrable_const ((n : ℝ)))
    (((measurable_of_countable (fun k : ℕ => ((k : ℕ) : ℝ))).comp
      (measurable_optStop_walk hd n η)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast zdOptimalStop_le hd _ n X

theorem measurable_rewardSum_walk (hd : 1 ≤ d) (δ : ℝ) (n : ℕ) (η : Site d → ℤ) :
    Measurable (fun X : ℕ → Site d =>
      ∑ j ∈ Finset.range (optStop n η X), Parking.xi δ η (X j)) := by
  classical
  have hsm : Measurable (optStop n η) := measurable_optStop_walk hd n η
  have heq : (fun X : ℕ → Site d => ∑ j ∈ Finset.range (optStop n η X), Parking.xi δ η (X j))
      = fun X => ∑ i ∈ Finset.range (n + 1),
          (if optStop n η X = i then ∑ j ∈ Finset.range i, Parking.xi δ η (X j) else 0) := by
    funext X
    rw [Finset.sum_eq_single (optStop n η X) (fun i _ hi => if_neg fun h => hi h.symm)
      (fun hmem => absurd (Finset.mem_range.mpr
        (Nat.lt_succ_of_le (zdOptimalStop_le hd _ n X))) hmem)]
    rw [if_pos rfl]
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.ite (hsm (measurableSet_singleton i)) ?_ measurable_const
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (measurable_of_countable (Parking.xi δ η)).comp (measurable_pi_apply j)

theorem integrable_rewardSum_walk (hd : 1 ≤ d) (δ : ℝ) (n : ℕ) (η : Site d → ℤ) :
    Integrable (fun X => ∑ j ∈ Finset.range (optStop n η X), Parking.xi δ η (X j))
      (LatticeProb.siteWalkLaw d (0 : Site d)) := by
  haveI : NeZero d := ⟨by omega⟩
  refine Integrable.mono'
    (integrable_const ((n : ℝ) * ∑ z ∈ boxFinset (0 : Site d) n, |Parking.xi δ η z|))
    (measurable_rewardSum_walk hd δ n η).aestronglyMeasurable ?_
  filter_upwards [ae_mem_boxFinset hd n (0 : Site d)] with X hX
  rw [Real.norm_eq_abs]
  calc |∑ j ∈ Finset.range (optStop n η X), Parking.xi δ η (X j)|
      ≤ ∑ j ∈ Finset.range (optStop n η X), |Parking.xi δ η (X j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, |Parking.xi δ η (X j)| :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun j hj => Finset.mem_range.mpr
            (lt_of_lt_of_le (Finset.mem_range.mp hj) (zdOptimalStop_le hd _ n X)))
          (fun j _ _ => abs_nonneg _)
    _ ≤ ∑ _j ∈ Finset.range n, ∑ z ∈ boxFinset (0 : Site d) n, |Parking.xi δ η z| := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjn : j ≤ n := le_of_lt (Finset.mem_range.mp hj)
        exact Finset.single_le_sum (f := fun z => |Parking.xi δ η z|)
          (fun z _ => abs_nonneg _) (hX j hjn)
    _ = (n : ℝ) * ∑ z ∈ boxFinset (0 : Site d) n, |Parking.xi δ η z| := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The reward of the optimal rule, recentred by the drift. -/
theorem sceneryPartialSum_eq_xi (δ : ℝ) (η : Site d → ℤ) (k : ℕ) (X : ℕ → Site d) :
    LatticeProb.Graph.Zd.sceneryPartialSum (fun y => ((η y : ℤ) : ℝ)) k X
      = (∑ j ∈ Finset.range k, Parking.xi δ η (X j)) - δ * k := by
  rw [LatticeProb.Graph.Zd.sceneryPartialSum]
  have he : ∀ j : ℕ, Parking.xi δ η (X j) = ((η (X j) : ℤ) : ℝ) + δ := fun j => rfl
  simp only [he, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- The odometer is the recentred reward of the optimal rule minus the drift times its mean. -/
theorem u_eq_rewardAvg_sub (hd : 1 ≤ d) (δ : ℝ) (n : ℕ) (η : Site d → ℤ) :
    u (fun y => ((η y : ℤ) : ℝ)) n 0
      = rewardAvg δ (optStop n) η
        - δ * ∫ X, ((optStop n η X : ℕ) : ℝ) ∂(LatticeProb.siteWalkLaw d (0 : Site d)) := by
  rw [u_eq_integral_zdOptimalStop hd _ n 0]
  have hcongr : ∀ X : ℕ → Site d,
      LatticeProb.Graph.Zd.sceneryPartialSum (fun y => ((η y : ℤ) : ℝ))
          (LatticeProb.Graph.Zd.zdOptimalStop (fun y => ((η y : ℤ) : ℝ)) n X) X
        = (∑ j ∈ Finset.range (optStop n η X), Parking.xi δ η (X j))
            - δ * ((optStop n η X : ℕ) : ℝ) :=
    fun X => sceneryPartialSum_eq_xi δ η _ X
  rw [integral_congr_ae (Filter.Eventually.of_forall hcongr),
    integral_sub (integrable_rewardSum_walk hd δ n η)
      ((integrable_optStop_walk hd n η).const_mul δ), rewardAvg, integral_const_mul]

theorem integrable_optStopAvg (hd : 1 ≤ d) (n : ℕ) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    Integrable (fun η : Site d → ℤ =>
        ∫ X, ((optStop n η X : ℕ) : ℝ) ∂(LatticeProb.siteWalkLaw d (0 : Site d)))
      (LatticeProb.iidLaw d ν) := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hjoint : Measurable (fun p : (Site d → ℤ) × (ℕ → Site d) =>
      ((optStop n p.1 p.2 : ℕ) : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => ((k : ℕ) : ℝ))).comp
      (measurable_uncurry_stopping (σ := fun η' : Site d → ℤ => optStop n η')
        (fun η' => isWalkStopping_zdOptimalStop hd _ n)
        (fun η' X => zdOptimalStop_le hd _ n X) (fun X => measurable_optStop hd n X))
  have hsm : StronglyMeasurable (fun η : Site d → ℤ =>
      ∫ X, ((optStop n η X : ℕ) : ℝ) ∂(LatticeProb.siteWalkLaw d (0 : Site d))) :=
    StronglyMeasurable.integral_prod_right' hjoint.stronglyMeasurable
  refine Integrable.mono' (integrable_const ((n : ℝ))) hsm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun η => ?_)
  have hnn : (0:ℝ) ≤ ∫ X, ((optStop n η X : ℕ) : ℝ) ∂(LatticeProb.siteWalkLaw d (0 : Site d)) :=
    integral_nonneg fun X => Nat.cast_nonneg _
  have hle : ∫ X, ((optStop n η X : ℕ) : ℝ) ∂(LatticeProb.siteWalkLaw d (0 : Site d))
      ≤ ∫ _X : ℕ → Site d, ((n : ℝ)) ∂(LatticeProb.siteWalkLaw d (0 : Site d)) := by
    refine integral_mono (integrable_optStop_walk hd n η) (integrable_const _) fun X => ?_
    have hle' : optStop n η X ≤ n := zdOptimalStop_le hd _ n X
    exact Nat.cast_le.mpr hle'
  rw [integral_const, probReal_univ, one_smul] at hle
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hle

/-- **Step 1 of `prop:near-divisible`** (`parking.tex:2848-2859`).  The optimal stopping rule
attains the odometer, `lem:mean-horizon` bounds its recentred reward by `C φ_d(M)`, and the
drift subtracts `δ M`; taking the supremum over the mean horizon gives the four rates of
`eq:near-divisible-upper`, uniformly in the horizon `n`. -/
theorem exists_meanu_upper (hd : 1 ≤ d) (hGrowth : Parking.External.SandpileGrowth)
    (hStopping : Parking.External.Stopping) (hConc : Parking.External.UConcentration)
    (hGreen : Parking.External.GreenNorms)
    {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ} (hfam : NearFamily δ₀ ν θ M K) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Icc (0:ℝ) δ₀, 0 < δ → δ ≤ 1 → ∀ n : ℕ,
      meanu (law d (ν δ)) n ≤ C * Parking.nearRate d δ := by
  have hfam' : NearFamily δ₀ ν θ M K := hfam
  obtain ⟨hδ₀, hθ, hprob, hmeanν, -, hexp, -⟩ := hfam
  obtain ⟨C1, hC1, hMH⟩ := exists_meanHorizon (d := d) hd hGrowth hStopping hConc hGreen hfam'
  obtain ⟨C2, hC2, hopt⟩ := exists_phi_sub_le_nearRate d hd hC1
  refine ⟨C2, hC2, fun δ hδ hδpos hδ1 n => ?_⟩
  haveI hpν : IsProbabilityMeasure (ν δ) := hprob δ hδ
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d (ν δ)) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hintexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) (ν δ) := (hexp δ hδ).1
  have hintabs : Integrable (fun k : ℤ => |(k : ℝ)|) (ν δ) :=
    (integrable_intCast_of_exp hθ (ν δ) hintexp).abs
  have hσ : ∀ η : Site d → ℤ, LatticeProb.IsWalkStopping (optStop n η) := fun η =>
    isWalkStopping_zdOptimalStop hd _ n
  have hσn : ∀ (η : Site d → ℤ) X, optStop n η X ≤ n := fun η X => zdOptimalStop_le hd _ n X
  have hm : ∀ X, Measurable fun η : Site d → ℤ => optStop n η X := fun X =>
    measurable_optStop hd n X
  set A : (Site d → ℤ) → ℝ := fun η =>
    ∫ X, ((optStop n η X : ℕ) : ℝ) ∂(LatticeProb.siteWalkLaw d (0 : Site d)) with hA
  set Mσ : ℝ := ∫ η, A η ∂(LatticeProb.iidLaw d (ν δ)) with hMσ
  obtain ⟨hIr, hbound⟩ := hMH δ hδ n (optStop n) hσ hσn hm Mσ rfl
  have hIA : Integrable A (LatticeProb.iidLaw d (ν δ)) := integrable_optStopAvg hd n (ν δ)
  have hmeanu : meanu (law d (ν δ)) n
      = (∫ η, rewardAvg δ (optStop n) η ∂(LatticeProb.iidLaw d (ν δ))) - δ * Mσ := by
    rw [meanu_eq_integral_u hd (ν δ) hintabs n]
    have hcongr : ∀ η : Site d → ℤ,
        u (fun y => ((η y : ℤ) : ℝ)) n 0 = rewardAvg δ (optStop n) η - δ * A η :=
      fun η => u_eq_rewardAvg_sub hd δ n η
    rw [integral_congr_ae (Filter.Eventually.of_forall hcongr),
      integral_sub hIr (hIA.const_mul δ), integral_const_mul]
  have hM0 : 0 ≤ Mσ := by
    rw [hMσ]
    exact integral_nonneg fun η => integral_nonneg fun X => Nat.cast_nonneg _
  have hfin := hopt δ hδpos hδ1 Mσ hM0
  rw [hmeanu]
  linarith

/-- **The upper bound of `eq:near-divisible-upper`** (`parking.tex:2831-2840`).  The bound of
Step 1 is uniform in the horizon, so the monotone limit obeys it too. -/
theorem exists_meanuLimit_upper (hd : 1 ≤ d) (hGrowth : Parking.External.SandpileGrowth)
    (hStopping : Parking.External.Stopping) (hConc : Parking.External.UConcentration)
    (hGreen : Parking.External.GreenNorms)
    {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ} (hfam : NearFamily δ₀ ν θ M K) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Icc (0:ℝ) δ₀, 0 < δ → δ ≤ 1 →
      Parking.meanuLimit (Parking.law d (ν δ)) ≤ ENNReal.ofReal (C * Parking.nearRate d δ) := by
  obtain ⟨C, hC, h⟩ := exists_meanu_upper hd hGrowth hStopping hConc hGreen hfam
  refine ⟨C, hC, fun δ hδ hδpos hδ1 => ?_⟩
  rw [Parking.meanuLimit]
  exact iSup_le fun n => ENNReal.ofReal_le_ofReal (h δ hδ hδpos hδ1 n)

/-- The limit mean dominates the mean at every horizon. -/
theorem ofReal_meanu_le_meanuLimit {P : Measure (Data d)} (n : ℕ) :
    ENNReal.ofReal (Parking.meanu P n) ≤ Parking.meanuLimit P :=
  le_iSup (fun m : ℕ => ENNReal.ofReal (Parking.meanu P m)) n
