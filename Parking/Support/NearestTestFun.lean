/-
A nonnegative test function supported in a prescribed `ℓ¹` ball, with a positive
value at the origin.

The continuum statement (S) of `parking.tex:1813-1814` asks for a DETERMINISTIC
test function `φ ≥ 0` whose support lies in the `ℓ¹` ball of a prescribed radius
and which is not identically zero, so that `∫ φ(x) v(1,x) dx > 0` follows from
the positivity of `v` on the open set where the continuum field is positive.
A smooth bump of the right radius supplies it: the supremum norm of `ℝ^d`
controls the `ℓ¹` norm by the factor `d`, so a bump of radius `r/(d+1)` is
supported in the `ℓ¹` ball of radius `r`.
-/
import Parking.Support.Continuum
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace Parking

/-- **A nonnegative test function supported in the `ℓ¹` ball of radius `r`,
equal to one at the origin.** -/
theorem exists_testFun_ellOne (d : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ φ : (Fin d → ℝ) → ℝ, IsTestFun φ ∧ (∀ x, 0 ≤ φ x) ∧ φ 0 = 1 ∧
      ∀ x ∈ tsupport φ, (∑ i, |x i|) ≤ r := by
  have hd : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  set ρ : ℝ := r / ((d : ℝ) + 1) with hρdef
  have hρ : 0 < ρ := by positivity
  let f : ContDiffBump (0 : Fin d → ℝ) := ⟨ρ / 2, ρ, by linarith, by linarith⟩
  refine ⟨fun x => f x, ⟨f.contDiff, f.hasCompactSupport⟩, fun x => f.nonneg, ?_, ?_⟩
  · simpa using f.one_of_mem_closedBall (by simp [f.rIn_pos.le])
  · intro x hx
    have hlt : ‖x‖ ≤ ρ := by
      have : x ∈ Metric.closedBall (0 : Fin d → ℝ) f.rOut := by
        rw [← f.tsupport_eq]; exact hx
      simpa using this
    have hsum : (∑ i, |x i|) ≤ (d : ℝ) * ‖x‖ := by
      calc (∑ i : Fin d, |x i|) ≤ ∑ _i : Fin d, ‖x‖ :=
            Finset.sum_le_sum fun i _ => by simpa using norm_le_pi_norm x i
        _ = (d : ℝ) * ‖x‖ := by simp
    have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hstep : (d : ℝ) * ‖x‖ ≤ (d : ℝ) * ρ := by
      exact mul_le_mul_of_nonneg_left hlt hdnn
    have hfin : (d : ℝ) * ρ ≤ r := by
      rw [hρdef, mul_div_assoc']
      rw [div_le_iff₀ hd]
      nlinarith [hr.le]
    linarith

/-- **From the pathwise positivity of the continuum signed pair to the statement
(S) of `parking.tex:1813-1814`.**  The test function and the level of (S) are
DETERMINISTIC while the ball on which the continuum field is positive at time one
is random, so the radius has to be produced first, by continuity from below over
the shrinking balls; only then is the bump chosen.  What is left to prove is the
pathwise hypothesis `hid`, the mollification identity
`⟨W,φ⟩ + ∫ U(1,·) Lφ = ∫ φ v(1,·) > 0`. -/
theorem exists_signed_level_of_pathwise {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : ((Fin d → ℝ) → ℝ) → Ω → ℝ) (Uc : Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hmeas : ∀ φ : (Fin d → ℝ) → ℝ, IsTestFun φ →
      Measurable fun ω => W φ ω + ∫ x, Uc ω 1 x * contOp d φ x)
    (hpos : ∀ᵐ ω ∂Q, ∃ r : ℝ, 0 < r ∧ ∀ x : Fin d → ℝ, (∑ i, |x i|) ≤ r → 0 < Uc ω 1 x)
    (hid : ∀ᵐ ω ∂Q, ∀ φ : (Fin d → ℝ) → ℝ, IsTestFun φ → (∀ x, 0 ≤ φ x) → φ 0 = 1 →
      (∀ x ∈ tsupport φ, 0 < Uc ω 1 x) →
      0 < W φ ω + ∫ x, Uc ω 1 x * contOp d φ x)
    {r₀ : ℝ} (hr₀ : 0 < r₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ (φ : (Fin d → ℝ) → ℝ) (a : ℝ), IsTestFun φ ∧ (∀ x, 0 ≤ φ x) ∧
      (∀ x : Fin d → ℝ, 0 < φ x → (∑ i, |x i|) ≤ r₀) ∧ 0 < a ∧
      Measurable (fun ω => W φ ω + ∫ x, Uc ω 1 x * contOp d φ x) ∧
      1 - ε ≤ (Q {ω | a ≤ W φ ω + ∫ x, Uc ω 1 x * contOp d φ x}).toReal := by
  classical
  rcases le_or_gt 1 ε with hge | hlt
  · obtain ⟨φ, hφtest, hφ0, hφ1, hφsupp⟩ := exists_testFun_ellOne d hr₀
    refine ⟨φ, 1, hφtest, hφ0, fun x hx => hφsupp x (subset_tsupport φ (by exact ne_of_gt hx)), one_pos,
      hmeas φ hφtest, ?_⟩
    have h0 : (0 : ℝ) ≤ (Q {ω | (1 : ℝ) ≤ W φ ω + ∫ x, Uc ω 1 x * contOp d φ x}).toReal :=
      ENNReal.toReal_nonneg
    linarith
  set rn : ℕ → ℝ := fun n => min r₀ (1 / (n + 1 : ℝ)) with hrn
  have hrnpos : ∀ n, 0 < rn n := fun n => lt_min hr₀ (by positivity)
  have hrnle : ∀ n, rn n ≤ r₀ := fun n => min_le_left _ _
  have hrnanti : ∀ n m : ℕ, n ≤ m → rn m ≤ rn n := by
    intro n m h
    refine min_le_min le_rfl ?_
    have : ((n : ℝ) + 1) ≤ ((m : ℝ) + 1) := by exact_mod_cast Nat.succ_le_succ h
    exact one_div_le_one_div_of_le (by positivity) this
  set P : Ω → Prop := fun ω => ∀ φ : (Fin d → ℝ) → ℝ, IsTestFun φ → (∀ x, 0 ≤ φ x) → φ 0 = 1 →
    (∀ x ∈ tsupport φ, 0 < Uc ω 1 x) →
    0 < W φ ω + ∫ x, Uc ω 1 x * contOp d φ x with hP
  set A : ℕ → Set Ω :=
    fun n => {ω | P ω ∧ ∀ x : Fin d → ℝ, (∑ i, |x i|) ≤ rn n → 0 < Uc ω 1 x} with hA
  have hmono : Monotone A := by
    intro n m hnm ω hω
    exact ⟨hω.1, fun x hx => hω.2 x (le_trans hx (hrnanti n m hnm))⟩
  have hcover :
      {ω | P ω ∧ ∃ r : ℝ, 0 < r ∧ ∀ x : Fin d → ℝ, (∑ i, |x i|) ≤ r → 0 < Uc ω 1 x}
      ⊆ ⋃ n, A n := by
    rintro ω ⟨hPω, r, hr, hball⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
    refine Set.mem_iUnion.mpr ⟨n, ⟨hPω, fun x hx => ?_⟩⟩
    exact hball x (le_trans (le_trans hx (min_le_right _ _)) hn.le)
  have hae : ∀ᵐ ω ∂Q,
      P ω ∧ ∃ r : ℝ, 0 < r ∧ ∀ x : Fin d → ℝ, (∑ i, |x i|) ≤ r → 0 < Uc ω 1 x := by
    filter_upwards [hid, hpos] with ω h1 h2 using ⟨h1, h2⟩
  have hnull : Q (⋃ n, A n)ᶜ = 0 := by
    have hp := MeasureTheory.ae_iff.mp hae
    have hsubset : (⋃ n, A n)ᶜ ⊆
        {ω | ¬ (P ω ∧ ∃ r : ℝ, 0 < r ∧
          ∀ x : Fin d → ℝ, (∑ i, |x i|) ≤ r → 0 < Uc ω 1 x)} :=
      fun ω hω hc => hω (hcover hc)
    exact measure_mono_null hsubset hp
  have hfull : Q (⋃ n, A n) = 1 := by
    refine le_antisymm prob_le_one ?_
    have h := measure_union_le (μ := Q) (⋃ n, A n) (⋃ n, A n)ᶜ
    rw [Set.union_compl_self, measure_univ, hnull, add_zero] at h
    exact h
  have hsup : ⨆ n, Q (A n) = 1 := by rw [← hmono.measure_iUnion, hfull]
  have hlt1 : ENNReal.ofReal (1 - ε) < ⨆ n, Q (A n) := by
    rw [hsup]
    exact ENNReal.ofReal_lt_one.mpr (by linarith)
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hlt1
  obtain ⟨φ, hφtest, hφ0, hφ1, hφsupp⟩ := exists_testFun_ellOne d (hrnpos n)
  set S : Ω → ℝ := fun ω => W φ ω + ∫ x, Uc ω 1 x * contOp d φ x with hS
  have hSm : Measurable S := hmeas φ hφtest
  have hsubpos : A n ⊆ {ω | 0 < S ω} := by
    intro ω hω
    exact hω.1 φ hφtest hφ0 hφ1 (fun x hx => hω.2 x (hφsupp x hx))

  set B : ℕ → Set Ω := fun k => {ω | (1 / (k + 1 : ℝ)) ≤ S ω} with hB
  have hBm : ∀ k, MeasurableSet (B k) := fun k => measurableSet_le measurable_const hSm
  have hBmono : Monotone B := by
    intro k l hkl ω hω
    simp only [hB, Set.mem_setOf_eq] at hω ⊢
    refine le_trans ?_ hω
    have : ((k : ℝ) + 1) ≤ ((l : ℝ) + 1) := by exact_mod_cast Nat.succ_le_succ hkl
    exact one_div_le_one_div_of_le (by positivity) this
  have hBunion : (⋃ k, B k) = {ω | 0 < S ω} := by
    ext ω
    constructor
    · rintro hω
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hω
      simp only [hB, Set.mem_setOf_eq] at hk
      have hp : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
      exact lt_of_lt_of_le hp hk
    · intro hω
      simp only [Set.mem_setOf_eq] at hω
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hω
      exact Set.mem_iUnion.mpr ⟨k, hk.le⟩
  have hchain : ENNReal.ofReal (1 - ε) < ⨆ k, Q (B k) := by
    rw [← hBmono.measure_iUnion, hBunion]
    exact lt_of_lt_of_le hn (measure_mono hsubpos)
  obtain ⟨k, hk⟩ := lt_iSup_iff.mp hchain
  refine ⟨φ, 1 / (k + 1 : ℝ), hφtest, hφ0,
    fun x hx => le_trans (hφsupp x (subset_tsupport φ (by exact ne_of_gt hx))) (hrnle n),
    by positivity, hSm, ?_⟩
  have h2 := ENNReal.toReal_mono (measure_ne_top Q _) hk.le
  rwa [ENNReal.toReal_ofReal (by linarith)] at h2

end Parking

end
