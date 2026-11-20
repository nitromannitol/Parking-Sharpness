import Parking.Support.ValueLipschitz
import Parking.Support.WalkMaximal
import Parking.Support.ContSpatialValue

/-!
# Local comparison of spatial stopping values

The rescaled simple random walk leaves a large ball before the horizon with small probability,
uniformly in the scale.  A reward comparison valid inside that ball therefore controls the
stopping values up to the probability of leaving it.
-/

open MeasureTheory

noncomputable section

namespace Parking

open LatticeProb

variable {d : ℕ}

/-- The event that the rescaled walk reaches sup-norm distance `A` by the step `⌊nT⌋`. -/
def spatialScaledExit (d n : ℕ) (T A : ℝ) : Set (ℕ → Fin d × Bool) :=
  {p | ∃ k ≤ ⌊(n : ℝ) * T⌋₊, A ≤ ‖spatialScaledSite n (walkPath (0 : Site d) p k)‖}

/-- The exit event is measurable. -/
theorem measurableSet_spatialScaledExit (d n : ℕ) (T A : ℝ) :
    MeasurableSet (spatialScaledExit d n T A) := by
  have heq : spatialScaledExit d n T A = ⋃ k ∈ Finset.range (⌊(n : ℝ) * T⌋₊ + 1),
      {p | A ≤ ‖spatialScaledSite n (walkPath (0 : Site d) p k)‖} := by
    ext p
    simp [spatialScaledExit]
  rw [heq]
  refine Finset.measurableSet_biUnion _ fun k _ => ?_
  exact measurableSet_le measurable_const
    ((measurable_of_countable (fun z : Site d => ‖spatialScaledSite n z‖)).comp
      (measurable_walkPath 0 k))

/-- A coordinate of a lattice site is at most its graph norm. -/
theorem abs_coord_le_graphNorm (z : Site d) (i : Fin d) :
    |((z i : ℤ) : ℝ)| ≤ (graphNorm z : ℝ) := by
  have h : (z i).natAbs ≤ graphNorm z := by
    unfold LatticeProb.graphNorm
    exact Finset.single_le_sum (f := fun j => (z j).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  calc |((z i : ℤ) : ℝ)| = ((z i).natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
    _ ≤ (graphNorm z : ℝ) := by exact_mod_cast h

/-- **The rescaled walk rarely leaves a large ball**, uniformly in the scale. -/
theorem measureReal_spatialScaledExit_le (hd : 1 ≤ d) {n : ℕ} (hn : 1 ≤ n) {T A : ℝ}
    (hT : 0 ≤ T) (hA : 0 < A) :
    (walkLaw d).real (spatialScaledExit d n T A) ≤ (d : ℝ) ^ 2 * T / A ^ 2 := by
  have := stepLaw_isProbability hd
  have : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let A' : ℝ := A * Real.sqrt n / d
  have hA' : 0 < A' := by positivity
  have hsub : spatialScaledExit d n T A ⊆
      {p | ∃ k ≤ ⌊(n : ℝ) * T⌋₊, (d : ℝ) * A' ≤ (graphNorm (walkPath (0 : Site d) p k) : ℝ)} := by
    rintro p ⟨k, hk, hp⟩
    refine ⟨k, hk, ?_⟩
    obtain ⟨i, hi⟩ : ∃ i, A ≤ ‖spatialScaledSite n (walkPath (0 : Site d) p k) i‖ := by
      by_contra h
      simp only [not_exists, not_le] at h
      exact absurd hp (not_le.mpr ((pi_norm_lt_iff hA).mpr h))
    rw [Real.norm_eq_abs, spatialScaledSite, abs_div, abs_of_pos hsq, le_div_iff₀ hsq] at hi
    have hle := abs_coord_le_graphNorm (walkPath (0 : Site d) p k) i
    have hdA : (d : ℝ) * A' = A * Real.sqrt n := by
      simp only [A']
      field_simp
    rw [hdA]
    linarith
  have hmax := measureReal_sup_walkPath_graphNorm_le hd ⌊(n : ℝ) * T⌋₊ hA'
  have hmono := measureReal_mono (μ := walkLaw d) hsub (measure_ne_top _ _)
  have hfloor : (⌊(n : ℝ) * T⌋₊ : ℝ) ≤ n * T := Nat.floor_le (mul_nonneg hnR.le hT)
  have hbound : (⌊(n : ℝ) * T⌋₊ : ℝ) / A' ^ 2 ≤ (d : ℝ) ^ 2 * T / A ^ 2 := by
    have hA'sq : A' ^ 2 = A ^ 2 * n / (d : ℝ) ^ 2 := by
      simp only [A']
      rw [div_pow, mul_pow, Real.sq_sqrt hnR.le]
    rw [hA'sq, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hpos : 0 ≤ (d : ℝ) ^ 2 * A ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hfloor hpos]
  linarith

/-- A local reward comparison and the exit probability bound the difference of spatial
stopping values. -/
theorem abs_stoppingSup_sub_le_of_local_reward (hd : 1 ≤ d)
    {n : ℕ} {T A δ M : ℝ} (hδ : 0 ≤ δ)
    (F G : ℕ → Site d → ℝ)
    (hF : ∀ k z, |F k z| ≤ M) (hG : ∀ k z, |G k z| ≤ M)
    (hlocal : ∀ p ∉ spatialScaledExit d n T A, ∀ k ≤ ⌊(n : ℝ) * T⌋₊,
      |F k (walkPath 0 p k) - G k (walkPath 0 p k)| ≤ δ) :
    |stoppingSup d F ⌊(n : ℝ) * T⌋₊ 0 - stoppingSup d G ⌊(n : ℝ) * T⌋₊ 0| ≤
      δ + 2 * M * (walkLaw d).real (spatialScaledExit d n T A) := by
  have := stepLaw_isProbability hd
  have : IsProbabilityMeasure (walkLaw d) := by unfold walkLaw; infer_instance
  let K := ⌊(n : ℝ) * T⌋₊
  let E := spatialScaledExit d n T A
  let c := δ + 2 * M * (walkLaw d).real E
  have hE : MeasurableSet E := measurableSet_spatialScaledExit d n T A
  have hterminal : ∀ {σ : (ℕ → Fin d × Bool) → ℕ}, IsStoppingTimeLE K σ →
      |terminalValue F 0 σ - terminalValue G 0 σ| ≤ c := by
    intro σ hσ
    have hFi := integrable_terminalReward hd hσ F 0
    have hGi := integrable_terminalReward hd hσ G 0
    have hpoint : ∀ p, |F (σ p) (walkPath 0 p (σ p)) - G (σ p) (walkPath 0 p (σ p))|
        ≤ δ + E.indicator (fun _ => 2 * M) p := by
      intro p
      by_cases hp : p ∈ E
      · rw [Set.indicator_of_mem hp]
        have hb := abs_sub (F (σ p) (walkPath 0 p (σ p))) (G (σ p) (walkPath 0 p (σ p)))
        have hf := hF (σ p) (walkPath 0 p (σ p))
        have hg := hG (σ p) (walkPath 0 p (σ p))
        linarith
      · rw [Set.indicator_of_notMem hp, add_zero]
        exact hlocal p hp (σ p) (hσ.1 p)
    have hi : Integrable (fun p => δ + E.indicator (fun _ => 2 * M) p) (walkLaw d) :=
      (integrable_const δ).add ((integrable_const (2 * M)).indicator hE)
    rw [terminalValue, terminalValue, ← integral_sub hFi hGi]
    calc
      |∫ p, (F (σ p) (walkPath 0 p (σ p)) - G (σ p) (walkPath 0 p (σ p))) ∂(walkLaw d)|
          ≤ ∫ p, |F (σ p) (walkPath 0 p (σ p)) - G (σ p) (walkPath 0 p (σ p))|
            ∂(walkLaw d) := abs_integral_le_integral_abs
      _ ≤ ∫ p, (δ + E.indicator (fun _ => 2 * M) p) ∂(walkLaw d) :=
        integral_mono (hFi.sub hGi).abs hi hpoint
      _ = c := by
        rw [integral_add (integrable_const δ) ((integrable_const (2 * M)).indicator hE),
          integral_indicator_const _ hE]
        simp [c, smul_eq_mul, mul_comm]
  have hbF := bddAbove_terminalValues hd F K 0 hF
  have hbG := bddAbove_terminalValues hd G K 0 hG
  have hneF := terminalValues_nonempty d F K 0
  have hneG := terminalValues_nonempty d G K 0
  have hFG : stoppingSup d F K 0 ≤ stoppingSup d G K 0 + c := by
    apply csSup_le hneF
    rintro a ⟨σ, hσ, rfl⟩
    have h1 : terminalValue G 0 σ ≤ stoppingSup d G K 0 := le_csSup hbG ⟨σ, hσ, rfl⟩
    have h2 := (abs_sub_le_iff.mp (hterminal hσ)).1
    linarith
  have hGF : stoppingSup d G K 0 ≤ stoppingSup d F K 0 + c := by
    apply csSup_le hneG
    rintro a ⟨σ, hσ, rfl⟩
    have h1 : terminalValue F 0 σ ≤ stoppingSup d F K 0 := le_csSup hbF ⟨σ, hσ, rfl⟩
    have h2 := (abs_sub_le_iff.mp (hterminal hσ)).2
    linarith
  rw [abs_sub_le_iff]
  constructor <;> linarith

end Parking
