/- Analysis support for the tail theorems downstream of `thm:subcritical`:
the exponential bounds extracted from a log-asymptotic, and the comparison of
`rangeExp` with the range-lower power integral.  `parking.tex:2499-2502`. -/
import Mathlib
import Parking.Support.Near
import Parking.Support.RangeLower

open MeasureTheory Filter Topology Set

noncomputable section

namespace Parking

/-- From a log-asymptotic `log (F t) / t ^ α → -k` with `k, α > 0` and `F` positive,
one gets two-sided exponential bounds with slack constants, valid from `t = 1`,
with a single multiplicative constant. -/
theorem exp_bounds_of_log_tendsto {F : ℕ → ℝ} (hF : ∀ t, 0 < F t)
    {k α : ℝ} (hk : 0 < k) (_hα : 0 < α)
    (hT : Tendsto (fun t : ℕ => Real.log (F t) / (t : ℝ) ^ α) atTop (𝓝 (-k))) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℕ, 1 ≤ t →
      F t ≤ C * Real.exp (-(k / 2) * (t : ℝ) ^ α) ∧
        Real.exp (-(2 * k) * (t : ℝ) ^ α) ≤ C * F t := by
  -- eventually log F t / t^α ∈ (-3k/2, -k/2)
  have hev : ∀ᶠ t : ℕ in atTop, (-3 * k / 2 < Real.log (F t) / (t : ℝ) ^ α)
      ∧ (Real.log (F t) / (t : ℝ) ^ α < -k / 2) := by
    have h1 : (-k : ℝ) ∈ Ioo (-3 * k / 2) (-k / 2) := by constructor <;> linarith
    have h2 : Ioo (-3 * k / 2) (-k / 2) ∈ 𝓝 (-k) :=
      isOpen_Ioo.mem_nhds h1
    exact Eventually.mono (hT h2) fun t ht => ⟨ht.1, ht.2⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  -- constants
  set q1 : ℝ := Real.exp (-(k / 2))
  set q2 : ℝ := Real.exp (-(2 * k))
  have hq1 : 0 < q1 := Real.exp_pos _
  have hq2 : 0 < q2 := Real.exp_pos _
  have hq1' : q1 < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hq2' : q2 < 1 := Real.exp_lt_one_iff.2 (by linarith)
  -- the finitely many small t
  set fin : Finset ℕ := (Finset.range (N + 2)).filter fun t => 1 ≤ t
  have hfinne : fin.Nonempty := by
    refine ⟨1, ?_⟩
    show 1 ∈ (Finset.range (N + 2)).filter fun t => 1 ≤ t
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  set C0 : ℝ := Finset.sup' fin hfinne fun t =>
    max (F t / Real.exp (-(k / 2) * (t : ℝ) ^ α))
        (Real.exp (-(2 * k) * (t : ℝ) ^ α) / F t)
  have hC0 : 0 ≤ C0 := by
    obtain ⟨m, hm⟩ := hfinne
    have hle := Finset.le_sup' (f := fun t : ℕ =>
      max (F t / Real.exp (-(k / 2) * (t : ℝ) ^ α))
          (Real.exp (-(2 * k) * (t : ℝ) ^ α) / F t)) hm
    exact le_trans (le_max_iff.2 (Or.inl (by
      exact div_nonneg (le_of_lt (hF m)) (Real.exp_nonneg _)))) hle
  refine ⟨max 1 C0, le_max_left _ _, fun t ht => ?_⟩
  by_cases hNt : N ≤ t
  · -- large t: use the asymptotic
    have h := hN t hNt
    have htp : 0 < (t : ℝ) ^ α := Real.rpow_pos_of_pos (Nat.cast_pos.2 ht) α
    have hFt : F t ≤ Real.exp (-(k / 2) * (t : ℝ) ^ α) := by
      have h2 := h.2
      have h3 : Real.log (F t) < -(k / 2) * (t : ℝ) ^ α := by
        have := (div_lt_iff₀ htp).mp h2
        linarith [this]
      exact le_of_lt ((Real.log_lt_iff_lt_exp (hF t)).1 h3)
    have hFt2 : Real.exp (-(2 * k) * (t : ℝ) ^ α) ≤ F t := by
      have h1 := h.1
      have h3 : -(3 * k / 2) * (t : ℝ) ^ α < Real.log (F t) := by
        have := (lt_div_iff₀ htp).mp h1
        linarith [this]
      have h6 : -(2 * k) * (t : ℝ) ^ α < -(3 * k / 2) * (t : ℝ) ^ α := by
        have h5 : 0 < (t : ℝ) ^ α := htp
        nlinarith [hk]
      have h4 : Real.exp (-(2 * k) * (t : ℝ) ^ α) < F t :=
        (Real.lt_log_iff_exp_lt (hF t)).mp (lt_of_lt_of_le h6 (le_of_lt h3))
      exact le_of_lt h4
    constructor
    · calc F t ≤ Real.exp (-(k / 2) * (t : ℝ) ^ α) := hFt
        _ = 1 * Real.exp (-(k / 2) * (t : ℝ) ^ α) := (one_mul _).symm
        _ ≤ max 1 C0 * Real.exp (-(k / 2) * (t : ℝ) ^ α) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
    · calc Real.exp (-(2 * k) * (t : ℝ) ^ α) ≤ F t := hFt2
        _ = 1 * F t := (one_mul _).symm
        _ ≤ max 1 C0 * F t := mul_le_mul_of_nonneg_right (le_max_left _ _) (hF t).le
  · -- small t: use C0
    have hmem : t ∈ fin := by
      show t ∈ (Finset.range (N + 2)).filter fun s => 1 ≤ s
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    have hle : F t / Real.exp (-(k / 2) * (t : ℝ) ^ α) ≤ C0 :=
      le_trans (le_max_iff.2 (Or.inl le_rfl))
        (Finset.le_sup' (f := fun s : ℕ =>
          max (F s / Real.exp (-(k / 2) * (s : ℝ) ^ α))
              (Real.exp (-(2 * k) * (s : ℝ) ^ α) / F s)) hmem)
    have hle2 : Real.exp (-(2 * k) * (t : ℝ) ^ α) / F t ≤ C0 :=
      le_trans (le_max_iff.2 (Or.inr le_rfl))
        (Finset.le_sup' (f := fun s : ℕ =>
          max (F s / Real.exp (-(k / 2) * (s : ℝ) ^ α))
              (Real.exp (-(2 * k) * (s : ℝ) ^ α) / F s)) hmem)
    have hexp : 0 < Real.exp (-(k / 2) * (t : ℝ) ^ α) := Real.exp_pos _
    constructor
    · have := (div_le_iff₀ hexp).1 hle
      have h5 : F t ≤ max 1 C0 * Real.exp (-(k / 2) * (t : ℝ) ^ α) := by
        calc F t = F t := rfl
          _ ≤ C0 * Real.exp (-(k / 2) * (t : ℝ) ^ α) := by
              have := (div_le_iff₀ hexp).1 hle
              linarith [this]
          _ ≤ max 1 C0 * Real.exp (-(k / 2) * (t : ℝ) ^ α) := by
              exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)
      exact h5
    · have hexp2 : 0 < F t := hF t
      have := (div_le_iff₀ hexp2).1 hle2
      have h5 : Real.exp (-(2 * k) * (t : ℝ) ^ α) ≤ max 1 C0 * F t := by
        calc Real.exp (-(2 * k) * (t : ℝ) ^ α)
            = Real.exp (-(2 * k) * (t : ℝ) ^ α) := rfl
          _ ≤ C0 * F t := by
              have := (div_le_iff₀ hexp2).1 hle2
              linarith [this]
          _ ≤ max 1 C0 * F t := by
              exact mul_le_mul_of_nonneg_right (le_max_right _ _) (hF t).le
      exact h5

theorem rangeExp_le_rangePow {d : ℕ} (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a) (t : ℕ) :
    rangeExp d a t
      ≤ ∫ p, (Real.exp (-(a * (1 : ℝ)))) ^ (rangeCard (0 : Site d) p t - 1)
          ∂(walkLaw d) := by
  haveI : IsProbabilityMeasure (walkLaw d) := walkLaw_isProbability (d := d) hd
  have hq : Real.exp (-(a * (1 : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hq0 : (0 : ℝ) ≤ Real.exp (-(a * (1 : ℝ))) := Real.exp_nonneg _
  have hpt : ∀ p : ℕ → Fin d × Bool, Real.exp (-(a * ((rangeCard (0 : Site d) p t : ℝ))))
      ≤ (Real.exp (-(a * (1 : ℝ)))) ^ (rangeCard (0 : Site d) p t - 1) := by
    intro p
    have hn : 1 ≤ rangeCard (0 : Site d) p t := one_le_rangeCard _ p t
    have hexp : Real.exp (-(a * ((rangeCard (0 : Site d) p t : ℝ))))
        = (Real.exp (-(a * (1 : ℝ)))) ^ (rangeCard (0 : Site d) p t) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hexp]
    have hn1 : rangeCard (0 : Site d) p t = (rangeCard (0 : Site d) p t - 1) + 1 := by omega
    rw [hn1, pow_succ]
    have h2 : Real.exp (-(a * (1 : ℝ))) ^ (rangeCard (0 : Site d) p t - 1)
        * Real.exp (-(a * (1 : ℝ)))
        ≤ Real.exp (-(a * (1 : ℝ))) ^ (rangeCard (0 : Site d) p t - 1) * 1 :=
      mul_le_mul_of_nonneg_left hq (pow_nonneg hq0 _)
    simpa using h2
  have hmeasL : Measurable fun p : ℕ → Fin d × Bool =>
      Real.exp (-(a * ((rangeCard (0 : Site d) p t : ℝ)))) := by
    exact (Measurable.of_discrete (β := ℝ) (f := fun n : ℕ => Real.exp (-(a * (n : ℝ))))).comp
      (measurable_rangeCard (0 : Site d) t)
  have hmeasR : Measurable fun p : ℕ → Fin d × Bool =>
      (Real.exp (-(a * (1 : ℝ)))) ^ (rangeCard (0 : Site d) p t - 1) := by
    exact (Measurable.of_discrete (β := ℝ)
      (f := fun n : ℕ => (Real.exp (-(a * (1 : ℝ)))) ^ (n - 1))).comp
      (measurable_rangeCard (0 : Site d) t)
  have hintL : Integrable (fun p => Real.exp (-(a * ((rangeCard (0 : Site d) p t : ℝ))))) (walkLaw d) := by
    refine (integrable_const (1 : ℝ)).mono' hmeasL.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.2 (by nlinarith [show (0:ℝ) ≤ (rangeCard (0 : Site d) p t : ℝ) from Nat.cast_nonneg _, ha])
  have hintR : Integrable (fun p => (Real.exp (-(a * (1 : ℝ)))) ^ (rangeCard (0 : Site d) p t - 1)) (walkLaw d) := by
    refine (integrable_const (1 : ℝ)).mono' hmeasR.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0 _)]
    have hn1 : Real.exp (-(a * (1 : ℝ))) ^ (rangeCard (0 : Site d) p t - 1)
        ≤ Real.exp (-(a * (1 : ℝ))) ^ 0 := by
      have h2 : ∀ m : ℕ, Real.exp (-(a * (1 : ℝ))) ^ (m + 1)
          ≤ Real.exp (-(a * (1 : ℝ))) ^ m := by
        intro m
        rw [pow_succ]
        have : Real.exp (-(a * (1 : ℝ))) ^ m * Real.exp (-(a * (1 : ℝ)))
            ≤ Real.exp (-(a * (1 : ℝ))) ^ m * 1 :=
          mul_le_mul_of_nonneg_left hq (pow_nonneg hq0 _)
        simpa using this
      induction rangeCard (0 : Site d) p t - 1 with
      | zero => exact le_refl _
      | succ m ih => exact le_trans (h2 m) ih
    rw [pow_zero] at hn1
    exact hn1
  exact integral_mono hintL hintR hpt

end Parking
