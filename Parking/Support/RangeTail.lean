/-
Paley-Zygmund for the range, Step 1 of `prop:resolvent`.

`parking.tex:2671-2683` combines the second-moment bound
`E_0|R_t|^2 ≤ 2(E_0|R_t|)^2` with Paley-Zygmund to produce a horizon `n` at
which `|R_n|` is at least `m` with probability bounded below by an absolute
constant.  This file proves the probability bound at every horizon, in the form
`P_x(|R_t| > (1/2)E_x|R_t|) ≥ 1/8`, together with the monotonicity of the range
and of its mean, which is what turns that bound into a statement about the
first horizon whose mean range exceeds `2m`.
-/
import Parking.Support.RangeMean
import LatticeProb.Prob.PaleyZygmund
import LatticeProb.Prob.CountableMeasurable

noncomputable section

open MeasureTheory

namespace Parking

open Finset

variable {d : ℕ}

/-- The range is nondecreasing in time. -/
theorem rangeCard_mono (X : ℕ → Site d) : Monotone fun t : ℕ => LatticeProb.rangeCard X t := by
  intro s t hst
  refine Finset.card_le_card (Finset.image_subset_image ?_)
  intro k hk
  simp only [Finset.mem_range] at hk ⊢
  omega

/-- The expected range is nondecreasing in time. -/
theorem integral_rangeCard_mono (hd : 1 ≤ d) (x : Site d) :
    Monotone fun t : ℕ => ∫ X, (LatticeProb.rangeCard X t : ℝ) ∂(LatticeProb.siteWalkLaw d x) := by
  haveI : NeZero d := ⟨by omega⟩
  intro s t hst
  refine integral_mono (LatticeProb.integrable_rangeCard x s)
    (LatticeProb.integrable_rangeCard x t) fun X => ?_
  exact Nat.cast_le.mpr (rangeCard_mono X hst)

/-- **Paley-Zygmund for the range.**  At every horizon the range exceeds half
its mean with probability at least `1/8`. -/
theorem rangeCard_half_mean_prob (hd : 1 ≤ d) (x : Site d) (t : ℕ) :
    (1 : ℝ) / 8 ≤ (LatticeProb.siteWalkLaw d x).real
      {X : ℕ → Site d | (1 / 2 : ℝ)
          * (∫ Y, (LatticeProb.rangeCard Y t : ℝ) ∂(LatticeProb.siteWalkLaw d x))
        < (LatticeProb.rangeCard X t : ℝ)} := by
  haveI : NeZero d := ⟨by omega⟩
  have hGpos : (0 : ℝ) < LatticeProb.srwGreen d (t + 1) 0 :=
    lt_of_lt_of_le zero_lt_one (LatticeProb.one_le_srwGreen_origin t)
  have hmpos : 0 < ∫ X, (LatticeProb.rangeCard X t : ℝ) ∂(LatticeProb.siteWalkLaw d x) := by
    refine lt_of_lt_of_le ?_ (LatticeProb.div_le_integral_rangeCard hd x t)
    have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    positivity
  have h := LatticeProb.paley_zygmund_of_second_moment (LatticeProb.siteWalkLaw d x)
    (X := fun X : ℕ → Site d => (LatticeProb.rangeCard X t : ℝ))
    ((LatticeProb.measurable_from_countable' (fun n : ℕ => (n : ℝ))).comp
      (LatticeProb.measurable_rangeCard t)) (fun _ => by positivity)
    (LatticeProb.integrable_rangeCard_sq x t) (θ := 1 / 2) (by norm_num) (by norm_num)
    hmpos (LatticeProb.integral_rangeCard_sq_le hd x t)
  norm_num at h
  exact h


/-- The scale of the Green function is nondecreasing. -/
theorem greenScale_mono (d : ℕ) : Monotone (greenScale d) := by
  intro s t hst
  have hst' : (s : ℝ) ≤ (t : ℝ) := Nat.cast_le.mpr hst
  unfold greenScale
  split_ifs with h1 h2
  · exact Real.sqrt_le_sqrt (by linarith)
  · exact Real.log_le_log (by positivity) (by linarith)
  · exact le_rfl

/-- **The horizon in dimension three and above.**  For every `m` there is a
horizon `n ≤ C(m+1)` at which the expected range is at least `m`.  This is the
choice of `n` in Step 1 of the proof of `prop:resolvent`
(`parking.tex:2680-2684`) in the case `d ≥ 3`, where the scale is bounded. -/
theorem exists_horizon_high (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, ∃ n : ℕ, (n : ℝ) ≤ C * ((m : ℝ) + 1) ∧
      (m : ℝ) ≤ ∫ X, (LatticeProb.rangeCard X n : ℝ) ∂(LatticeProb.siteWalkLaw d 0) := by
  obtain ⟨c, hc, hlow⟩ := exists_meanRange_lower (d := d) (by omega)
  have hg : ∀ t : ℕ, greenScale d t = 1 := by
    intro t
    have h1 : d ≠ 1 := by omega
    have h2 : d ≠ 2 := by omega
    simp only [greenScale, if_neg h1, if_neg h2]
  refine ⟨c⁻¹ + 1, by positivity, fun m => ?_⟩
  refine ⟨⌈(m : ℝ) / c⌉₊, ?_, ?_⟩
  · have hmm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hceil : (⌈(m : ℝ) / c⌉₊ : ℝ) ≤ (m : ℝ) / c + 1 := by
      have h := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ (m : ℝ) / c)
      linarith
    have hdiv : (m : ℝ) / c = c⁻¹ * (m : ℝ) := by
      rw [inv_mul_eq_div]
    have hcinv : (0 : ℝ) < c⁻¹ := by positivity
    nlinarith [hceil, hmm, hdiv]
  · have h := hlow 0 ⌈(m : ℝ) / c⌉₊
    rw [hg, div_one] at h
    refine le_trans ?_ h
    have hceil : (m : ℝ) / c ≤ (⌈(m : ℝ) / c⌉₊ : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hc] at hceil
    nlinarith [hceil]

end Parking

end
