/-
Moments of the sandpile odometer at a REAL one-site law.

`Parking/Support/UBound.lean` proves the a priori bound and the integrability of
the odometer's moments for the INTEGER field of the parking model.  Step 1 of
`lem:mean-horizon` compares the recentred scenery with the real reference law of
`Parking/Support/ConvexOrder.lean`, and needs the same two facts there.

The route is the one of `eq:apriori-finite` read in the reals.  The odometer at
time `n` reads only the box of radius `n` (`u_eq_of_eqOn_box`) and is at most `n`
times any uniform bound on the field (`u_le_mul_of_le`), so it is at most `n`
times the positive part of the field summed over that box.  Jensen's inequality
for sums of powers (`pow_sum_le_card_mul_sum_pow`) turns the `r`-th power of that
sum into a sum of `r`-th powers, one per site, and each of those is a function of
a single coordinate, whose law is the one-site law
(`Measure.infinitePi_map_eval`).  A finite exponential moment gives every
polynomial moment through `x^r/r! ≤ e^x`.
-/
import Parking.Support.UMoment
import Parking.Support.ConvexOrder

noncomputable section

namespace Parking

open MeasureTheory LatticeProb

variable {d : ℕ}

theorem u_le_mul_posBox (hd : 1 ≤ d) (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    u η n x ≤ (n : ℝ) * ∑ z ∈ boxFinset x n, max (η z) 0 := by
  classical
  set B : ℝ := ∑ z ∈ boxFinset x n, max (η z) 0 with hBdef
  have hB : 0 ≤ B := Finset.sum_nonneg fun z _ => le_max_right (η z) 0
  set ξ : Site d → ℝ := fun y => if y ∈ boxFinset x n then η y else 0 with hξdef
  have h1 : u η n x = u ξ n x := u_eq_of_eqOn_box n x fun y hy => by simp [hξdef, hy]
  have h2 : ∀ y, ξ y ≤ B := by
    intro y
    by_cases hy : y ∈ boxFinset x n
    · simp only [hξdef, if_pos hy]
      exact le_trans (le_max_left (η y) 0)
        (Finset.single_le_sum (f := fun z => max (η z) 0)
          (fun z _ => le_max_right (η z) 0) hy)
    · simp only [hξdef, if_neg hy]
      exact hB
  rw [h1]
  exact u_le_mul_of_le hd hB h2 n x

theorem integrable_abs_pow_of_exp_moment (ν : Measure ℝ) [IsProbabilityMeasure ν] {θ : ℝ}
    (hθ : 0 < θ) (hexp : Integrable (fun z : ℝ => Real.exp (θ * |z|)) ν) (r : ℕ) :
    Integrable (fun z : ℝ => |z| ^ r) ν := by
  have hbound : ∀ z : ℝ, |z| ^ r ≤ ((Nat.factorial r : ℝ) / θ ^ r) * Real.exp (θ * |z|) := by
    intro z
    have hx : (0:ℝ) ≤ θ * |z| := by positivity
    have hfac := Real.pow_div_factorial_le_exp (θ * |z|) hx r
    have hθr : (0:ℝ) < θ ^ r := by positivity
    have hf0 : (0:ℝ) < (Nat.factorial r : ℝ) := by positivity
    rw [mul_pow, div_le_iff₀ hf0] at hfac
    rw [div_mul_eq_mul_div, le_div_iff₀ hθr]
    nlinarith [hfac, pow_nonneg (abs_nonneg z) r, Real.exp_nonneg (θ * |z|)]
  refine Integrable.mono' (hexp.const_mul ((Nat.factorial r : ℝ) / θ ^ r))
    (measurable_abs.pow_const r).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) r)]
  exact hbound z

theorem integrable_maxPow_eval (ν : Measure ℝ) [IsProbabilityMeasure ν] (r : ℕ)
    (h : Integrable (fun t : ℝ => max t 0 ^ r) ν) (z : Site d) :
    Integrable (fun η : Site d → ℝ => max (η z) 0 ^ r) (LatticeProb.iidLaw d ν) := by
  have hev : (Measure.infinitePi fun _ : Site d => ν).map (fun ω : Site d → ℝ => ω z) = ν :=
    Measure.infinitePi_map_eval (fun _ : Site d => ν) z
  rw [LatticeProb.iidLaw]
  have := (integrable_map_measure
    (f := fun ω : Site d → ℝ => ω z) (g := fun t : ℝ => max t 0 ^ r)
    (by rw [hev]; exact h.aestronglyMeasurable)
    (measurable_pi_apply z).aemeasurable).mp (by rw [hev]; exact h)
  exact this

/-- **Every moment of the odometer is finite at a real one-site law with a finite
moment of the same order.**  The odometer at time `n` is at most `n` times the
positive part of the field summed over the box of radius `n`, and Jensen's
inequality for sums of powers turns the power of that sum into a sum of powers. -/
theorem integrable_u_pow_iid (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (r : ℕ) (hpow : Integrable (fun t : ℝ => max t 0 ^ r) ν)
    (n : ℕ) (x : Site d) :
    Integrable (fun η : Site d → ℝ => u η n x ^ r) (LatticeProb.iidLaw d ν) := by
  classical
  match r, hpow with
  | 0, _ =>
    haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) :=
      inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => ν))
    simp
  | (m + 1), hpow =>
    set s : Finset (Site d) := boxFinset x n with hs
    set c : ℝ := (n : ℝ) ^ (m + 1) * ((s.card : ℝ) ^ m) with hc
    have hc0 : 0 ≤ c := by positivity
    have hdom : Integrable
        (fun η : Site d → ℝ => c * ∑ z ∈ s, max (η z) 0 ^ (m + 1))
        (LatticeProb.iidLaw d ν) :=
      (integrable_finsetSum s fun z _ => integrable_maxPow_eval ν (m + 1) hpow z).const_mul c
    refine Integrable.mono' hdom
      ((measurable_u_eval n x).pow_const (m + 1)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun η => ?_)
    have hnn : ∀ z ∈ s, (0 : ℝ) ≤ max (η z) 0 := fun z _ => le_max_right (η z) 0
    have hjen := pow_sum_le_card_mul_sum_pow (s := s) (f := fun z => max (η z) 0) hnn m
    have hu : u η n x ≤ (n : ℝ) * ∑ z ∈ s, max (η z) 0 := u_le_mul_posBox hd η n x
    have hu0 : (0 : ℝ) ≤ u η n x := u_nonneg η n x
    have hsum0 : (0 : ℝ) ≤ ∑ z ∈ s, max (η z) 0 := Finset.sum_nonneg hnn
    have hpowle : u η n x ^ (m + 1) ≤ ((n : ℝ) * ∑ z ∈ s, max (η z) 0) ^ (m + 1) :=
      pow_le_pow_left₀ hu0 hu (m + 1)
    have hexp : ((n : ℝ) * ∑ z ∈ s, max (η z) 0) ^ (m + 1)
        = (n : ℝ) ^ (m + 1) * (∑ z ∈ s, max (η z) 0) ^ (m + 1) := mul_pow _ _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hu0 (m + 1))]
    calc u η n x ^ (m + 1)
        ≤ (n : ℝ) ^ (m + 1) * (∑ z ∈ s, max (η z) 0) ^ (m + 1) := by rw [← hexp]; exact hpowle
      _ ≤ (n : ℝ) ^ (m + 1) * ((s.card : ℝ) ^ m * ∑ z ∈ s, max (η z) 0 ^ (m + 1)) := by
          exact mul_le_mul_of_nonneg_left hjen (by positivity)
      _ = c * ∑ z ∈ s, max (η z) 0 ^ (m + 1) := by rw [hc]; ring

end Parking

end
