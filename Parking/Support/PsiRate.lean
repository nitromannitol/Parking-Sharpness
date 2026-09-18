/-
The ingredients of Step 3 of `prop:near-divisible` (`parking.tex:2881-2896`) that
do not depend on the mean horizon lemma.

Step 3 reads: "Choose `B` so that `|ξ_δ(0)| ≤ B` almost surely for every
sufficiently small `δ`.  Since `ξ_δ(0)` has mean zero, it is dominated in convex
order by `Bχ`.  Applying the coordinatewise convex comparison to `u_m(0;·)^2`,
then using Theorem thm:BP and Lemma lem:u-concentration, gives
`(E u_m(0;ξ_δ)^2)^{1/2} ≤ C[log(m+2)]^{2/d}`.  Repeating Step 2 of
lem:mean-horizon with `q = 2` bounds the expected reward of a stopping time of
mean `M` by `C[log(M+2)]^{2/d}`."

Two things are proved here.  First, the convex comparison the step opens with:
a mean zero law supported in `[-B,B]` is below the two point law at `±B` in
convex order, because a convex function is below its chord on `[-B,B]` and the
chord has the same mean.  Second, the arithmetic of the rate
`ψ_d(s) = [log(s+2)]^{2/d}`: it is nonnegative and nondecreasing, it satisfies
`ψ_d(M+2) ≤ 3ψ_d(M)`, and the dyadic series `∑_j 2^{-4j/5} ψ_d(2^j N)` is at
most a constant times `ψ_d(N)`.  Those are exactly the three properties of the
scale that the block decomposition of `lem:mean-horizon` consumes, so they are
what a version of that lemma at this rate needs.
-/
import Parking.Support.NearHorizon

open MeasureTheory ProbabilityTheory LatticeProb
open scoped ENNReal NNReal

noncomputable section
namespace Parking

/-- The chord bound for a convex function on `[-B,B]`. -/
theorem convex_chord_le {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) {B x : ℝ} (hB : 0 < B)
    (hx : |x| ≤ B) :
    f x ≤ ((B + x) / (2 * B)) * f B + ((B - x) / (2 * B)) * f (-B) := by
  have hB2 : (0:ℝ) < 2 * B := by linarith
  have habs := abs_le.mp hx
  have hs : (0:ℝ) ≤ (B + x) / (2 * B) := by
    apply div_nonneg _ hB2.le
    linarith [habs.1]
  have ht : (0:ℝ) ≤ (B - x) / (2 * B) := by
    apply div_nonneg _ hB2.le
    linarith [habs.2]
  have hst : (B + x) / (2 * B) + (B - x) / (2 * B) = 1 := by field_simp; ring
  have hkey := hf.2 (Set.mem_univ B) (Set.mem_univ (-B)) hs ht hst
  simp only [smul_eq_mul] at hkey
  have hcomb : (B + x) / (2 * B) * B + (B - x) / (2 * B) * (-B) = x := by
    field_simp
    ring
  rwa [hcomb] at hkey

/-- **The bounded half of the convex comparison of Step 3** (`parking.tex:2881-2884`).
A mean zero law supported in `[-B,B]` is below the two point law at `±B` in convex order. -/
theorem convex_integral_le_twoPointLaw {μ : Measure ℝ} [IsProbabilityMeasure μ] {B : ℝ}
    (hB : 0 < B) (hsupp : ∀ᵐ z ∂μ, |z| ≤ B) (hid : Integrable (id : ℝ → ℝ) μ)
    (hmean : ∫ z, z ∂μ = 0) {f : ℝ → ℝ} {K : ℝ≥0} (hf : ConvexOn ℝ Set.univ f)
    (hfL : LipschitzWith K f) :
    ∫ z, f z ∂μ ≤ ∫ z, f z ∂(twoPointLaw B) := by
  have hfi : Integrable f μ := integrable_real_lipschitz hfL hid
  have hB2 : (0:ℝ) < 2 * B := by linarith
  have hg : ∀ z : ℝ, ((B + z) / (2 * B)) * f B + ((B - z) / (2 * B)) * f (-B)
      = ((f B + f (-B)) / 2) + z * ((f B - f (-B)) / (2 * B)) := by
    intro z
    field_simp
    ring
  have hbound : Integrable (fun z : ℝ =>
      ((f B + f (-B)) / 2) + z * ((f B - f (-B)) / (2 * B))) μ :=
    (integrable_const _).add (hid.mul_const _)
  have hmono : ∫ z, f z ∂μ
      ≤ ∫ z, (((f B + f (-B)) / 2) + z * ((f B - f (-B)) / (2 * B))) ∂μ := by
    refine integral_mono_ae hfi hbound ?_
    filter_upwards [hsupp] with z hz
    rw [← hg z]
    exact convex_chord_le hf hB hz
  have hval : ∫ z, (((f B + f (-B)) / 2) + z * ((f B - f (-B)) / (2 * B))) ∂μ
      = (f B + f (-B)) / 2 := by
    have hlin : Integrable (fun z : ℝ => z * ((f B - f (-B)) / (2 * B))) μ :=
      hid.mul_const _
    rw [integral_add (integrable_const _) hlin, integral_const, integral_mul_const, hmean]
    simp
  rw [integral_twoPointLaw B f]
  linarith [hmono, hval]

/-! ### The rate of Step 3 -/

/-- The rate of Step 3 of `prop:near-divisible`: `[log(s+2)]^{2/d}`. -/
def psi (d : ℕ) (s : ℝ) : ℝ := Real.log (s + 2) ^ ((2:ℝ) / d)

theorem log_two_le_log_add_two {s : ℝ} (hs : 0 ≤ s) : Real.log 2 ≤ Real.log (s + 2) :=
  Real.log_le_log (by norm_num) (by linarith)

theorem one_le_logAddTwo_real {s : ℝ} (hs : 1 ≤ s) : (1:ℝ) ≤ Real.log (s + 2) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  nlinarith [Real.exp_one_lt_d9]

theorem log_add_two_nonneg {s : ℝ} (hs : 0 ≤ s) : (0:ℝ) ≤ Real.log (s + 2) :=
  le_trans (Real.log_nonneg (by norm_num)) (log_two_le_log_add_two hs)

theorem psi_nonneg (d : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ psi d s :=
  Real.rpow_nonneg (log_add_two_nonneg hs) _

theorem psi_mono (d : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : psi d s ≤ psi d t :=
  Real.rpow_le_rpow (log_add_two_nonneg hs)
    (Real.log_le_log (by linarith) (by linarith)) (by positivity)

theorem two_rpow_le_two {d : ℕ} (hd2 : 2 ≤ d) : (2:ℝ) ^ ((2:ℝ) / d) ≤ 2 := by
  have hdR : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd2
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    (show (2:ℝ) / d ≤ 1 by rw [div_le_one (by linarith)]; linarith)
  rwa [Real.rpow_one] at h

theorem psi_add_two_le (d : ℕ) (hd2 : 2 ≤ d) {M : ℝ} (hM : 0 ≤ M) :
    psi d (M + 2) ≤ 3 * psi d M := by
  have hlog : Real.log (M + 2 + 2) ≤ 2 * Real.log (M + 2) := by
    have hsq : M + 2 + 2 ≤ (M + 2) ^ 2 := by nlinarith
    have h1 : Real.log (M + 2 + 2) ≤ Real.log ((M + 2) ^ 2) :=
      Real.log_le_log (by linarith) hsq
    rwa [Real.log_pow, Nat.cast_ofNat] at h1
  have hnn : (0:ℝ) ≤ Real.log (M + 2 + 2) := log_add_two_nonneg (by linarith)
  have hstep : psi d (M + 2) ≤ (2 * Real.log (M + 2)) ^ ((2:ℝ) / d) :=
    Real.rpow_le_rpow hnn hlog (by positivity)
  have hsplit : (2 * Real.log (M + 2)) ^ ((2:ℝ) / d)
      = (2:ℝ) ^ ((2:ℝ) / d) * psi d M :=
    Real.mul_rpow (by norm_num) (log_add_two_nonneg hM)
  have h2 := two_rpow_le_two hd2
  have hpsi0 : 0 ≤ psi d M := psi_nonneg d hM
  nlinarith [hstep, hsplit.le, hsplit.ge, h2, hpsi0]

theorem psi_two_pow_le (d : ℕ) (hd2 : 2 ≤ d) (j : ℕ) {N : ℝ} (hN : 1 ≤ N) :
    psi d (2 ^ j * N) ≤ ((j : ℝ) * Real.log 2 + 1) ^ ((2:ℝ) / d) * psi d N := by
  have hk : (1 : ℝ) ≤ (2:ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hL1 : (1:ℝ) ≤ Real.log (N + 2) := one_le_logAddTwo_real hN
  have hstep : (2:ℝ) ^ j * N + 2 ≤ (2:ℝ) ^ j * (N + 2) := by nlinarith [hk]
  have h1 : Real.log ((2:ℝ) ^ j * N + 2) ≤ Real.log ((2:ℝ) ^ j * (N + 2)) :=
    Real.log_le_log (by nlinarith [hk]) hstep
  have h2 : Real.log ((2:ℝ) ^ j * (N + 2)) = (j : ℝ) * Real.log 2 + Real.log (N + 2) := by
    rw [Real.log_mul (by positivity) (by linarith), Real.log_pow]
  have hj0 : (0:ℝ) ≤ (j : ℝ) * Real.log 2 := by
    have : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have h3 : Real.log ((2:ℝ) ^ j * N + 2) ≤ ((j : ℝ) * Real.log 2 + 1) * Real.log (N + 2) := by
    nlinarith [h1, h2, hL1, hj0]
  have hnn : (0:ℝ) ≤ Real.log ((2:ℝ) ^ j * N + 2) :=
    log_add_two_nonneg (by nlinarith [hk])
  have hrp : psi d ((2:ℝ) ^ j * N)
      ≤ (((j : ℝ) * Real.log 2 + 1) * Real.log (N + 2)) ^ ((2:ℝ) / d) :=
    Real.rpow_le_rpow hnn h3 (by positivity)
  rwa [Real.mul_rpow (by linarith) (log_add_two_nonneg (by linarith))] at hrp

theorem rpow_le_self_of_one_le {d : ℕ} (hd2 : 2 ≤ d) {x : ℝ} (hx : 1 ≤ x) :
    x ^ ((2:ℝ) / d) ≤ x := by
  have hdR : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd2
  have h := Real.rpow_le_rpow_of_exponent_le hx
    (show (2:ℝ) / d ≤ 1 by rw [div_le_one (by linarith)]; linarith)
  rwa [Real.rpow_one] at h

/-- **The block series at the rate of Step 3.**  The dyadic series
`∑_j 2^{-4j/5} ψ(2^j N)` is at most a constant times `ψ(N)`. -/
theorem exists_psi_block_sum (d : ℕ) (hd2 : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N →
      Summable (fun j : ℕ => (2:ℝ) ^ (-(j : ℝ) * ((4:ℝ)/5)) * psi d (2 ^ j * N)) ∧
      ∑' j : ℕ, (2:ℝ) ^ (-(j : ℝ) * ((4:ℝ)/5)) * psi d (2 ^ j * N) ≤ C * psi d N := by
  set r : ℝ := (2:ℝ) ^ (-((4:ℝ)/5)) with hrdef
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    rw [hrdef, show (1:ℝ) = (2:ℝ) ^ (0:ℝ) from (Real.rpow_zero 2).symm]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  have hrnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1
  have hpow : ∀ j : ℕ, (2:ℝ) ^ (-(j : ℝ) * ((4:ℝ)/5)) = r ^ j := by
    intro j
    rw [show -(j : ℝ) * ((4:ℝ)/5) = (j : ℝ) * (-((4:ℝ)/5)) by ring, two_rpow_mul]
  have hg1 : Summable (fun j : ℕ => ((j:ℝ)) * r ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (k := 1) (R := ℝ) hrnorm
  have hg2 : Summable (fun j : ℕ => r ^ j) := summable_geometric_of_lt_one hr0.le hr1
  have hgS : Summable (fun j : ℕ => r ^ j * ((j:ℝ) * Real.log 2 + 1)) := by
    refine Summable.congr ((hg1.mul_left (Real.log 2)).add hg2) fun j => ?_
    ring
  set S : ℝ := ∑' j : ℕ, r ^ j * ((j:ℝ) * Real.log 2 + 1) with hS
  refine ⟨max 1 S, lt_of_lt_of_le one_pos (le_max_left _ _), fun N hN => ?_⟩
  have hpsiN : 0 ≤ psi d N := psi_nonneg d (by linarith)
  have hmaj : ∀ j : ℕ, (2:ℝ) ^ (-(j : ℝ) * ((4:ℝ)/5)) * psi d (2 ^ j * N)
      ≤ r ^ j * ((j:ℝ) * Real.log 2 + 1) * psi d N := by
    intro j
    rw [hpow j]
    have hj1 : (1:ℝ) ≤ (j:ℝ) * Real.log 2 + 1 := by
      have : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      nlinarith [Nat.cast_nonneg (α := ℝ) j]
    have h1 := psi_two_pow_le d hd2 j hN
    have h2 : ((j:ℝ) * Real.log 2 + 1) ^ ((2:ℝ)/d) ≤ (j:ℝ) * Real.log 2 + 1 :=
      rpow_le_self_of_one_le hd2 hj1
    have h3 : ((j:ℝ) * Real.log 2 + 1) ^ ((2:ℝ)/d) * psi d N
        ≤ ((j:ℝ) * Real.log 2 + 1) * psi d N := mul_le_mul_of_nonneg_right h2 hpsiN
    have hrj : (0:ℝ) < r ^ j := pow_pos hr0 j
    nlinarith [h1, h3, hrj]
  have hnn : ∀ j : ℕ, (0:ℝ) ≤ (2:ℝ) ^ (-(j : ℝ) * ((4:ℝ)/5)) * psi d (2 ^ j * N) := by
    intro j
    have h2 : (0:ℝ) < (2:ℝ) ^ (-(j : ℝ) * ((4:ℝ)/5)) := Real.rpow_pos_of_pos (by norm_num) _
    have hk : (1:ℝ) ≤ (2:ℝ) ^ j := one_le_pow₀ (by norm_num)
    have h4 : (0:ℝ) ≤ psi d ((2:ℝ) ^ j * N) := psi_nonneg d (by nlinarith)
    positivity
  have hsumr : Summable (fun j : ℕ => r ^ j * ((j:ℝ) * Real.log 2 + 1) * psi d N) :=
    hgS.mul_right _
  have hsummable := hsumr.of_nonneg_of_le hnn hmaj
  refine ⟨hsummable, ?_⟩
  calc ∑' j : ℕ, (2:ℝ) ^ (-(j : ℝ) * ((4:ℝ)/5)) * psi d (2 ^ j * N)
      ≤ ∑' j : ℕ, r ^ j * ((j:ℝ) * Real.log 2 + 1) * psi d N :=
        hsummable.tsum_le_tsum hmaj hsumr
    _ = S * psi d N := tsum_mul_right
    _ ≤ max 1 S * psi d N := mul_le_mul_of_nonneg_right (le_max_right _ _) hpsiN
