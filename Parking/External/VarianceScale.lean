import Parking.Support.NearestCriticalModel
import LatticeProb.Walk.SRWGreenSup

/-!
# Variance and correlation estimates

The variance and correlation estimates of sandpile.tex:1117-1240, cited
from Lawler-Limic, Propositions 2.4.1, 2.4.4, 2.4.6 and Theorem 4.3.1.
These are the explicit VarianceScale hypothesis of the sealed sibling
critical_toppling, used at parking.tex:1822-1848.

No longer assumed.  `Parking.CriticalScale.greenTime`, `varianceRate` and
`corrRate` are literal re-exports of the shared library's `LatticeProb.greenTime`,
`LatticeProb.varianceRate` and `LatticeProb.corrRate` (see
`Parking/Support/NearestCriticalModel.lean`), so every clause below reduces to
the library's own random-walk estimates
(`LatticeProb.exists_tsum_srwGreen_sq_bounds`, `LatticeProb.exists_tsum_srwGreen_mul_le`,
`LatticeProb.exists_tsum_srwWindow_sq_le`, `LatticeProb.exists_tsum_srwGreen_four_sq_le`)
once the two-point kernels are read through the library's own
`LatticeProb.greenTime_eq_srwGreen` (equivalently `LatticeProb.heatKernel_eq_srwHeat`
summed) as `srwGreen`/`srwWindow` at the *difference* of the two sites, and the
resulting sums over the lattice are reindexed by that difference (a
translation composed with a reflection).
-/

open MeasureTheory ProbabilityTheory LatticeProb

/-- The finite-time variance scale `eq:Qt-table`, the membrane correlation bound
`eq:corr-bound`, and the dimension-four window and tail bounds
`eq:d4-window-l2`, `eq:d4-window-linfty` and `eq:d4-full-window-bounds` of
`ssec:green-estimates`, all in their scenery-free Green-kernel form. -/
def Parking.External.VarianceScale : Prop :=
  (∀ d : ℕ, 1 ≤ d →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ t : ℕ, 2 ≤ t →
          c * Parking.CriticalScale.varianceRate d t ≤
              ∑' y : Parking.Site d, Parking.CriticalScale.greenTime d t 0 y ^ 2 ∧
            (∑' y : Parking.Site d, Parking.CriticalScale.greenTime d t 0 y ^ 2) ≤
              C * Parking.CriticalScale.varianceRate d t) ∧
  (∀ d : ℕ, 1 ≤ d → d ≤ 4 →
      ∃ C : ℝ, 0 < C ∧
        ∀ m n : ℕ, 1 ≤ m → m ≤ n →
          (∑' x : Parking.Site d,
              Parking.CriticalScale.greenTime d m 0 x * Parking.CriticalScale.greenTime d n 0 x) ≤
            C * Parking.CriticalScale.corrRate d m n *
              Real.sqrt (∑' x : Parking.Site d, Parking.CriticalScale.greenTime d m 0 x ^ 2) *
              Real.sqrt (∑' x : Parking.Site d, Parking.CriticalScale.greenTime d n 0 x ^ 2)) ∧
  (∃ C : ℝ, 0 < C ∧
      (∀ m n : ℕ, 1 ≤ m → m < n → ∀ x : Parking.Site 4,
          (∑' z : Parking.Site 4,
              Parking.CriticalScale.windowKernel m n x z ^ 2) ≤
            C * (1 + Real.log (((n : ℝ) + 2) / ((m : ℝ) + 2))) ∧
          ∀ z : Parking.Site 4,
            Parking.CriticalScale.windowKernel m n x z ≤ C / (m : ℝ)) ∧
      (∀ n : ℕ, 2 ≤ n → ∀ x : Parking.Site 4,
          (∑' z : Parking.Site 4, Parking.CriticalScale.greenTime 4 n x z ^ 2) ≤
            C * Real.log ((n : ℝ) + 2) ∧
          ∀ z : Parking.Site 4, Parking.CriticalScale.greenTime 4 n x z ≤ C))

/-- Reindexing a sum over the lattice by `z ↦ -z`. -/
private theorem tsum_neg_reflect {d : ℕ} (f : Parking.Site d → ℝ) :
    ∑' z : Parking.Site d, f (-z) = ∑' y : Parking.Site d, f y :=
  Equiv.tsum_eq (Equiv.neg (Parking.Site d)) f

/-- Reindexing a sum over the lattice by `z ↦ x - z`, a reflection through `x`. -/
private theorem tsum_reflect {d : ℕ} (x : Parking.Site d) (f : Parking.Site d → ℝ) :
    ∑' z : Parking.Site d, f (x - z) = ∑' y : Parking.Site d, f y := by
  have h1 : ∑' z : Parking.Site d, f (x - z) = ∑' z : Parking.Site d, f (-z + x) := by
    refine tsum_congr fun z => ?_
    congr 1
    abel
  rw [h1]
  have h2 := Equiv.tsum_eq (Equiv.neg (Parking.Site d)) (fun w => f (w + x))
  simp only [Equiv.neg_apply] at h2
  rw [h2]
  exact LatticeProb.tsum_shift x f

theorem green_sq_eq (d t : ℕ) :
    (∑' y : Parking.Site d, Parking.CriticalScale.greenTime d t 0 y ^ 2)
      = ∑' y : Parking.Site d, LatticeProb.srwGreen d t y ^ 2 := by
  have hfun : (fun y : Parking.Site d => Parking.CriticalScale.greenTime d t 0 y ^ 2)
      = fun y => LatticeProb.srwGreen d t (-y) ^ 2 := by
    funext y
    rw [show Parking.CriticalScale.greenTime d t 0 y = LatticeProb.greenTime d t 0 y from rfl,
      LatticeProb.greenTime_eq_srwGreen, zero_sub]
  rw [hfun]
  exact tsum_neg_reflect (fun y => LatticeProb.srwGreen d t y ^ 2)

-- FROZEN-STATEMENT-BEGIN
/-- The random-walk estimates of `ssec:green-estimates`, `eq:Qt-table`,
`eq:corr-bound` and the four dimension-four window displays, proved rather
than assumed. -/
theorem Parking.External.varianceScale : Parking.External.VarianceScale
-- FROZEN-STATEMENT-END
:= by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨c, C, hc, hC, h⟩ := LatticeProb.exists_tsum_srwGreen_sq_bounds (d := d) hd
    refine ⟨c, C, hc, hC, fun t ht => ?_⟩
    rw [green_sq_eq]
    exact h t ht
  · intro d hd hd4
    obtain ⟨C, hC, h⟩ := LatticeProb.exists_tsum_srwGreen_mul_le (d := d) hd hd4
    refine ⟨C, hC, fun m n hm hmn => ?_⟩
    have hfun : (fun x : Parking.Site d =>
          Parking.CriticalScale.greenTime d m 0 x * Parking.CriticalScale.greenTime d n 0 x)
        = fun x => LatticeProb.srwGreen d m (-x) * LatticeProb.srwGreen d n (-x) := by
      funext x
      rw [show Parking.CriticalScale.greenTime d m 0 x = LatticeProb.greenTime d m 0 x from rfl,
        show Parking.CriticalScale.greenTime d n 0 x = LatticeProb.greenTime d n 0 x from rfl,
        LatticeProb.greenTime_eq_srwGreen, LatticeProb.greenTime_eq_srwGreen, zero_sub]
    rw [hfun, tsum_neg_reflect (fun x => LatticeProb.srwGreen d m x * LatticeProb.srwGreen d n x),
      green_sq_eq, green_sq_eq]
    exact h m n hm hmn
  · obtain ⟨C₁, hC₁, hwin⟩ := LatticeProb.exists_tsum_srwWindow_sq_le
    obtain ⟨C₂, hC₂, hfull⟩ := LatticeProb.exists_tsum_srwGreen_four_sq_le
    refine ⟨max (max C₁ C₂) (max (2 * LatticeProb.diagConst 4) (1 + 2 * LatticeProb.diagConst 4)),
      lt_of_lt_of_le hC₁ (le_trans (le_max_left _ _) (le_max_left _ _)), ?_, ?_⟩
    · intro m n hm hmn x
      have hwkz : ∀ z : Parking.Site 4,
          Parking.CriticalScale.windowKernel m n x z = LatticeProb.srwWindow 4 m n (x - z) := by
        intro z
        show (∑ k ∈ Finset.Ico m n, Parking.CriticalScale.heatKernel 4 k x z)
          = LatticeProb.srwWindow 4 m n (x - z)
        rw [LatticeProb.srwWindow]
        exact Finset.sum_congr rfl fun k _ =>
          show LatticeProb.LocalCLT.heatKernel 4 k x z = LatticeProb.srwHeat 4 k (x - z) from
            LatticeProb.heatKernel_eq_srwHeat 4 k x z
      have hwk : (fun z : Parking.Site 4 => Parking.CriticalScale.windowKernel m n x z ^ 2)
          = fun z => LatticeProb.srwWindow 4 m n (x - z) ^ 2 := by
        funext z; rw [hwkz]
      constructor
      · rw [hwk, tsum_reflect x (fun y => LatticeProb.srwWindow 4 m n y ^ 2)]
        refine le_trans (hwin m n hm hmn.le) ?_
        have hlog : (0 : ℝ) ≤ Real.log (((n : ℝ) + 2) / ((m : ℝ) + 2)) := by
          refine Real.log_nonneg ((one_le_div (by positivity)).mpr ?_)
          have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn.le
          linarith
        refine mul_le_mul_of_nonneg_right ?_ (by linarith)
        exact le_trans (le_max_left _ _) (le_max_left _ _)
      · intro z
        rw [hwkz]
        refine le_trans (LatticeProb.srwWindow_le hm n _) ?_
        have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        refine div_le_div_of_nonneg_right ?_ hmpos.le
        exact le_trans (le_max_left _ _) (le_max_right _ _)
    · intro n hn x
      have hgz : (fun z : Parking.Site 4 => Parking.CriticalScale.greenTime 4 n x z ^ 2)
          = fun z => LatticeProb.srwGreen 4 n (x - z) ^ 2 := by
        funext z
        rw [show Parking.CriticalScale.greenTime 4 n x z = LatticeProb.greenTime 4 n x z from rfl,
          LatticeProb.greenTime_eq_srwGreen]
      constructor
      · rw [hgz, tsum_reflect x (fun y => LatticeProb.srwGreen 4 n y ^ 2)]
        refine le_trans (hfull n hn) ?_
        have hlog : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) := by
          refine Real.log_nonneg ?_
          have : (0 : ℝ) ≤ (n : ℝ) := by positivity
          linarith
        refine mul_le_mul_of_nonneg_right ?_ hlog
        exact le_trans (le_max_right _ _) (le_max_left _ _)
      · intro z
        rw [show Parking.CriticalScale.greenTime 4 n x z = LatticeProb.greenTime 4 n x z from rfl,
          LatticeProb.greenTime_eq_srwGreen]
        refine le_trans (LatticeProb.srwGreen_four_le n _) ?_
        exact le_trans (le_max_right _ _) (le_max_right _ _)
